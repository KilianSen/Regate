from __future__ import annotations

import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from fractions import Fraction


def _find_cvc5() -> str:
    """Locate the cvc5 binary: CVC5REGATE_CVC5, then PATH, then this
    interpreter's own environment.

    The `cvc5` wheel installs a real binary into <prefix>/bin, which is on PATH
    only while the virtualenv is activated. Without this fallback, running under
    an unactivated venv (a service, a bare `.venv/bin/python`) leaves cvc5
    unfindable and every goal degrades silently to `unknown`.
    """
    explicit = os.environ.get("CVC5REGATE_CVC5")
    if explicit:
        return explicit
    found = shutil.which("cvc5")
    if found:
        return found
    for base in (sys.prefix, sys.base_prefix):
        for sub in ("bin", "Scripts"):
            for name in ("cvc5", "cvc5.exe"):
                cand = os.path.join(base, sub, name)
                if os.path.isfile(cand) and os.access(cand, os.X_OK):
                    return cand
    return "cvc5"


# The cvc5 binary. Override with CVC5REGATE_CVC5; else PATH, else this venv.
CVC5 = _find_cvc5()
# The Carcara Alethe-proof checker (optional). Override with CVC5REGATE_CARCARA.
CARCARA = os.environ.get("CVC5REGATE_CARCARA") or shutil.which("carcara") or ""
# Per-call wall-clock budget (seconds). cvc5's induction search is unbounded, so a
# goal outside what it can prove must time out into `unknown`, never hang grading.
TIMEOUT = float(os.environ.get("CVC5REGATE_TIMEOUT", "20"))
# A short budget for the cheap disprove pass (counterexample search runs first).
DISPROVE_TIMEOUT = float(os.environ.get("CVC5REGATE_DISPROVE_TIMEOUT", "5"))


def cvc5_available() -> bool:
    """Is a runnable cvc5 binary present?"""
    path = shutil.which(CVC5) or (CVC5 if os.path.isfile(CVC5) else None)
    if path is None:
        return False
    try:
        proc = subprocess.run([path, "--version"], capture_output=True,
                              text=True, timeout=10)
    except (OSError, subprocess.SubprocessError):
        return False
    return proc.returncode == 0 and "cvc5" in (proc.stdout + proc.stderr).lower()


def carcara_available() -> bool:
    """Is the optional Carcara Alethe-proof checker present?"""
    if not CARCARA:
        return False
    return shutil.which(CARCARA) is not None or os.path.isfile(CARCARA)


# ---------------------------------------------------------------------------
# The solver invocation (the mock seam — the only thing that runs cvc5).
# ---------------------------------------------------------------------------
_RESULTS = ("unsat", "sat", "unknown")


def _parse_result(stdout: str) -> str:
    """The check-sat verdict is the first bare `sat`/`unsat`/`unknown` line."""
    for line in stdout.splitlines():
        tok = line.strip()
        if tok in _RESULTS:
            return tok
    return "error"


def _run_cvc5(smt2_source: str, extra_args: list[str] | None = None,
              timeout: float | None = None) -> tuple[str, str]:
    """Run cvc5 on `smt2_source`. Returns (result, detail) where result is one of
    `unsat` / `sat` / `unknown` / `error`, and detail is the raw stdout+stderr.

    Isolated so tests can stub it without a cvc5 install."""
    if not cvc5_available():
        return "error", "cvc5 toolchain unavailable"
    args = [CVC5, "--lang=smt2"] + (extra_args or [])
    tmp = tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False, encoding="utf-8")
    try:
        tmp.write(smt2_source)
        tmp.close()
        try:
            proc = subprocess.run(args + [tmp.name], capture_output=True, text=True,
                                  timeout=timeout if timeout is not None else TIMEOUT)
        except subprocess.TimeoutExpired:
            return "unknown", f"cvc5 timed out after {timeout or TIMEOUT}s"
    finally:
        os.unlink(tmp.name)
    out = (proc.stdout or "") + (proc.stderr or "")
    return _parse_result(proc.stdout or ""), out.strip()


# ---------------------------------------------------------------------------
# Carcara re-check of an emitted Alethe proof (best-effort).
# ---------------------------------------------------------------------------
def recheck_alethe(smt2_source: str, alethe_proof: str) -> bool:
    """Independently re-verify an Alethe proof with Carcara. False if Carcara is
    absent or rejects the proof (we then fall back to the solver's own verdict)."""
    if not carcara_available() or not alethe_proof.strip():
        return False
    with tempfile.TemporaryDirectory() as d:
        prob = os.path.join(d, "problem.smt2")
        prf = os.path.join(d, "proof.alethe")
        with open(prob, "w", encoding="utf-8") as fh:
            fh.write(smt2_source)
        with open(prf, "w", encoding="utf-8") as fh:
            fh.write(alethe_proof)
        try:
            proc = subprocess.run([CARCARA, "check", prf, prob],
                                  capture_output=True, text=True, timeout=TIMEOUT)
        except (OSError, subprocess.SubprocessError):
            return False
        return proc.returncode == 0 and "valid" in (proc.stdout + proc.stderr).lower()


_ALETHE_UNSUPPORTED = re.compile(r"unsupported by alethe|untranslated|\berror\b", re.I)


_ALETHE_ARGS = ["--produce-proofs", "--proof-format-mode=alethe",
                "--proof-alethe-define-skolems", "--dump-proofs"]


def try_alethe_proof(prove_source: str, solve_args: list[str] | None = None) -> str | None:
    """Ask cvc5 for an Alethe proof of `prove_source` (which must be `unsat`).
    Returns the proof text, or None if cvc5 cannot export Alethe for it (e.g. an
    induction proof carrying skolems — unsupported by the cvc5 1.3.x exporter).

    `solve_args` are the solving flags the proof is for: `["--quant-ind"]` for an
    induction goal, `[]` for a plain (non-inductive) equivalence query — the latter
    is where cvc5 *can* usually export a checkable Alethe certificate."""
    result, detail = _run_cvc5(
        prove_source,
        (solve_args or ["--quant-ind"]) + _ALETHE_ARGS,
    )
    if result != "unsat":
        return None
    # The proof is the parenthesised block after the `unsat` line. If cvc5 hit an
    # export limitation it emits an `(error "Proof unsupported by Alethe: …")`.
    body = detail.split("unsat", 1)[-1]
    if _ALETHE_UNSUPPORTED.search(body):
        return None
    start = body.find("(")
    return body[start:].strip() if start != -1 else None


# ---------------------------------------------------------------------------
# Public solver API: prove / disprove with content-hash caching.
# ---------------------------------------------------------------------------
@dataclass
class SolveResult:
    verdict: str        # "unsat" (proved) | "sat" (refuted) | "unknown" | "error"
    detail: str = ""
    witness: dict | None = None     # {var: value} for a `sat` (proven_unequal)
    alethe: str | None = None       # emitted Alethe proof text, if any
    rechecked: bool = False         # Carcara independently re-verified `alethe`


_CACHE: dict[str, SolveResult] = {}


def _key(*parts: str) -> str:
    return hashlib.sha256("\0".join(parts).encode()).hexdigest()


def prove_rule(rule_source: str) -> SolveResult:
    """Prove a transmitted rule's universally-quantified equality (negated goal →
    expect `unsat`). Plain solving: a rule is an unconditional algebraic identity,
    not an inductive claim, so neither `--quant-ind` nor the model finder applies.
    A rule cvc5 cannot settle is simply unproven — inconclusive, never false."""
    key = _key("rule", rule_source)
    if key in _CACHE:
        return _CACHE[key]
    verdict, detail = _run_cvc5(rule_source, [], timeout=DISPROVE_TIMEOUT)
    res = SolveResult(verdict, detail)
    _CACHE[key] = res
    return res


def prove(prove_source: str, want_certificate: bool = True) -> SolveResult:
    """Prove `∀n.P(n)` via `--quant-ind` (negated goal → expect `unsat`).

    On `unsat`, optionally try to emit + Carcara-recheck an Alethe certificate."""
    key = _key("prove", prove_source, str(want_certificate))
    if key in _CACHE:
        return _CACHE[key]
    verdict, detail = _run_cvc5(prove_source, ["--quant-ind"])
    res = SolveResult(verdict, detail)
    if verdict == "unsat" and want_certificate:
        proof = try_alethe_proof(prove_source)
        if proof is not None:
            res.alethe = proof
            res.rechecked = recheck_alethe(prove_source, proof)
    _CACHE[key] = res
    return res


def prove_equiv(prove_source: str, want_certificate: bool = True) -> SolveResult:
    """Prove a non-inductive equivalence `∀x⃗. L = R` (negated goal → expect `unsat`).

    Plain solving — no `--quant-ind`: two expressions are equal by an unconditional
    algebraic identity, not by induction. Unlike the induction path, cvc5 can often
    export a checkable Alethe proof here, so a `proven_equal` may carry a Carcara-
    re-checked certificate rather than a bare re-runnable problem."""
    key = _key("equiv", prove_source, str(want_certificate))
    if key in _CACHE:
        return _CACHE[key]
    verdict, detail = _run_cvc5(prove_source, [])
    res = SolveResult(verdict, detail)
    if verdict == "unsat" and want_certificate:
        proof = try_alethe_proof(prove_source, solve_args=[])
        if proof is not None:
            res.alethe = proof
            res.rechecked = recheck_alethe(prove_source, proof)
    _CACHE[key] = res
    return res


# cvc5 reports model values as `(((val n) 2))`, `((x (- 3)))`, `((x (/ 1 2)))`, or —
# for a datatype-sorted constant — a constructor term like `((n (succ zero)))`. The
# previous regex could only read atoms, so a rational silently dropped the variable
# from the witness and a constructor term was unreadable. Parse s-expressions instead.
def _sexprs(text: str) -> list:
    """Read `text` into nested lists of atoms. Unbalanced input yields what parsed."""
    tokens = text.replace("(", " ( ").replace(")", " ) ").split()
    stack: list[list] = [[]]
    for tok in tokens:
        if tok == "(":
            stack.append([])
        elif tok == ")":
            if len(stack) == 1:
                continue
            done = stack.pop()
            stack[-1].append(done)
        else:
            stack[-1].append(tok)
    return stack[0]


def _render(node) -> str:
    return node if isinstance(node, str) else "(" + " ".join(_render(n) for n in node) + ")"


def _as_number(node) -> str | None:
    """A model value as an exact numeric string, or None if it is not numeric.

    Handles `(- 3)`, `(/ 1 2)`, `(- (/ 1 2))`, and ℕ constructor terms (`zero`,
    `(succ (succ zero))` -> `2`). A non-numeric constructor term such as
    `(cons 5 nil)` returns None, so D4 still degrades it to `unknown`."""
    if isinstance(node, str):
        if node == "zero":
            return "0"
        try:
            Fraction(node)
            return node
        except (ValueError, ZeroDivisionError):
            return None
    if len(node) == 2 and node[0] == "-":
        inner = _as_number(node[1])
        return None if inner is None else str(-Fraction(inner))
    if len(node) == 2 and node[0] == "succ":
        inner = _as_number(node[1])
        if inner is None:
            return None
        v = Fraction(inner)
        return None if v.denominator != 1 or v < 0 else str(v + 1)
    if len(node) == 3 and node[0] == "/":
        a, b = _as_number(node[1]), _as_number(node[2])
        if a is None or b is None or Fraction(b) == 0:
            return None
        return str(Fraction(a) / Fraction(b))
    return None


def _parse_values(detail: str) -> dict:
    """Pull `(get-value …)` pairs out of cvc5 output into {label: value}.

    Values that are not numeric are kept in raw s-expression form so the caller can
    see what came back; `_usable_witness` rejects them (they are not reportable as a
    numeric counterexample), which is the D4 fail-safe."""
    out: dict[str, str] = {}
    for top in _sexprs(detail):
        if not isinstance(top, list):
            continue
        for pair in top:
            if isinstance(pair, list) and len(pair) == 2:
                num = _as_number(pair[1])
                out[_render(pair[0])] = num if num is not None else _render(pair[1])
    return out


def disprove(disprove_source: str, value_labels: list[str]) -> SolveResult:
    """Search for a counterexample to `∀n.P(n)` with the induction variable a free
    constant and cvc5's recursive-function model finder (`--fmf-fun`). On `sat`,
    extract the requested `get-value` labels as the numeric witness."""
    key = _key("disprove", disprove_source)
    if key in _CACHE:
        return _CACHE[key]
    verdict, detail = _run_cvc5(disprove_source, ["--fmf-fun", "--produce-models"],
                                timeout=DISPROVE_TIMEOUT)
    res = SolveResult(verdict, detail)
    if verdict == "sat":
        values = _parse_values(detail)
        # Map cvc5's get-value keys back to the requested labels. A ℕ variable is read
        # as `(val n)`; everything else is its bare name. Match EXACTLY on those two
        # forms — a substring test let a one-char accumulator (`a`, `l`, `v`) collide
        # with the `(val n)` key and clobber its own value.
        witness: dict[str, str] = {}
        for lbl in value_labels:
            # Prefer the bare name — the datatype constant read straight out of the
            # model. `(val n)` is only still honoured so an older query shape (or a
            # stubbed solver emitting one) keeps working.
            if lbl in values:
                witness[lbl] = values[lbl]
            elif f"(val {lbl})" in values:
                witness[lbl] = values[f"(val {lbl})"]
        res.witness = witness or values or None
    _CACHE[key] = res
    return res
