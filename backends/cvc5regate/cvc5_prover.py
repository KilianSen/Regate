from __future__ import annotations

import hashlib
import os
import re
import shutil
import subprocess
import tempfile
from dataclasses import dataclass

# The cvc5 binary. Override with CVC5REGATE_CVC5; else found on PATH.
CVC5 = os.environ.get("CVC5REGATE_CVC5") or shutil.which("cvc5") or "cvc5"
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


def try_alethe_proof(prove_source: str) -> str | None:
    """Ask cvc5 for an Alethe proof of `prove_source` (which must be `unsat`).
    Returns the proof text, or None if cvc5 cannot export Alethe for it (e.g. an
    induction proof carrying skolems — unsupported by the cvc5 1.3.x exporter)."""
    result, detail = _run_cvc5(
        prove_source,
        ["--quant-ind", "--produce-proofs", "--proof-format-mode=alethe",
         "--proof-alethe-define-skolems", "--dump-proofs"],
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


# cvc5 reports a numeric model value as e.g. `(((val n) 2))` or `((x (- 3)))`.
_VALUE_RE = re.compile(r"\(\s*(\([^()]*\)|[^()\s]+)\s+(\(-\s*\d+\)|-?\d+(?:\.\d+)?|[^()\s]+)\s*\)")


def _parse_values(detail: str) -> dict:
    """Pull `(get-value …)` pairs out of cvc5 output into {label: value}."""
    out: dict[str, str] = {}
    for m in _VALUE_RE.finditer(detail):
        label, value = m.group(1).strip(), m.group(2).strip()
        value = re.sub(r"\(-\s*(\d+)\)", r"-\1", value)   # (- 3) -> -3
        out[label] = value
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
        # Map cvc5's `(val n)` style labels back to the bare variable names.
        witness: dict[str, str] = {}
        for lbl in value_labels:
            for k, v in values.items():
                if lbl in k:
                    witness[lbl] = v
        res.witness = witness or values or None
    _CACHE[key] = res
    return res
