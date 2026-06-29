"""Runtime Lean prover for Leanregate custom rulesets.

The scaffold rejected inline `exercise.ruleset`s outright: a formal backend may
only grade with rules it has a proof for, and the scaffold had no way to prove a
rule that arrived on the wire. This module lifts that restriction for *trusted*
authors (instructors, not students) by **establishing soundness at request time**
with a real Lean kernel running in the container.

Per rule, hybrid:

  1. *auto-prove* — translate the MathNode `lhs`/`rhs` (+ `conditions` as
     hypotheses) into a rational-identity goal over ℚ and discharge it with
     `field_simp [hyps]; ring`. The whole catalogue lives in this fragment, so a
     sound rule proves itself and an unsound one (a missing `≠ 0` guard, say) is
     *rejected* — Lean cannot prove a false identity.
  2. *proof-carrying* — if auto-prove fails and the rule ships a `proof` tactic
     block, elaborate and kernel-check that instead (covers rules outside the
     ring/field fragment, e.g. relational rewrites).

A rule Lean accepts becomes a `ProvenRule` for this request (see
`lean_check.proven_from_custom`); one it rejects, or one that needs a tactic
outside the fragment with no supplied proof, is left UNPROVEN — derivations using
it grade `unknown`, never a false grade. That asymmetry is the same honesty the
scaffold had, now extended to dynamically-supplied rules.

Lean runs in-process via `lake env lean` on a generated file inside a prebuilt
Mathlib project (`LEANREGATE_LEAN_PROJECT`). If the toolchain is absent the
prover reports `unavailable` and `grade.py` degrades to the built-in catalogue.

stdlib-only; shares no code with Eggregate — only the protocol.
"""
from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
from dataclasses import dataclass, field

# Where the prebuilt lake project (with Mathlib oleans) lives in the container.
# The Dockerfile populates it; unset/missing ⇒ Lean is unavailable.
LEAN_PROJECT = os.environ.get("LEANREGATE_LEAN_PROJECT", "/app/leanproj")
# Cold-loading the Mathlib tactic olean set on the first request takes ~85s in a
# fresh container (no persistent Lean server; page cache is empty). The default
# must clear that or every first request times out → `unknown`. Override with
# LEANREGATE_LEAN_TIMEOUT; warm requests are fast once the page cache is hot.
LEAN_TIMEOUT = float(os.environ.get("LEANREGATE_LEAN_TIMEOUT", "180"))


# ---------------------------------------------------------------------------
# MathNode -> Lean term translation.
# ---------------------------------------------------------------------------
_BIN_OP = {"add": "+", "sub": "-", "mul": "*"}


class TranslationError(ValueError):
    """The rule uses a construct we do not translate to a ℚ term."""


def _collect_wilds(node: dict, acc: set[str]) -> None:
    if node.get("type") == "wild":
        acc.add(str(node["value"]))
        return
    for children in (node.get("slots") or {}).values():
        for ch in children:
            _collect_wilds(ch, acc)


def wild_names(*nodes: dict) -> list[str]:
    """The free variables of a rule, alphabetical — declared as `(a b … : ℚ)`."""
    acc: set[str] = set()
    for n in nodes:
        _collect_wilds(n, acc)
    return sorted(acc)


def to_lean(node: dict) -> str:
    """A MathNode arithmetic expression as a parenthesised Lean ℚ term.

    Raises `TranslationError` for anything outside the rational-arithmetic
    fragment (e.g. a relational `eq` node, which is a Prop, not a term)."""
    t = node.get("type")
    if t == "wild":
        return str(node["value"])
    if t == "number":
        return f"({node['value']} : ℚ)"
    if t in _BIN_OP:
        slots = node["slots"]
        return f"({to_lean(slots['left'][0])} {_BIN_OP[t]} {to_lean(slots['right'][0])})"
    if t == "frac":
        slots = node["slots"]
        return f"({to_lean(slots['numerator'][0])} / {to_lean(slots['denominator'][0])})"
    if t == "neg":
        return f"(-{to_lean(node['slots']['inner'][0])})"
    raise TranslationError(f"cannot translate node type {t!r} to a ℚ term")


def to_lean_prop(node: dict) -> str:
    """A MathNode as a Lean Prop. An `eq` node is `a = b`; an arithmetic term `t`
    has no propositional reading on its own, so this is only meaningful for the
    relational (`eq`) rewrites that travel via a supplied proof."""
    if node.get("type") == "eq":
        slots = node["slots"]
        return f"({to_lean(slots['left'][0])} = {to_lean(slots['right'][0])})"
    raise TranslationError(f"node type {node.get('type')!r} is not a proposition")


# ---------------------------------------------------------------------------
# Conditions -> Lean hypotheses.
# ---------------------------------------------------------------------------
def _condition_to_hyp(cond: dict, idx: int) -> tuple[str, str]:
    """(binder, name) for a side condition, e.g. nonzero(c) -> ("(h0 : c ≠ 0)", "h0").

    Raises `TranslationError` for kinds with no ℚ hypothesis (integer/constant) —
    those rules fall back to the proof-carrying path."""
    kind = cond.get("kind")
    var = cond.get("var")
    name = f"h{idx}"
    if kind == "nonzero":
        return f"({name} : {var} ≠ 0)", name
    if kind == "positive":
        return f"({name} : 0 < {var})", name
    if kind == "notequal":
        arg = cond.get("arg")
        rhs = f"({arg} : ℚ)" if isinstance(arg, (int, float, str)) and str(arg).lstrip("-").isdigit() else str(arg)
        return f"({name} : {var} ≠ {rhs})", name
    raise TranslationError(f"side condition kind {kind!r} has no ℚ hypothesis")


# ---------------------------------------------------------------------------
# Goal construction.
# ---------------------------------------------------------------------------
THEOREM = "regate_rule"


def _goal(rule: dict) -> tuple[str, list[str]]:
    """Return (binders+goal, nonzero-hyp-names) for the rule's soundness theorem.

    For an arithmetic rewrite this is `∀ (vars) , hyps → lhs = rhs`; for a
    relational (`eq`) rewrite it is `… → (lhs ↔ rhs)`."""
    lhs, rhs = rule["lhs"], rule["rhs"]
    binders = " ".join(wild_names(lhs, rhs)) or "_x"
    hyp_binders: list[str] = []
    nonzero_names: list[str] = []
    for i, cond in enumerate(rule.get("conditions", [])):
        binder, name = _condition_to_hyp(cond, i)
        hyp_binders.append(binder)
        if cond.get("kind") == "nonzero":
            nonzero_names.append(name)
    if lhs.get("type") == "eq" or rhs.get("type") == "eq":
        body = f"{to_lean_prop(lhs)} ↔ {to_lean_prop(rhs)}"
    else:
        body = f"{to_lean(lhs)} = {to_lean(rhs)}"
    parts = [f"∀ ({binders} : ℚ)"]
    parts.extend(hyp_binders)
    sig = ", ".join(parts) + f", {body}"
    return sig, nonzero_names


def _auto_source(rule: dict) -> str:
    """A Lean file that states the rule and tries to discharge it automatically."""
    sig, nonzero = _goal(rule)
    simp_args = "[" + ", ".join(nonzero) + "]" if nonzero else ""
    return (
        "import Mathlib.Tactic.Ring\n"
        "import Mathlib.Tactic.FieldSimp\n\n"
        f"theorem {THEOREM} : {sig} := by\n"
        "  intros\n"
        f"  first\n"
        f"    | (field_simp {simp_args}; ring)\n"
        f"    | ring\n"
        f"    | field_simp {simp_args}\n"
    )


def _carried_source(rule: dict) -> str:
    """A Lean file that states the rule and discharges it with the supplied proof.

    Imports the tactic suite + ℚ defs rather than all of `import Mathlib`. This is
    the SAME surface as Basic.lean and the induction emitter, which lets the image
    ship only the transitive olean closure of `Mathlib.Tactic` (see the Dockerfile's
    prune step) instead of every Mathlib olean. A carried proof keeps the full
    tactic suite (ring/field_simp/linarith/nlinarith/positivity/norm_num/omega/…);
    the only thing it loses is citing a Mathlib *named theorem* by name, which the
    ℚ rational-rewrite rules this path certifies do not need."""
    sig, _ = _goal(rule)
    proof = rule["proof"].rstrip("\n")
    indented = "\n".join("  " + line for line in proof.splitlines())
    return (
        "import Mathlib.Tactic\n"
        "import Mathlib.Data.Rat.Defs\n\n"
        f"theorem {THEOREM} : {sig} := by\n"
        f"{indented}\n"
    )


# ---------------------------------------------------------------------------
# Lean invocation (the mock seam — the only thing that touches the toolchain).
# ---------------------------------------------------------------------------
# The Dockerfile bakes `lake env`'s LEAN_PATH/LD_LIBRARY_PATH into this file so the
# runtime can invoke `lean` directly. We MUST NOT call `lake` at runtime: `lake env`
# re-resolves dependencies and, if a package's git checkout looks off, deletes and
# re-clones it from GitHub — wiping the prebuilt oleans and needing network. Calling
# `lean` with the captured env sidesteps lake entirely (and is far faster: no
# workspace resolution). Absent the file (dev/source checkout) we fall back to lake.
LEAN_ENV_FILE = os.path.join(LEAN_PROJECT, ".lean_env")


def _baked_env() -> dict[str, str] | None:
    if not os.path.isfile(LEAN_ENV_FILE):
        return None
    env: dict[str, str] = {}
    with open(LEAN_ENV_FILE, encoding="utf-8") as fh:
        for line in fh:
            line = line.rstrip("\n")
            if "=" in line:
                k, v = line.split("=", 1)
                if v:
                    env[k] = v
    return env or None


def _lean_direct_ok() -> bool:
    return _baked_env() is not None and shutil.which("lean") is not None


def lean_available() -> bool:
    if not os.path.isdir(LEAN_PROJECT):
        return False
    return _lean_direct_ok() or shutil.which("lake") is not None


def _run_lean(body: str) -> tuple[bool, str]:
    """Elaborate `body` in the prebuilt Mathlib project. (True, "") on success;
    (False, diagnostics) on a Lean error, missing toolchain, or timeout.

    Prefers a direct `lean` call with the baked env (no lake); falls back to
    `lake env lean`. Isolated so tests can stub it without a Lean install."""
    if not lean_available():
        return False, "lean toolchain unavailable"
    src_dir = os.path.join(LEAN_PROJECT, "Regate")
    os.makedirs(src_dir, exist_ok=True)
    src = os.path.join(src_dir, "Check.lean")
    with open(src, "w", encoding="utf-8") as fh:
        fh.write(body)
    rel = os.path.relpath(src, LEAN_PROJECT)
    baked = _baked_env()
    if baked is not None and shutil.which("lean") is not None:
        cmd, env = ["lean", rel], {**os.environ, **baked}
    else:
        cmd, env = ["lake", "env", "lean", rel], None
    try:
        proc = subprocess.run(
            cmd, cwd=LEAN_PROJECT, capture_output=True, text=True,
            timeout=LEAN_TIMEOUT, env=env,
        )
    except subprocess.TimeoutExpired:
        return False, f"lean timed out after {LEAN_TIMEOUT}s"
    if proc.returncode == 0:
        return True, ""
    return False, (proc.stderr or proc.stdout or "lean error").strip()


# ---------------------------------------------------------------------------
# Public API.
# ---------------------------------------------------------------------------
@dataclass
class ProofResult:
    rule_id: str
    proven: bool
    method: str        # "ring" | "proof" | "rejected" | "unavailable" | "untranslatable"
    lemma: str         # the Lean theorem name when proven, else ""
    detail: str = ""   # Lean diagnostics when rejected


_CACHE: dict[str, ProofResult] = {}


def _cache_key(rule: dict) -> str:
    # Content-addressed: same rule body ⇒ same proof outcome. Drop cosmetic id so
    # two ids for the same identity share a result.
    canon = {k: rule.get(k) for k in ("lhs", "rhs", "conditions", "proof")}
    return hashlib.sha256(json.dumps(canon, sort_keys=True).encode()).hexdigest()


def prove_rule(rule: dict) -> ProofResult:
    """Establish soundness of one custom rule, hybrid + cached."""
    rid = str(rule.get("id", "?"))
    key = _cache_key(rule)
    cached = _CACHE.get(key)
    if cached is not None:
        return ProofResult(rid, cached.proven, cached.method, cached.lemma, cached.detail)

    if not lean_available():
        return _store(key, ProofResult(rid, False, "unavailable", "", "lean toolchain unavailable"))

    # 1) auto-prove, when the rule is in the arithmetic fragment.
    try:
        body = _auto_source(rule)
    except TranslationError as e:
        auto_detail = str(e)
    else:
        ok, detail = _run_lean(body)
        if ok:
            return _store(key, ProofResult(rid, True, "ring", THEOREM))
        auto_detail = detail

    # 2) proof-carrying fallback.
    if rule.get("proof"):
        ok, detail = _run_lean(_carried_source(rule))
        if ok:
            return _store(key, ProofResult(rid, True, "proof", THEOREM))
        return _store(key, ProofResult(rid, False, "rejected", "", detail))

    return _store(key, ProofResult(rid, False, "rejected", "", auto_detail))


def _store(key: str, result: ProofResult) -> ProofResult:
    _CACHE[key] = result
    return result


def prove_ruleset(ruleset: list[dict]) -> dict[str, ProofResult]:
    """Prove every rule in an inline ruleset; keyed by rule id."""
    return {str(r.get("id", f"rule{i}")): prove_rule(r) for i, r in enumerate(ruleset)}
