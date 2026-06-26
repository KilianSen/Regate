"""Certify a proof by induction over ℕ with a real Lean kernel run.

eggregate grades the two obligations (base, step) soundly but can only *assert*
the induction schema (`base ∧ step ⟹ ∀n.P(n)`). This module is where leanregate
earns its keep: it translates the induction goal + its recursive definitions into
Lean, emits an `induction n` proof, and **kernel-checks it** — turning eggregate's
deferred `equal_no_certificate` into a certified verdict.

Honest by construction (same as `lean_prover`): if Lean accepts the proof the
claim is certified; if Lean rejects it, or the goal is outside the supported
fragment, or the toolchain is absent, we report not-certified and `grade.py`
returns `unknown` — never a false grade.

Supported fragment (a first slice): a goal that is a ℚ-valued equality over `+ - *`
/`pow`/`succ`/literals, with the induction variable (and any other exponents)
typed ℕ and all other variables ℚ, and `pow` defined by the two transmitted rules
`pow(a,0) → base` and `pow(a,S n) → step`. Anything else ⇒ not certified (`unknown`).

stdlib-only; shares no code with Eggregate — only the protocol.
"""
from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass

import lean_prover  # reuse the kernel seam: _run_lean, lean_available, caching style

FUN = "pw"           # the Lean name for the model's `pow` node
THEOREM = "regate_induction"


class InductionError(ValueError):
    """The induction goal/definitions are outside the supported Lean fragment."""


# ---------------------------------------------------------------------------
# Typing: which variables are ℕ (exponents / the induction var) vs ℚ.
# ---------------------------------------------------------------------------
def _infer(node: dict, dom: str, env: dict[str, str]) -> None:
    t = node.get("type")
    if t == "variable":
        name = str(node["value"])
        if env.get(name, dom) != dom:
            raise InductionError(f"variable {name!r} is used as both ℚ and ℕ")
        env[name] = dom
        return
    if t == "number":
        return
    s = node.get("slots") or {}
    if t == "succ":
        _infer(s["inner"][0], "N", env)
    elif t == "pow":
        _infer(s["base"][0], "Q", env)
        _infer(s["exponent"][0], "N", env)
    elif t == "frac":
        _infer(s["numerator"][0], "Q", env)
        _infer(s["denominator"][0], "Q", env)
    elif t in ("add", "sub", "mul"):
        _infer(s["left"][0], dom, env)
        _infer(s["right"][0], dom, env)
    elif t == "neg":
        _infer(s["inner"][0], dom, env)
    elif t == "eq":
        _infer(s["left"][0], "Q", env)
        _infer(s["right"][0], "Q", env)
    else:
        raise InductionError(f"cannot type node type {t!r}")


# ---------------------------------------------------------------------------
# MathNode -> Lean term, domain-aware (ℚ or ℕ).
# ---------------------------------------------------------------------------
_BIN = {"add": "+", "sub": "-", "mul": "*"}


def _term(node: dict, dom: str) -> str:
    t = node.get("type")
    if t in ("variable", "wild"):
        return str(node["value"])
    if t == "number":
        return f"({node['value']} : {'ℚ' if dom == 'Q' else 'ℕ'})"
    s = node["slots"]
    if t == "succ":
        return f"({_term(s['inner'][0], 'N')} + 1)"
    if t == "pow":
        return f"({FUN} {_term(s['base'][0], 'Q')} {_term(s['exponent'][0], 'N')})"
    if t in _BIN:
        return f"({_term(s['left'][0], dom)} {_BIN[t]} {_term(s['right'][0], dom)})"
    if t == "frac":
        return f"({_term(s['numerator'][0], 'Q')} / {_term(s['denominator'][0], 'Q')})"
    if t == "neg":
        return f"(-{_term(s['inner'][0], dom)})"
    raise InductionError(f"cannot translate node type {t!r}")


# ---------------------------------------------------------------------------
# The recursive `pow` definition, derived from the transmitted definitions.
# ---------------------------------------------------------------------------
def _wild_name(node: dict) -> str:
    if node.get("type") != "wild":
        raise InductionError("expected a wildcard in the definition pattern")
    return str(node["value"])


def _build_pow_def(definitions: list[dict]) -> str:
    """`def pw : ℚ → ℕ → ℚ` from the `pow(a,0)→…` and `pow(a,S n)→…` rules."""
    base_rule = succ_rule = None
    for d in definitions:
        lhs = d.get("lhs", {})
        if lhs.get("type") != "pow":
            continue
        exp = lhs["slots"]["exponent"][0]
        if exp.get("type") == "number" and str(exp.get("value")) == "0":
            base_rule = d
        elif exp.get("type") == "succ":
            succ_rule = d
    if base_rule is None or succ_rule is None:
        raise InductionError("pow needs a base rule (pow(a,0)→…) and a successor rule (pow(a,S n)→…)")

    b_var = _wild_name(base_rule["lhs"]["slots"]["base"][0])
    base_body = _term(base_rule["rhs"], "Q")

    s_var = _wild_name(succ_rule["lhs"]["slots"]["base"][0])
    rec_var = _wild_name(succ_rule["lhs"]["slots"]["exponent"][0]["slots"]["inner"][0])
    succ_body = _term(succ_rule["rhs"], "Q")
    return (
        f"def {FUN} : ℚ → ℕ → ℚ\n"
        f"  | {b_var}, 0 => {base_body}\n"
        f"  | {s_var}, ({rec_var} + 1) => {succ_body}\n"
    )


# ---------------------------------------------------------------------------
# The whole Lean file: definition + theorem + induction proof.
# ---------------------------------------------------------------------------
def build_source(ex: dict) -> str:
    goal = ex.get("goal")
    if not goal or goal.get("type") != "eq":
        raise InductionError("induction goal must be an equality")
    var = ex.get("inductionVar")
    if not var:
        raise InductionError("missing inductionVar")

    env: dict[str, str] = {}
    _infer(goal, "Q", env)
    if env.get(var) != "N":
        raise InductionError(f"induction variable {var!r} must be a ℕ (exponent) variable")

    q_vars = sorted(v for v, d in env.items() if d == "Q")
    n_vars = sorted(v for v, d in env.items() if d == "N")
    fresh = next(c for c in ("k", "m", "p", "q", "i", "j") if c not in env)
    ihn = "ih" if "ih" not in env else "ih0"

    pow_def = _build_pow_def(ex.get("definitions") or [])
    lhs = _term(goal["slots"]["left"][0], "Q")
    rhs = _term(goal["slots"]["right"][0], "Q")
    binders = ""
    if q_vars:
        binders += f" ({' '.join(q_vars)} : ℚ)"
    binders += f" ({' '.join(n_vars)} : ℕ)"
    intro = " ".join(q_vars + n_vars)
    return (
        "import Mathlib\n\n"
        f"{pow_def}\n"
        f"theorem {THEOREM} :∀{binders}, {lhs} = {rhs} := by\n"
        f"  intro {intro}\n"
        f"  induction {var} with\n"
        f"  | zero => first | simp_all [{FUN}] | (simp [{FUN}]; ring) | ring\n"
        f"  | succ {fresh} {ihn} => first | simp_all [{FUN}, {ihn}] "
        f"| (simp [{FUN}, {ihn}]; ring) | (simp only [{FUN}]; rw [{ihn}]; ring)\n"
    )


# ---------------------------------------------------------------------------
# Public API.
# ---------------------------------------------------------------------------
@dataclass
class CertifyResult:
    certified: bool
    method: str      # "induction" | "rejected" | "unavailable" | "untranslatable"
    detail: str = ""


_CACHE: dict[str, CertifyResult] = {}


def certify(ex: dict) -> CertifyResult:
    """Certify `∀ inductionVar. goal` with a Lean `induction` kernel run."""
    try:
        source = build_source(ex)
    except InductionError as e:
        return CertifyResult(False, "untranslatable", str(e))

    key = hashlib.sha256(source.encode()).hexdigest()
    if key in _CACHE:
        return _CACHE[key]
    if not lean_prover.lean_available():
        return CertifyResult(False, "unavailable", "lean toolchain unavailable")

    ok, detail = lean_prover._run_lean(source)
    result = CertifyResult(True, "induction") if ok else CertifyResult(False, "rejected", detail)
    _CACHE[key] = result
    return result
