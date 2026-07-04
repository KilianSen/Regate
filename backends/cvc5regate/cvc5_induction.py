from __future__ import annotations

import hashlib
import os
from dataclasses import dataclass

import cvc5_prover
import step_check  # strict symbolic rule-instance checking of the student's steps

THEOREM_VAR = "n"   # cosmetic; the actual induction var name comes from the request


class InductionError(ValueError):
    """The induction goal/definitions are outside the supported SMT fragment."""


# Relational goal node types and their SMT operators.
_REL = {"eq": "=", "le": "<=", "lt": "<", "ge": ">=", "gt": ">"}
_BIN = {"add": "+", "sub": "-", "mul": "*"}


# ---------------------------------------------------------------------------
# Typing: which variables are ℕ (the induction var / exponents) vs numeric.
# Mirrors lean_induction._infer.
# ---------------------------------------------------------------------------
def _infer(node: dict, dom: str, env: dict[str, str], indvar: str = "") -> None:
    t = node.get("type")
    if t == "variable":
        name = str(node["value"])
        # The induction variable is ALWAYS the ℕ datatype (cvc5 inducts on it
        # structurally); wherever it appears in a numeric position it is coerced
        # via `val`. So it is exempt from the numeric/ℕ consistency check.
        if name == indvar:
            env[name] = "N"
            return
        if env.get(name, dom) != dom:
            raise InductionError(f"variable {name!r} is used as both numeric and ℕ")
        env[name] = dom
        return
    if t == "number":
        return
    s = node.get("slots") or {}
    if t == "succ":
        _infer(s["inner"][0], "N", env, indvar)
    elif t == "pow":
        _infer(s["base"][0], "Q", env, indvar)
        _infer(s["exponent"][0], "N", env, indvar)
    elif t == "frac":
        _infer(s["numerator"][0], "Q", env, indvar)
        _infer(s["denominator"][0], "Q", env, indvar)
    elif t in _BIN:
        # `add` may be ℕ (an exponent sum) or numeric; inherit the context domain.
        _infer(s["left"][0], dom, env, indvar)
        _infer(s["right"][0], dom, env, indvar)
    elif t == "neg":
        _infer(s["inner"][0], dom, env, indvar)
    elif t == "apply":
        # A transmitted recursive function f(args…, k): the LAST argument is the
        # ℕ recursion variable, the rest are numeric.
        args = s["args"]
        for a in args[:-1]:
            _infer(a, "Q", env, indvar)
        _infer(args[-1], "N", env, indvar)
    elif t in _REL:
        _infer(s["left"][0], "Q", env, indvar)
        _infer(s["right"][0], "Q", env, indvar)
    elif t == "divides":
        _infer(s["value"][0], "Q", env, indvar)
    else:
        raise InductionError(f"cannot type node type {t!r}")


# ---------------------------------------------------------------------------
# MathNode -> SMT term.  Numeric sort S is "Real" (ℚ) or "Int".
# ---------------------------------------------------------------------------
class _Ctx:
    """Mutable translation state: which built-ins/funcs the emitted file needs."""
    def __init__(self, sort: str, env: dict[str, str]):
        self.sort = sort
        self.env = env
        self.need_val = False     # val : Nat -> Int
        self.need_nplus = False   # nplus : Nat -> Nat -> Nat


def _num_lit(value, sort: str) -> str:
    s = str(value).strip()
    neg = s.startswith("-")
    body = s[1:] if neg else s
    if sort == "Real" and "." not in body and "/" not in body:
        body = body + ".0"
    return f"(- {body})" if neg else body


def _nat_lit(k: int) -> str:
    out = "zero"
    for _ in range(k):
        out = f"(succ {out})"
    return out


def _coerce(nat_term: str, sort: str, ctx: _Ctx) -> str:
    """Place a Nat term where a numeric (Real/Int) value is required."""
    ctx.need_val = True
    return f"(val {nat_term})" if sort == "Int" else f"(to_real (val {nat_term}))"


def _nat_term(node: dict, ctx: _Ctx) -> str:
    """A ℕ-sorted (Nat datatype) term — exponent / succ-argument position."""
    t = node.get("type")
    if t in ("variable", "wild"):
        return str(node["value"])
    if t == "number":
        k = int(str(node["value"]))
        if k < 0:
            raise InductionError("negative ℕ literal")
        return _nat_lit(k)
    s = node.get("slots") or {}
    if t == "succ":
        return f"(succ {_nat_term(s['inner'][0], ctx)})"
    if t == "add":
        ctx.need_nplus = True
        return f"(nplus {_nat_term(s['left'][0], ctx)} {_nat_term(s['right'][0], ctx)})"
    raise InductionError(f"cannot translate node type {t!r} to ℕ")


def _term(node: dict, ctx: _Ctx) -> str:
    """A numeric (Real/Int) SMT term."""
    t = node.get("type")
    if t in ("variable", "wild"):
        name = str(node["value"])
        if ctx.env.get(name) == "N":
            return _coerce(name, ctx.sort, ctx)
        return name
    if t == "number":
        return _num_lit(node["value"], ctx.sort)
    s = node["slots"]
    if t in _BIN:
        return f"({_BIN[t]} {_term(s['left'][0], ctx)} {_term(s['right'][0], ctx)})"
    if t == "neg":
        return f"(- {_term(s['inner'][0], ctx)})"
    if t == "frac":
        if ctx.sort != "Real":
            raise InductionError("fractions require the rational (Real) domain")
        return f"(/ {_term(s['numerator'][0], ctx)} {_term(s['denominator'][0], ctx)})"
    if t == "pow":
        base = _term(s["base"][0], ctx)
        exp = _nat_term(s["exponent"][0], ctx)
        return f"(pow {base} {exp})"
    if t == "apply":
        fname = str(node["value"])
        args = s["args"]
        parts = [_term(a, ctx) for a in args[:-1]] + [_nat_term(args[-1], ctx)]
        return f"({fname} {' '.join(parts)})"
    if t == "succ":
        # A ℕ value appearing where a number is wanted, e.g. the `(k+1)` summand
        # in a sum's recursive step — coerce it.
        return _coerce(_nat_term(node, ctx), ctx.sort, ctx)
    raise InductionError(f"cannot translate node type {t!r} to a numeric term")


def _goal_term(goal: dict, ctx: _Ctx) -> str:
    """The goal relation as an SMT Bool."""
    t = goal.get("type")
    s = goal.get("slots") or {}
    if t in _REL:
        return f"({_REL[t]} {_term(s['left'][0], ctx)} {_term(s['right'][0], ctx)})"
    if t == "divides":
        if ctx.sort != "Int":
            raise InductionError("divisibility requires the integer domain")
        d = s["divisor"][0]
        if d.get("type") != "number":
            raise InductionError("divisor must be a numeric literal")
        return f"(= (mod {_term(s['value'][0], ctx)} {int(str(d['value']))}) 0)"
    raise InductionError(f"goal must be a relation (=,<=,<,>=,>,divides), got {t!r}")


# ---------------------------------------------------------------------------
# Recursive function definitions, derived from the transmitted `definitions`.
# ---------------------------------------------------------------------------
def _wild(node: dict) -> str:
    if node.get("type") not in ("wild", "variable"):
        raise InductionError("expected a pattern variable in the definition")
    return str(node["value"])


def _build_pow(definitions: list[dict], ctx: _Ctx) -> str:
    """`define-fun-rec pow ((a S) (n Nat)) S` from the pow(a,0)/pow(a,S n) rules."""
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
        raise InductionError("pow needs a base rule pow(a,0)→… and a successor rule pow(a,S n)→…")
    # Parameter names come from the successor rule: base `a`, recursion var `k`.
    # The exponent parameter is matched on, so name it `e` (cannot clash with `k`).
    a = _wild(succ_rule["lhs"]["slots"]["base"][0])
    k = _wild(succ_rule["lhs"]["slots"]["exponent"][0]["slots"]["inner"][0])
    base_body = _term(base_rule["rhs"], ctx)      # constant (e.g. 1) for pow
    succ_body = _term(succ_rule["rhs"], ctx)      # references `a` and `(pow a k)`
    return (
        f"(define-fun-rec pow (({a} {ctx.sort}) (e Nat)) {ctx.sort}\n"
        f"  (match e ((zero {base_body}) ((succ {k}) {succ_body}))))\n"
    )


def _build_apply_defs(definitions: list[dict], ctx: _Ctx) -> str:
    """`define-fun-rec` for each generic recursive function supplied as `apply`
    definitions: f(args…,0)→base and f(args…,S k)→step."""
    by_name: dict[str, dict] = {}
    for d in definitions:
        lhs = d.get("lhs", {})
        if lhs.get("type") != "apply":
            continue
        by_name.setdefault(str(lhs["value"]), {})
        last = lhs["slots"]["args"][-1]
        if last.get("type") == "number" and str(last.get("value")) == "0":
            by_name[str(lhs["value"])]["base"] = d
        elif last.get("type") == "succ":
            by_name[str(lhs["value"])]["succ"] = d
    out = []
    for fname, rules in by_name.items():
        if "base" not in rules or "succ" not in rules:
            raise InductionError(f"recursive function {fname!r} needs a 0-rule and a succ-rule")
        b_args = rules["base"]["lhs"]["slots"]["args"]
        s_args = rules["succ"]["lhs"]["slots"]["args"]
        params = [f"({_wild(a)} {ctx.sort})" for a in s_args[:-1]]
        k = _wild(s_args[-1]["slots"]["inner"][0])
        base_body = _term(rules["base"]["rhs"], ctx)
        succ_body = _term(rules["succ"]["rhs"], ctx)
        out.append(
            f"(define-fun-rec {fname} ({' '.join(params)} ({k} Nat)) {ctx.sort}\n"
            f"  (match {k} ((zero {base_body}) ((succ {k}) {succ_body}))))\n"
        )
    return "".join(out)


# ---------------------------------------------------------------------------
# The whole SMT-LIB file: preamble + recursive defs + (negated) goal.
# ---------------------------------------------------------------------------
def _numsort(ex: dict, goal: dict) -> str:
    dom = ex.get("domain")
    if dom == "int":
        return "Int"
    if dom == "rat":
        return "Real"
    return "Int" if goal.get("type") == "divides" else "Real"


def _preamble(ctx: _Ctx, defs_block: str) -> str:
    lines = ["(set-logic ALL)",
             "(declare-datatype Nat ((zero) (succ (pred Nat))))"]
    if ctx.need_val:
        lines.append("(define-fun-rec val ((n Nat)) Int "
                     "(match n ((zero 0) ((succ k) (+ 1 (val k))))))")
    if ctx.need_nplus:
        lines.append("(define-fun-rec nplus ((m Nat) (n Nat)) Nat "
                     "(match m ((zero n) ((succ k) (succ (nplus k n))))))")
    return "\n".join(lines) + "\n" + defs_block


def _translate(ex: dict) -> tuple[str, str, str, list[str]]:
    """Return (preamble+defs, goal_bool, induction_var, numeric_var_names)."""
    goal = ex.get("goal")
    if not goal or goal.get("type") not in (set(_REL) | {"divides"}):
        raise InductionError("induction goal must be a relation (=,<=,<,>=,>,divides)")
    var = ex.get("inductionVar")
    if not var:
        raise InductionError("missing inductionVar")
    var = str(var)

    env: dict[str, str] = {var: "N"}
    _infer(goal, "Q", env, indvar=var)
    if env.get(var) != "N":
        raise InductionError(f"induction variable {var!r} could not be typed as ℕ")

    sort = _numsort(ex, goal)
    ctx = _Ctx(sort, env)
    # Translate the goal first so `ctx` learns which built-ins/defs are needed,
    # but recursive defs must be emitted before the goal references them.
    defs = ""
    definitions = ex.get("definitions") or []
    if any(d.get("lhs", {}).get("type") == "pow" for d in definitions):
        defs += _build_pow(definitions, ctx)
    defs += _build_apply_defs(definitions, ctx)
    goal_bool = _goal_term(goal, ctx)
    preamble = _preamble(ctx, defs)

    num_vars = sorted(v for v, d in env.items() if d == "Q")
    return preamble, goal_bool, var, num_vars


def build_prove_source(ex: dict) -> str:
    """SMT for proving `∀n.P(n)`: assert the negated universally-quantified goal,
    so `unsat` means the theorem holds."""
    preamble, goal_bool, var, num_vars = _translate(ex)
    sort = _numsort(ex, ex["goal"])
    binders = [f"({v} {sort})" for v in num_vars] + [f"({var} Nat)"]
    return (preamble +
            f"(assert (not (forall ({' '.join(binders)}) {goal_bool})))\n"
            "(check-sat)\n")


def build_disprove_source(ex: dict) -> tuple[str, list[str]]:
    """SMT for refuting `∀n.P(n)`: the induction variable is a *free* constant and
    we ask cvc5 (with `--fmf-fun`) to find a numeric model — a counterexample. Also
    returns the `get-value` labels naming the witness."""
    preamble, goal_bool, var, num_vars = _translate(ex)
    sort = _numsort(ex, ex["goal"])
    decls = [f"(declare-const {v} {sort})" for v in num_vars]
    decls.append(f"(declare-const {var} Nat)")
    labels = list(num_vars) + [var]
    getvals = " ".join(f"(val {var})" if lbl == var else lbl for lbl in labels)
    return (preamble + "\n".join(decls) + "\n" +
            f"(assert (not {goal_bool}))\n"
            "(check-sat)\n"
            f"(get-value ({getvals}))\n"), labels


def build_source(ex: dict) -> str:
    """The prove-source (used by tests / inspection)."""
    return build_prove_source(ex)


# ---------------------------------------------------------------------------
# Public API.
# ---------------------------------------------------------------------------
@dataclass
class CertifyResult:
    # outcome maps onto the protocol: "proven_equal" (certified),
    # "proven_unequal" (witness), "equal_no_certificate" (believed, no recheck),
    # or "unknown" (inconclusive / unavailable / untranslatable).
    outcome: str
    certified: bool
    method: str            # "alethe+carcara" | "quant-ind" | "fmf-fun" | "rejected" | "unavailable" | "untranslatable"
    witness: dict | None = None
    detail: str = ""


# Default: trust cvc5's sound induction calculus as the certifying engine (the
# same trust leanregate places in the Lean kernel — neither runs a *second*
# checker by default). Set CVC5REGATE_REQUIRE_RECHECK=1 for the protocol-purist
# stance: certify only when an Alethe proof is *independently* re-checked by
# Carcara; an un-re-checked `unsat` then degrades to `equal_no_certificate`.
REQUIRE_RECHECK = os.environ.get("CVC5REGATE_REQUIRE_RECHECK", "0") == "1"

_CACHE: dict[str, CertifyResult] = {}


def certify(ex: dict) -> CertifyResult:
    """Decide `∀ inductionVar. goal` with cvc5. Disprove-first (cheap), then prove."""
    try:
        prove_src = build_prove_source(ex)
        disprove_src, labels = build_disprove_source(ex)
    except InductionError as e:
        return CertifyResult("unknown", False, "untranslatable", detail=str(e))

    key = hashlib.sha256((prove_src + str(REQUIRE_RECHECK)).encode()).hexdigest()
    if key in _CACHE:
        return _CACHE[key]
    if not cvc5_prover.cvc5_available():
        return CertifyResult("unknown", False, "unavailable",
                             detail="cvc5 toolchain unavailable")

    # 1) Disprove first (ground-truth counterexample search) — robust.py philosophy.
    dis = cvc5_prover.disprove(disprove_src, labels)
    if dis.verdict == "sat" and dis.witness:
        return _store(key, CertifyResult("proven_unequal", False, "fmf-fun",
                                         witness=dis.witness,
                                         detail="cvc5 found a counterexample"))

    # 2) Prove (structural induction), with an optional Alethe+Carcara re-check.
    res = cvc5_prover.prove(prove_src, want_certificate=True)
    if res.verdict == "unsat":
        if res.rechecked:
            return _store(key, CertifyResult("proven_equal", True, "alethe+carcara",
                                             detail="cvc5 proof re-checked by Carcara"))
        if REQUIRE_RECHECK:
            return _store(key, CertifyResult("equal_no_certificate", False, "quant-ind",
                                             detail="cvc5 proved it but no independently "
                                                    "re-checked Alethe certificate is available"))
        return _store(key, CertifyResult("proven_equal", True, "quant-ind",
                                         detail="proved by cvc5 structural induction"))
    if res.verdict == "sat":
        # A `sat` on the universally-quantified prove query is itself a refutation,
        # though without an extractable numeric witness here.
        return _store(key, CertifyResult("unknown", False, "rejected",
                                         detail="cvc5 refuted the universal but produced no witness"))
    return _store(key, CertifyResult("unknown", False, "rejected", detail=res.detail[:600]))


def _store(key: str, result: CertifyResult) -> CertifyResult:
    _CACHE[key] = result
    return result


# ---------------------------------------------------------------------------
# Grading the STUDENT's derivation strictly (rule-instance, NOT value-equivalence).
#
# Each step must be an instance of the *claimed rule* at the *claimed path*
# producing exactly the claimed result (step_check); each Type-B step must
# substitute exactly the inductive hypothesis. No value-equivalence leniency — a
# step that reaches a value-equal state by any other means than the claimed rule
# is rejected. SMT cannot enforce this (it proves any arithmetic-true equality,
# regardless of the claimed rule), so the rule-instance check is symbolic. Both
# obligations must reduce to a reflexive `t = t`; cvc5 then BACKSTOPS the leap by
# certifying the goal. Invalid step ⇒ `invalid`; an unknown/guarded rule, or a
# goal cvc5 cannot certify ⇒ `uncertifiable` (→ unknown); a missing/half-empty
# submission ⇒ `unattempted` (→ unknown) — never an auto-pass.
# ---------------------------------------------------------------------------
@dataclass
class GradeResult:
    status: str      # "certified" | "invalid" | "unattempted" | "uncertifiable" | "untranslatable" | "unavailable"
    reason: str = ""


def grade_derivation(ex: dict, sub: dict) -> GradeResult:
    goal = ex.get("goal")
    var = ex.get("inductionVar")
    if not goal or goal.get("type") != "eq" or not var:
        return GradeResult("untranslatable",
                           "derivation grading needs an equality goal with an inductionVar")
    var = str(var)
    base_steps = (sub.get("base") or {}).get("steps")
    step_steps = (sub.get("step") or {}).get("steps")
    if not base_steps or not step_steps:
        return GradeResult("unattempted",
                           "no induction derivation submitted (need both a base-case and an "
                           "inductive-step derivation)")

    rules = step_check.build_rules(ex)
    ac = step_check.ac_ops(ex)   # () unless exercise.options.ac_normalization
    base0 = step_check.substitute(goal, var, {"type": "number", "value": "0"})
    base = step_check.check_case(base0, base_steps, rules, ih=None, ac=ac)
    if base.status == "invalid":
        return GradeResult("invalid", f"base case: {base.reason}")
    if base.status != "certified":
        return GradeResult("uncertifiable", f"base case: {base.reason}")
    if not step_check.is_reflexive(base.final, ac):
        return GradeResult("invalid", "base case did not reduce both sides to a common form (t = t)")
    succ = {"type": "succ", "slots": {"inner": [{"type": "variable", "value": var}]}}
    step0 = step_check.substitute(goal, var, succ)
    ih = (goal["slots"]["left"][0], goal["slots"]["right"][0])
    stp = step_check.check_case(step0, step_steps, rules, ih=ih, ac=ac)
    if stp.status == "invalid":
        return GradeResult("invalid", f"inductive step: {stp.reason}")
    if stp.status != "certified":
        return GradeResult("uncertifiable", f"inductive step: {stp.reason}")
    if not step_check.is_reflexive(stp.final, ac):
        return GradeResult("invalid", "inductive step did not reduce both sides to a common form (t = t)")

    # Every student step is a valid rule-instance and both obligations close. cvc5
    # backstops the induction leap by certifying the goal (disprove-first, then prove).
    if not cvc5_prover.cvc5_available():
        return GradeResult("uncertifiable",
                           "derivation steps are valid but cvc5 is unavailable to certify "
                           "the induction leap")
    cert = certify(ex)
    if cert.certified:
        return GradeResult("certified",
                           "every step is the claimed rule applied correctly, and cvc5 certifies "
                           "the induction")
    return GradeResult("uncertifiable",
                       f"derivation steps are valid but cvc5 did not certify the goal ({cert.method})")
