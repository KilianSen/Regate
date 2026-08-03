from __future__ import annotations

import hashlib
import os
import re
from dataclasses import dataclass
from fractions import Fraction

import cvc5_prover
import step_check  # strict symbolic rule-instance checking of the student's steps

THEOREM_VAR = "n"   # cosmetic; the actual induction var name comes from the request


class InductionError(ValueError):
    """The induction goal/definitions are outside the supported SMT fragment."""


# Relational goal node types and their SMT operators.
_REL = {"eq": "=", "le": "<=", "lt": "<", "ge": ">=", "gt": ">"}
_BIN = {"add": "+", "sub": "-", "mul": "*"}
_NUM_SORTS = {"int": "Int", "rat": "Real"}


# ---------------------------------------------------------------------------
# Datatype descriptor (since 1.1): the type of the induction variable. Defaults
# to ℕ (zero/succ) when `exercise.datatype` is absent, so ℕ induction is byte-for-
# byte unchanged. A constructor field whose sort is the datatype's own name is a
# *recursive* position (each yields an IH). Exactly one non-recursive ("base") and
# one recursive ("step") constructor are supported — ℕ, lists, binary trees —
# deliberately bounded short of a general datatype / proof-assistant engine.
#
# ℕ keeps its legacy node forms (`number 0` = zero, `succ` node = succ, and the
# `val : Nat→Int` coercion for ℕ values in numeric positions). Other datatypes use
# `apply`-form constructors (`nil`, `cons h t`) and never coerce — their induction
# variable only ever appears as a recursive-function argument.
# ---------------------------------------------------------------------------
@dataclass
class _Field:
    name: str
    sort: str            # a datatype name (recursive) or "int"/"rat"


@dataclass
class _Ctor:
    name: str
    fields: list         # list[_Field]


@dataclass
class _Datatype:
    name: str
    ctors: list          # list[_Ctor]

    def recursive_fields(self, ctor) -> list:
        return [f for f in ctor.fields if f.sort == self.name]

    def base_ctor(self) -> "_Ctor":
        cs = [c for c in self.ctors if not self.recursive_fields(c)]
        if len(cs) != 1:
            raise InductionError(f"datatype {self.name!r} needs exactly one non-recursive constructor")
        if cs[0].fields:
            raise InductionError(f"base constructor {cs[0].name!r} must be nullary")
        return cs[0]

    def step_ctor(self) -> "_Ctor":
        cs = [c for c in self.ctors if self.recursive_fields(c)]
        if len(cs) != 1:
            raise InductionError(f"datatype {self.name!r} needs exactly one recursive constructor")
        return cs[0]

    def declare(self) -> str:
        parts = []
        for c in self.ctors:
            if not c.fields:
                parts.append(f"({c.name})")
                continue
            fs = " ".join(
                f"({f.name} {self.name if f.sort == self.name else _NUM_SORTS.get(f.sort, 'Int')})"
                for f in c.fields)
            parts.append(f"({c.name} {fs})")
        return f"(declare-datatype {self.name} ({' '.join(parts)}))"


_NAT = _Datatype("Nat", [_Ctor("zero", []), _Ctor("succ", [_Field("pred", "Nat")])])


def _parse_datatype(ex: dict) -> _Datatype:
    d = ex.get("datatype")
    if not d:
        return _NAT
    name = str(d.get("name") or "")
    if not name:
        raise InductionError("exercise.datatype needs a name")
    ctors = [_Ctor(str(c.get("name")),
                   [_Field(str(f.get("name")), str(f.get("sort")))
                    for f in (c.get("fields") or [])])
             for c in (d.get("constructors") or [])]
    if not ctors:
        raise InductionError("exercise.datatype needs constructors")
    # Every field sort must be the datatype itself (recursive) or a known numeric
    # domain. Do NOT silently coerce an unknown sort to Int: `∀(h:Int)` is a *weaker*
    # claim than `∀(h:Real)`, so a typo like "real" would let cvc5 certify a goal that
    # is false over the intended rationals — the one non-fail-safe mistranslation.
    allowed = {name, "int", "rat"}
    for c in ctors:
        for f in c.fields:
            if f.sort not in allowed:
                raise InductionError(
                    f"field {f.name!r} of constructor {c.name!r} has unknown sort {f.sort!r} "
                    f"(expected {name!r}, 'int', or 'rat')")
    dt = _Datatype(name, ctors)
    dt.base_ctor(); dt.step_ctor()      # validate the bounded shape up front
    return dt


def _ctor_of(node: dict, dt: _Datatype):
    """The datatype constructor `node` is an instance of, or None. ℕ uses `number 0`
    / `succ`; other datatypes use `apply`-form constructors."""
    t = node.get("type")
    if dt.name == "Nat":
        if t == "number" and str(node.get("value")) == "0":
            return next((c for c in dt.ctors if c.name == "zero"), None)
        if t == "succ":
            return next((c for c in dt.ctors if c.name == "succ"), None)
        return None
    if t == "apply":
        return next((c for c in dt.ctors if c.name == str(node.get("value"))), None)
    return None


def _rec_index(args: list, dt: _Datatype):
    """Index of the argument in constructor position (the recursion argument), or None."""
    for i, a in enumerate(args):
        if _ctor_of(a, dt) is not None:
            return i
    return None


def _signatures(definitions: list, dt: _Datatype) -> dict:
    """function name → ["dt"|"num"] per argument, from the constructor-matched arg
    across its base/step rules. Drives argument routing in `_infer` and `_term`."""
    sigs: dict[str, list] = {}
    for d in definitions:
        lhs = d.get("lhs", {})
        if lhs.get("type") != "apply":
            continue
        name = str(lhs["value"])
        args = lhs["slots"]["args"]
        sig = sigs.setdefault(name, ["num"] * len(args))
        for i, a in enumerate(args):
            if _ctor_of(a, dt) is not None:
                sig[i] = "dt"
    return sigs


# ---------------------------------------------------------------------------
# Typing: which variables are the induction datatype vs numeric (ℚ/ℤ).
# The datatype tag is "N" for ℕ (legacy, gets the `val` coercion) or the datatype
# name otherwise. Mirrors lean_induction._infer.
# ---------------------------------------------------------------------------
def _infer(node: dict, dom: str, env: dict[str, str], indvar: str = "",
           sigs: dict | None = None, dt: _Datatype = _NAT) -> None:
    sigs = sigs if sigs is not None else {}
    dt_tag = "N" if dt.name == "Nat" else dt.name
    t = node.get("type")
    if t in ("variable", "wild"):
        name = str(node["value"])
        # The induction variable is ALWAYS the datatype (cvc5 inducts on it
        # structurally); for ℕ it is coerced via `val` wherever it appears numeric,
        # so it is exempt from the numeric/datatype consistency check.
        if name == indvar:
            env[name] = dt_tag
            return
        if env.get(name, dom) != dom:
            raise InductionError(f"variable {name!r} is used at two incompatible sorts")
        env[name] = dom
        return
    if t == "number":
        return
    s = node.get("slots") or {}
    if t == "succ":
        _infer(s["inner"][0], "N", env, indvar, sigs, dt)
    elif t == "pow":
        _infer(s["base"][0], "Q", env, indvar, sigs, dt)
        _infer(s["exponent"][0], "N", env, indvar, sigs, dt)
    elif t == "frac":
        _infer(s["numerator"][0], "Q", env, indvar, sigs, dt)
        _infer(s["denominator"][0], "Q", env, indvar, sigs, dt)
    elif t in _BIN:
        # `add` may be ℕ (an exponent sum) or numeric; inherit the context domain.
        _infer(s["left"][0], dom, env, indvar, sigs, dt)
        _infer(s["right"][0], dom, env, indvar, sigs, dt)
    elif t == "neg":
        _infer(s["inner"][0], dom, env, indvar, sigs, dt)
    elif t == "apply":
        name = str(node["value"])
        args = s["args"]
        if _ctor_of(node, dt) is not None:
            # A datatype constructor application (e.g. `cons h t`): recursive fields
            # are the datatype, the rest numeric.
            ctor = _ctor_of(node, dt)
            for f, a in zip(ctor.fields, args):
                _infer(a, dt.name if f.sort == dt.name else "Q", env, indvar, sigs, dt)
            return
        sig = sigs.get(name)
        if sig is None:
            # Legacy ℕ default: last argument is the recursion variable, rest numeric.
            # A *nullary* application has no such argument — without this guard the
            # `args[-1]` below raised an uncaught IndexError (HTTP 500 / exit 1) on any
            # request carrying an undefined nullary `apply` (e.g. a bare `nil`).
            if dt.name != "Nat" or not args:
                raise InductionError(f"unknown function {name!r} (no definition)")
            for a in args[:-1]:
                _infer(a, "Q", env, indvar, sigs, dt)
            _infer(args[-1], "N", env, indvar, sigs, dt)
            return
        for a, srt in zip(args, sig):
            _infer(a, dt_tag if srt == "dt" else "Q", env, indvar, sigs, dt)
    elif t in _REL:
        _infer(s["left"][0], "Q", env, indvar, sigs, dt)
        _infer(s["right"][0], "Q", env, indvar, sigs, dt)
    elif t == "divides":
        _infer(s["value"][0], "Q", env, indvar, sigs, dt)
    else:
        raise InductionError(f"cannot type node type {t!r}")


# ---------------------------------------------------------------------------
# MathNode -> SMT term.  Numeric sort S is "Real" (ℚ) or "Int".
# ---------------------------------------------------------------------------
class _Ctx:
    """Mutable translation state: the datatype, function signatures, and which
    built-ins the emitted file needs."""
    def __init__(self, sort: str, env: dict[str, str],
                 dt: _Datatype = _NAT, sigs: dict | None = None):
        self.sort = sort
        self.env = env
        self.dt = dt
        self.sigs = sigs if sigs is not None else {}
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


def _dt_term(node: dict, ctx: _Ctx) -> str:
    """A datatype-sorted term for `ctx.dt`: the induction variable, or a constructor
    application. For ℕ this is the exponent / succ-argument position (`_nat_term`);
    for other datatypes it emits `apply`-form constructors (`nil`, `(cons h t)`)."""
    dt = ctx.dt
    t = node.get("type")
    if t in ("variable", "wild"):
        return str(node["value"])
    if dt.name == "Nat":
        if t == "number":
            k = int(str(node["value"]))
            if k < 0:
                raise InductionError("negative ℕ literal")
            return _nat_lit(k)
        s = node.get("slots") or {}
        if t == "succ":
            return f"(succ {_dt_term(s['inner'][0], ctx)})"
        if t == "add":
            ctx.need_nplus = True
            return f"(nplus {_dt_term(s['left'][0], ctx)} {_dt_term(s['right'][0], ctx)})"
        raise InductionError(f"cannot translate node type {t!r} to ℕ")
    ctor = _ctor_of(node, dt)
    if ctor is None:
        raise InductionError(f"{node.get('value')!r} is not a constructor of {dt.name}")
    args = (node.get("slots") or {}).get("args", [])
    parts = [_dt_term(a, ctx) if f.sort == dt.name else _term(a, ctx)
             for f, a in zip(ctor.fields, args)]
    return f"({ctor.name} {' '.join(parts)})" if parts else ctor.name


def _term(node: dict, ctx: _Ctx) -> str:
    """A numeric (Real/Int) SMT term."""
    t = node.get("type")
    if t in ("variable", "wild"):
        name = str(node["value"])
        tag = ctx.env.get(name)
        if tag == "N":
            return _coerce(name, ctx.sort, ctx)
        if tag is not None and tag not in ("Q",):
            raise InductionError(f"{name!r} is a {tag} value, not numeric")
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
        exp = _dt_term(s["exponent"][0], ctx)
        return f"(pow {base} {exp})"
    if t == "apply":
        fname = str(node["value"])
        args = s["args"]
        sig = ctx.sigs.get(fname)
        if sig is None:
            # Legacy ℕ default: last argument is the recursion variable, rest numeric.
            # `not args` guards the same nullary-application IndexError as `_infer`.
            if ctx.dt.name != "Nat" or not args:
                raise InductionError(f"unknown function {fname!r} (no definition)")
            parts = [_term(a, ctx) for a in args[:-1]] + [_dt_term(args[-1], ctx)]
        else:
            parts = [_dt_term(a, ctx) if srt == "dt" else _term(a, ctx)
                     for a, srt in zip(args, sig)]
        return f"({fname} {' '.join(parts)})"
    if t == "succ":
        # A ℕ value appearing where a number is wanted, e.g. the `(k+1)` summand
        # in a sum's recursive step — coerce it.
        return _coerce(_dt_term(node, ctx), ctx.sort, ctx)
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


def _ctor_field_names(node: dict, dt: _Datatype) -> list[str]:
    """Pattern-variable names bound by a constructor pattern in a definition rule:
    `succ(k)` → ["k"]; `cons(h, t)` → ["h", "t"]."""
    t = node.get("type")
    if t == "succ":
        return [_wild(node["slots"]["inner"][0])]
    if t == "apply":
        return [_wild(a) for a in (node.get("slots") or {}).get("args", [])]
    return []


def _fresh(base: str, used: set) -> str:
    name, i = base, 0
    while name in used:
        i += 1
        name = f"{base}{i}"
    return name


def _apply_names(node: dict) -> set:
    """Every function/constructor name applied anywhere in `node`."""
    names = {str(node["value"])} if node.get("type") == "apply" else set()
    for kids in (node.get("slots") or {}).values():
        for k in kids:
            names |= _apply_names(k)
    return names


def _plain_def(name: str, rules: list[dict], ctx: _Ctx) -> str:
    """A NON-recursive named operator as a plain `define-fun`.

    This is the escape hatch a host uses to add an ordinary binary/n-ary operator as
    *data* — one defining equation with pattern-variable parameters, e.g.
    `avg(a, b) → (a + b)/2` — instead of a new MathNode type wired into the backend.
    A non-recursive `define-fun` is a definitional extension (a macro): unfolding it
    is conservative, so it is strictly safer than the `define-fun-rec` axiom a
    recursive definition emits. It is also purely *syntactic* power: the body must
    already be translatable vocabulary, so this widens the surface syntax, it does
    not widen the SMT fragment.

    Requirements, each an `InductionError` (→ `unknown`, never a wrong grade):
    exactly one equation (a case split must be given as constructor rules), distinct
    pattern-variable parameters, and no self-reference (`define-fun` cannot recurse —
    a recursive operator needs the base/step constructor rules below).
    """
    if len(rules) != 1:
        raise InductionError(
            f"non-recursive function {name!r} needs exactly one defining equation "
            f"(got {len(rules)}); a case split must be given as constructor rules")
    d = rules[0]
    params = [_wild(a) for a in d["lhs"]["slots"]["args"]]
    if len(set(params)) != len(params):
        raise InductionError(f"definition of {name!r} repeats a parameter name")
    if name in _apply_names(d["rhs"]):
        raise InductionError(
            f"{name!r} is defined non-recursively but its body calls itself; supply a "
            f"{ctx.dt.base_ctor().name}-rule and a {ctx.dt.step_ctor().name}-rule instead")
    body = _term(d["rhs"], ctx)
    ps = " ".join(f"({p} {ctx.sort})" for p in params)
    return f"(define-fun {name} ({ps}) {ctx.sort}\n  {body})\n"


def _build_apply_defs(definitions: list[dict], ctx: _Ctx) -> str:
    """SMT definitions for every function supplied as `apply` definitions.

    Two shapes, distinguished by whether the left-hand side matches a constructor:

    * **recursive** — a base-constructor rule and a step-constructor rule, recursing
      on the constructor-matched argument (any position, per the datatype
      descriptor) → `define-fun-rec` over a `match`.
    * **non-recursive** — a single equation over pattern variables (`avg(a,b) → …`)
      → a plain `define-fun` (see `_plain_def`). This is what lets a host add an
      ordinary binary operator without a new MathNode type.
    """
    dt = ctx.dt
    base_c, step_c = dt.base_ctor(), dt.step_ctor()
    by_name: dict[str, dict] = {}
    plain: dict[str, list] = {}
    order: list[str] = []
    for d in definitions:
        lhs = d.get("lhs", {})
        if lhs.get("type") != "apply":
            continue
        name = str(lhs["value"])
        args = lhs["slots"]["args"]
        if name not in order:
            order.append(name)
        ridx = _rec_index(args, dt)
        if ridx is None:
            plain.setdefault(name, []).append(d)
            continue
        ctor = _ctor_of(args[ridx], dt)
        by_name.setdefault(name, {})[ctor.name] = (d, ridx)
    out = []
    for name in order:                       # emit in the order the request declared them
        if name in plain and name in by_name:
            raise InductionError(
                f"definition of {name!r} mixes constructor rules with a non-recursive "
                f"equation; give either one equation or a full set of constructor rules")
        if name in plain:
            out.append(_plain_def(name, plain[name], ctx))
            continue
        rules = by_name[name]
        if base_c.name not in rules or step_c.name not in rules:
            raise InductionError(
                f"recursive function {name!r} needs a {base_c.name}-rule and a {step_c.name}-rule")
        base_d, bridx = rules[base_c.name]
        step_d, sridx = rules[step_c.name]
        if bridx != sridx:
            raise InductionError(f"{name!r} recurses on inconsistent argument positions")
        ridx = sridx
        s_args = step_d["lhs"]["slots"]["args"]
        b_args = base_d["lhs"]["slots"]["args"]
        # The emitted parameters come from the STEP rule, but the base rule's body is
        # translated as written — so the two rules must name the shared (non-recursion)
        # parameters identically, or the base branch would reference an unbound symbol
        # and cvc5 would fail to parse the file. Decline cleanly instead.
        if len(b_args) != len(s_args):
            raise InductionError(
                f"{name!r}: the {base_c.name}-rule takes {len(b_args)} arguments but the "
                f"{step_c.name}-rule takes {len(s_args)}")
        for i, (ba, sa) in enumerate(zip(b_args, s_args)):
            if i == ridx:
                continue
            if _wild(ba) != _wild(sa):
                raise InductionError(
                    f"{name!r}: the {base_c.name}-rule calls argument {i} {_wild(ba)!r} but the "
                    f"{step_c.name}-rule calls it {_wild(sa)!r}; use one name in both rules")
        fields = _ctor_field_names(s_args[ridx], dt)
        used = {_wild(a) for i, a in enumerate(s_args) if i != ridx} | set(fields)
        subj = _fresh(dt.name.lower(), used)         # the match subject (recursion param)
        params = [f"({subj} {dt.name})" if i == ridx else f"({_wild(a)} {ctx.sort})"
                  for i, a in enumerate(s_args)]
        base_body = _term(base_d["rhs"], ctx)
        step_body = _term(step_d["rhs"], ctx)
        step_pat = step_c.name if not fields else f"({step_c.name} {' '.join(fields)})"
        out.append(
            f"(define-fun-rec {name} ({' '.join(params)}) {ctx.sort}\n"
            f"  (match {subj} (({base_c.name} {base_body}) ({step_pat} {step_body}))))\n"
        )
    return "".join(out)


# ---------------------------------------------------------------------------
# `exercise.assumptions` — the declared facts that scope the exercise's domain.
#
# The protocol's `Assumption` is `{"kind": "nonzero"|"positive"|"integer"|
# "constant", "value": <MathNode>}`. They are NOT decoration: SMT-LIB leaves
# `(/ x 0)` underspecified, so a bare `x/x = 1` query is `sat` at `x = 0` and the
# counterexample search happily returns the very point the exercise excluded — a
# WRONG GRADE (`proven_unequal` on a correct answer). They are equally load-bearing
# on the prove side: `x/x = 1` is only *valid* under the hypothesis `x ≠ 0`.
#
# So every SMT query built from an exercise carries them: as a hypothesis
# (`(=> guard goal)`) in a prove query, and as an asserted constraint on the model
# in a disprove query. A kind we cannot translate soundly makes the whole query
# DECLINE (`InductionError` → `unknown`) — silently dropping an assumption is what
# produced the wrong grade in the first place.
#
# `constant` is deliberately NOT translatable: it is a syntactic property of the
# matched subterm ("is a numeral", cf. eggregate's `conditions.discharge`), not a
# constraint on a numeric model, so there is no faithful SMT reading of it.
# ---------------------------------------------------------------------------
TRANSLATABLE_ASSUMPTIONS = ("nonzero", "positive", "integer")


def parse_assumptions(ex: dict) -> list[dict]:
    """`exercise.assumptions`, structurally validated. Raises `InductionError` for a
    malformed entry or a kind with no sound SMT reading, so the caller declines."""
    raw = ex.get("assumptions") or []
    if not isinstance(raw, list):
        raise InductionError("exercise.assumptions must be a list")
    out = []
    for a in raw:
        if not isinstance(a, dict) or "kind" not in a or "value" not in a:
            raise InductionError("each assumption needs a 'kind' and a 'value'")
        kind = str(a["kind"])
        if kind not in TRANSLATABLE_ASSUMPTIONS:
            raise InductionError(
                f"assumption kind {kind!r} has no sound SMT translation "
                f"(supported: {', '.join(TRANSLATABLE_ASSUMPTIONS)})")
        if not isinstance(a["value"], dict):
            raise InductionError("assumption 'value' must be a MathNode")
        out.append({"kind": kind, "value": a["value"]})
    return out


def _infer_assumptions(assumps: list[dict], env: dict[str, str], indvar: str,
                       sigs: dict, dt: _Datatype) -> None:
    """Type the assumption terms into the same environment as the goal, so a variable
    mentioned only by an assumption still gets declared/bound in the emitted file."""
    for a in assumps:
        _infer(a["value"], "Q", env, indvar, sigs, dt)


def _assumption_bools(assumps: list[dict], ctx: _Ctx) -> list[str]:
    """The assumptions as SMT Bools over `ctx`."""
    zero = _num_lit(0, ctx.sort)
    out = []
    for a in assumps:
        term = _term(a["value"], ctx)
        kind = a["kind"]
        if kind == "nonzero":
            out.append(f"(not (= {term} {zero}))")
        elif kind == "positive":
            out.append(f"(> {term} {zero})")
        elif kind == "integer":
            # Integral by construction in the ℤ domain; `is_int` is the Reals_Ints
            # predicate for ℚ.
            out.append("true" if ctx.sort == "Int" else f"(is_int {term})")
        else:                                    # unreachable: parse_assumptions filters
            raise InductionError(f"assumption kind {kind!r} has no sound SMT translation")
    return out


def _guard_of(assumps: list[dict], ctx: _Ctx) -> str:
    """The conjunction of the assumptions, or "" when there are none."""
    bools = _assumption_bools(assumps, ctx)
    if not bools:
        return ""
    return bools[0] if len(bools) == 1 else f"(and {' '.join(bools)})"


def _under_guard(guard: str, body: str) -> str:
    """`body` under the declared assumptions. Negating this once yields BOTH queries:
    `(not (forall … (=> guard body)))` proves, and `(not (=> guard body))` — i.e.
    `guard ∧ ¬body` — searches for a counterexample *inside* the assumed domain."""
    return f"(=> {guard} {body})" if guard else body


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
    lines = ["(set-logic ALL)", ctx.dt.declare()]
    if ctx.need_val:
        lines.append("(define-fun-rec val ((n Nat)) Int "
                     "(match n ((zero 0) ((succ k) (+ 1 (val k))))))")
    if ctx.need_nplus:
        lines.append("(define-fun-rec nplus ((m Nat) (n Nat)) Nat "
                     "(match m ((zero n) ((succ k) (succ (nplus k n))))))")
    return "\n".join(lines) + "\n" + defs_block


def _translate(ex: dict, force_val: bool = False) -> tuple[str, str, str, list[str]]:
    """Return (preamble+defs, goal_bool, induction_var, numeric_var_names).

    ``force_val`` emits the ``val : Nat -> Int`` helper even when the goal never
    coerces a ℕ into a numeric position -- the disprove source needs it to read the
    induction variable back out via ``(get-value ((val n)))``.

    The returned goal is already **under the exercise's declared assumptions**
    (``(=> guard goal)``): negated it proves ``guard -> goal``, and as a free-constant
    query it means ``guard AND NOT goal`` -- a counterexample the assumptions admit.
    An assumption we cannot translate raises, so the query declines rather than
    silently dropping it.
    """
    goal = ex.get("goal")
    if not goal or goal.get("type") not in (set(_REL) | {"divides"}):
        raise InductionError("induction goal must be a relation (=,<=,<,>=,>,divides)")
    var = ex.get("inductionVar")
    if not var:
        raise InductionError("missing inductionVar")
    var = str(var)

    dt = _parse_datatype(ex)
    dt_tag = "N" if dt.name == "Nat" else dt.name
    definitions = ex.get("definitions") or []
    sigs = _signatures(definitions, dt)

    assumps = parse_assumptions(ex)
    env: dict[str, str] = {var: dt_tag}
    _infer(goal, "Q", env, var, sigs, dt)
    if env.get(var) != dt_tag:
        raise InductionError(f"induction variable {var!r} could not be typed as {dt.name}")
    _infer_assumptions(assumps, env, var, sigs, dt)

    sort = _numsort(ex, goal)
    ctx = _Ctx(sort, env, dt, sigs)
    ctx.need_val = force_val and dt.name == "Nat"    # `val` is a ℕ-only coercion
    # Translate the goal first so `ctx` learns which built-ins/defs are needed,
    # but recursive defs must be emitted before the goal references them.
    defs = ""
    if any(d.get("lhs", {}).get("type") == "pow" for d in definitions):
        defs += _build_pow(definitions, ctx)
    defs += _build_apply_defs(definitions, ctx)
    goal_bool = _under_guard(_guard_of(assumps, ctx), _goal_term(goal, ctx))
    preamble = _preamble(ctx, defs)

    num_vars = sorted(v for v, d in env.items() if d == "Q")
    return preamble, goal_bool, var, num_vars


def build_prove_source(ex: dict) -> str:
    """SMT for proving `∀n.P(n)`: assert the negated universally-quantified goal,
    so `unsat` means the theorem holds. The goal already carries the exercise's
    declared assumptions as a hypothesis (`_translate`)."""
    preamble, goal_bool, var, num_vars = _translate(ex)
    sort = _numsort(ex, ex["goal"])
    dtname = _parse_datatype(ex).name
    # The induction variable MUST be quantified first: cvc5's --quant-ind inducts on
    # the leading datatype binder. With an accumulator (`x`) ahead of it, cvc5 tries
    # to induct on the numeric `x` and never generalizes the recursion — every
    # accumulator goal then times out. Datatype-first, it inducts on the induction
    # variable with the accumulators kept universal (measured: 30s timeout → 0.01s).
    binders = [f"({var} {dtname})"] + [f"({v} {sort})" for v in num_vars]
    return (preamble +
            f"(assert (not (forall ({' '.join(binders)}) {goal_bool})))\n"
            "(check-sat)\n")


def build_disprove_source(ex: dict) -> tuple[str, list[str]]:
    """SMT for refuting `∀n.P(n)`: the induction variable is a *free* constant and
    we ask cvc5 (with `--fmf-fun`) to find a numeric model — a counterexample. Also
    returns the `get-value` labels naming the witness.

    The asserted body is `(not (=> guard goal))` = `guard ∧ ¬goal`, so a model is a
    counterexample the exercise's `assumptions` actually admit — never the excluded
    point itself (`x = 0` is not a counterexample to `x/x = 1` under `x ≠ 0`)."""
    # `force_val`: the witness is read back as `(val n)`, so `val` must be defined
    # even when the goal itself never coerces `n` into a numeric position. Without
    # it cvc5 parse-errors on the `get-value` and the counterexample is lost.
    preamble, goal_bool, var, num_vars = _translate(ex, force_val=True)
    sort = _numsort(ex, ex["goal"])
    dt = _parse_datatype(ex)
    decls = [f"(declare-const {v} {sort})" for v in num_vars]
    decls.append(f"(declare-const {var} {dt.name})")
    labels = list(num_vars) + [var]
    # ℕ reads the witness numerically via `val`; a non-ℕ datatype has no numeric
    # coercion, so the model value is a constructor term (e.g. `(cons 5 nil)`) the
    # numeric parser cannot read → D4: the witness degrades to empty → `unknown`,
    # never a `proven_unequal` without a witness.
    getvals = " ".join(
        (f"(val {var})" if dt.name == "Nat" else var) if lbl == var else lbl
        for lbl in labels)
    return (preamble + "\n".join(decls) + "\n" +
            f"(assert (not {goal_bool}))\n"
            "(check-sat)\n"
            f"(get-value ({getvals}))\n"), labels


def build_source(ex: dict) -> str:
    """The prove-source (used by tests / inspection)."""
    return build_prove_source(ex)


# ---------------------------------------------------------------------------
# The ruleset's trust boundary.
#
# Regate's premise: a ruleset is authored and formally validated ONCE, upstream.
# This backend validates the student's *derivation* against it, so by default it
# takes the caller's warrant rather than re-proving every rule per submission.
# `options.verify_rules` re-establishes it here — each rule becomes its own SMT
# validity query. Use it for rules from an untrusted source, or in CI.
#
# Why it matters: cvc5's induction certifies the *goal*, not the ruleset, so a
# derivation whose steps cite a false rule (`a*b = b`) would otherwise certify any
# true goal. Unproven is inconclusive (→ `unknown`), never `invalid` — the student
# followed the rule they were handed. Recursive `definitions` are definitional,
# hence always trusted.
#
# Unlike coqregate/leanregate there is no proof-carrying path: an author cannot
# ship an SMT proof for cvc5 to check, because cvc5 1.3.x cannot export one for
# the quantified fragment. Verification here always means re-solving.
# ---------------------------------------------------------------------------
@dataclass
class ProvenRule:
    id: str
    proven: bool
    # "trusted" -- taken on the caller's warrant (verify_rules off)
    # "smt"     -- re-solved here and proven
    method: str      # …| "rejected" | "guarded" | "unavailable" | "untranslatable"
    detail: str = ""


def verify_rules_enabled(ex: dict) -> bool:
    """Should the transmitted ruleset be re-verified rather than trusted?"""
    return bool((ex.get("options") or {}).get("verify_rules"))


def _mentions(node: dict, types: tuple[str, ...]) -> bool:
    if node.get("type") in types:
        return True
    return any(_mentions(ch, types)
               for children in (node.get("slots") or {}).values() for ch in children)


def build_rule_source(rule: dict, ex: dict, use_assumptions: bool = False) -> str:
    """SMT for proving one transmitted rule: assert the negated universally-
    quantified equality, so `unsat` means the rule holds.

    `use_assumptions` puts the exercise's declared `assumptions` in front of the
    equality as a hypothesis (`∀x⃗. guard → lhs = rhs`). It is OFF for *rule
    verification* on purpose: `options.verify_rules` asks whether a rule is valid
    **as transmitted**, and a rule's wildcards are not the exercise's variables, so
    an exercise-level `x ≠ 0` must never be allowed to "prove" an unguarded rule that
    happens to name a wildcard `x`. The equivalence oracle (`cvc5_equiv`) turns it ON:
    there the lhs/rhs *are* the student's expressions, and `x/x = 1` is a theorem only
    under the exercise's `x ≠ 0`.
    """
    lhs_node, rhs_node = rule.get("lhs"), rule.get("rhs")
    if not lhs_node or not rhs_node:
        raise InductionError("rule needs lhs and rhs")
    assumps = parse_assumptions(ex) if use_assumptions else []

    # The datatype + function signatures come from the exercise, exactly as in
    # `_translate`. Without them every `apply` fell back to the legacy ℕ heuristic
    # ("the last argument is the recursion variable"), which mistyped a non-ℕ
    # datatype, mistyped a non-recursive operator's last argument as a ℕ, and crashed
    # outright (IndexError) on a nullary application such as `nil`.
    dt = _parse_datatype(ex)
    definitions = ex.get("definitions") or []
    sigs = _signatures(definitions, dt)

    env: dict[str, str] = {}
    _infer(lhs_node, "Q", env, "", sigs, dt)
    _infer(rhs_node, "Q", env, "", sigs, dt)
    _infer_assumptions(assumps, env, "", sigs, dt)

    sort = _numsort(ex, ex.get("goal") or {"type": "eq"})
    ctx = _Ctx(sort, env, dt, sigs)

    nodes = [lhs_node, rhs_node] + [a["value"] for a in assumps]
    defs = ""
    if any(_mentions(n, ("pow",)) for n in nodes):
        defs += _build_pow(definitions, ctx)
    if any(_mentions(n, ("apply",)) for n in nodes):
        defs += _build_apply_defs(definitions, ctx)

    body = _under_guard(_guard_of(assumps, ctx),
                        f"(= {_term(lhs_node, ctx)} {_term(rhs_node, ctx)})")
    preamble = _preamble(ctx, defs)

    # Datatype binders first (see build_prove_source): a rule quantifying over a ℕ or
    # other datatype variable is proven the same way, and cvc5's induction heuristics
    # lead with the datatype. A variable typed as a non-ℕ datatype (`t : List` in
    # `summa(cons h t) = h + summa t`) previously fell out of the binder list entirely
    # and left an unbound symbol behind — an unprovable file, i.e. a false negative.
    binders = [f"({v} Nat)" for v, d in sorted(env.items()) if d == "N"]
    if dt.name != "Nat":
        binders += [f"({v} {dt.name})" for v, d in sorted(env.items()) if d == dt.name]
    binders += [f"({v} {sort})" for v, d in sorted(env.items()) if d == "Q"]
    if not binders:                       # a ground rule: no quantifier needed
        return preamble + f"(assert (not {body}))\n(check-sat)\n"
    return (preamble +
            f"(assert (not (forall ({' '.join(binders)}) {body})))\n"
            "(check-sat)\n")


_RULE_CACHE: dict[str, ProvenRule] = {}


def prove_rule(rule: dict, ex: dict) -> ProvenRule:
    """SMT-prove one transmitted rule. Unproven is inconclusive, not false."""
    rid = str(rule.get("id", "?"))
    if rule.get("conditions"):
        # A guarded rule (`x/x = 1` needing `x != 0`) is not an unconditional
        # equality; we do not model the side condition, so we cannot prove it.
        return ProvenRule(rid, False, "guarded",
                          "guarded rules are outside the certifiable fragment")
    try:
        source = build_rule_source(rule, ex)
    except InductionError as e:
        return ProvenRule(rid, False, "untranslatable", str(e))

    key = hashlib.sha256(source.encode()).hexdigest()
    if key in _RULE_CACHE:
        return _RULE_CACHE[key]
    if not cvc5_prover.cvc5_available():
        return ProvenRule(rid, False, "unavailable", "cvc5 toolchain unavailable")

    res = cvc5_prover.prove_rule(source)
    result = (ProvenRule(rid, True, "smt") if res.verdict == "unsat"
              else ProvenRule(rid, False, "rejected",
                              f"cvc5 returned {res.verdict}: {res.detail[:300]}"))
    _RULE_CACHE[key] = result
    return result


def prove_ruleset(ex: dict) -> dict[str, ProvenRule]:
    """Establish the ruleset's soundness, keyed by rule id.

    By default this is the caller's warrant, not a solver run: Regate's premise is
    that a ruleset is authored and formally validated upstream, and this backend
    grades derivations against it. `options.verify_rules` re-establishes it here.
    """
    rules = ex.get("ruleset") or []
    if not verify_rules_enabled(ex):
        return {str(r.get("id")): ProvenRule(
            str(r.get("id")), True, "trusted",
            "ruleset warranted valid by the caller; set options.verify_rules to re-prove")
            for r in rules}
    return {str(r.get("id")): prove_rule(r, ex) for r in rules}


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
    if dis.verdict == "sat":
        # D4 — witnesses fail safe. The numeric parser cannot read a datatype
        # counterexample (a constructor term like `(cons -1 nil)`); it would emit a
        # garbage pair (e.g. `{'-': '1'}` from the nested `(- 1)`). Only a witness
        # keyed by the real variables with numeric values is trustworthy — anything
        # else means "the goal is false but we have no reportable witness" → unknown,
        # never a `proven_unequal` carrying a misleading witness.
        # The same gate covers `exercise.assumptions`: a point the exercise excluded
        # is not a counterexample, so a witness we cannot show to satisfy the declared
        # assumptions degrades to `unknown` too.
        if usable_witness(ex, dis.witness, labels):
            return _store(key, CertifyResult("proven_unequal", False, "fmf-fun",
                                             witness=dis.witness,
                                             detail="cvc5 found a counterexample"))
        return _store(key, CertifyResult("unknown", False, "rejected",
                                         detail="cvc5 refuted the goal but produced no numeric "
                                                "witness admitted by the declared assumptions"))

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


_NUM_WITNESS = re.compile(r"^-?\d+(?:\.\d+)?$")


def _usable_witness(witness: dict | None, labels: list[str]) -> bool:
    """A witness is reportable only if every entry names a real variable (one of the
    `get-value` labels) and carries a numeric value. Rejects the misparsed fragments
    a datatype counterexample produces (`{'-': '1'}`), so D4 degrades them to unknown."""
    if not witness:
        return False
    return all(k in labels and _NUM_WITNESS.match(str(v)) for k, v in witness.items())


def _eval_witness(node: dict, values: dict[str, Fraction]) -> Fraction | None:
    """Evaluate a MathNode at the witness point exactly, or `None` if it cannot be
    (an unbound variable, a division by zero, a node outside the rational fragment).
    Deliberately tiny: this is a *safety check*, so "cannot evaluate" must fail."""
    t = node.get("type")
    if t == "number":
        try:
            return Fraction(str(node.get("value")))
        except (ValueError, ZeroDivisionError):
            return None
    if t in ("variable", "wild"):
        return values.get(str(node.get("value")))
    s = node.get("slots") or {}
    try:
        if t in ("add", "sub", "mul", "frac"):
            key = ("numerator", "denominator") if t == "frac" else ("left", "right")
            a, b = _eval_witness(s[key[0]][0], values), _eval_witness(s[key[1]][0], values)
            if a is None or b is None:
                return None
            if t == "add":
                return a + b
            if t == "sub":
                return a - b
            if t == "mul":
                return a * b
            return None if b == 0 else a / b
        if t == "neg":
            v = _eval_witness(s["inner"][0], values)
            return None if v is None else -v
    except (KeyError, IndexError):
        return None
    return None


def witness_respects_assumptions(ex: dict, witness: dict | None) -> bool:
    """Fail-safe (D4 for assumptions): can this counterexample be *shown* to satisfy
    the exercise's declared assumptions?

    The queries already assert the assumptions, so a well-formed `sat` model satisfies
    them by construction — this is the independent second opinion that keeps a
    translation gap from ever surfacing as `proven_unequal`. Anything we cannot
    re-evaluate here (an unbound variable, a term outside the rational fragment, an
    untranslatable kind) answers **no**, and the caller degrades to `unknown`."""
    try:
        assumps = parse_assumptions(ex)
    except InductionError:
        return False
    if not assumps:
        return True
    values: dict[str, Fraction] = {}
    for k, v in (witness or {}).items():
        try:
            values[str(k)] = Fraction(str(v))
        except (ValueError, ZeroDivisionError):
            return False
    for a in assumps:
        v = _eval_witness(a["value"], values)
        if v is None:
            return False
        if a["kind"] == "nonzero" and v == 0:
            return False
        if a["kind"] == "positive" and v <= 0:
            return False
        if a["kind"] == "integer" and v.denominator != 1:
            return False
    return True


def usable_witness(ex: dict, witness: dict | None, labels: list[str]) -> bool:
    """The full witness gate: numerically reportable (D4) **and** admitted by the
    exercise's assumptions. Never emit `proven_unequal` on anything else."""
    return _usable_witness(witness, labels) and witness_respects_assumptions(ex, witness)


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
    status: str      # "certified" | "refuted" | "invalid" | "unattempted" | "uncertifiable" | "untranslatable" | "unavailable"
    reason: str = ""
    witness: dict | None = None      # numeric counterexample, when status == "refuted"
    smtlib: str = ""                 # the SMT-LIB the solver accepted (certificate)
    ruleset: dict | None = None      # per-rule proof status, for meta


def _base_node(dt: _Datatype) -> dict:
    """The base constructor as a MathNode: ℕ `0`, or a nullary `apply` (e.g. `nil`)."""
    if dt.name == "Nat":
        return {"type": "number", "value": "0"}
    return {"type": "apply", "value": dt.base_ctor().name, "slots": {"args": []}}


def _step_node(dt: _Datatype, var: str) -> tuple[dict, list[str]]:
    """The step constructor as a MathNode + the recursion-variable name(s) the IH is
    taken at. ℕ reuses the induction variable as the predecessor (`succ n`, IH at `n`
    — legacy); other datatypes name each field by its descriptor field name and take
    an IH at every recursive field (`cons h t`, IH at `t`; trees → two IHs, M3)."""
    step_c = dt.step_ctor()
    if dt.name == "Nat":
        return ({"type": "succ", "slots": {"inner": [{"type": "variable", "value": var}]}}, [var])
    args, rec_vars = [], []
    for f in step_c.fields:
        args.append({"type": "variable", "value": f.name})
        if f.sort == dt.name:
            rec_vars.append(f.name)
    return ({"type": "apply", "value": step_c.name, "slots": {"args": args}}, rec_vars)


def grade_derivation(ex: dict, sub: dict) -> GradeResult:
    goal = ex.get("goal")
    var = ex.get("inductionVar")
    if not goal or goal.get("type") != "eq" or not var:
        return GradeResult("untranslatable",
                           "derivation grading needs an equality goal with an inductionVar")
    var = str(var)

    # Disprove FIRST, before grading anything: if the goal is false, no derivation
    # of it can be right, and a numeric counterexample is the most useful thing we
    # can hand back. `certify` runs the same cheap `--fmf-fun` model search; its
    # `proven_unequal` verdict used to be unreachable through /grade because we only
    # consulted it *after* both obligations had already certified.
    if cvc5_prover.cvc5_available():
        refute = certify(ex)
        if refute.outcome == "proven_unequal" and refute.witness:
            return GradeResult("refuted", "cvc5 found a counterexample to the goal",
                               witness=refute.witness)

    # Prove the transmitted ruleset: a rule cvc5 cannot prove may never be composed
    # into a certified derivation, however correctly the student applies it.
    proven = prove_ruleset(ex)
    ruleset_meta = {rid: {"proven": p.proven, "method": p.method, "detail": p.detail}
                    for rid, p in proven.items()}

    base_steps = (sub.get("base") or {}).get("steps")
    step_steps = (sub.get("step") or {}).get("steps")
    if not base_steps or not step_steps:
        return GradeResult("unattempted",
                           "no induction derivation submitted (need both a base-case and an "
                           "inductive-step derivation)", ruleset=ruleset_meta)

    try:
        dt = _parse_datatype(ex)
    except InductionError as e:
        return GradeResult("untranslatable", str(e), ruleset=ruleset_meta)
    rules = step_check.build_rules(ex, {rid for rid, p in proven.items() if p.proven})
    ac = step_check.ac_ops(ex)   # () unless exercise.options.ac_normalization
    base0 = step_check.substitute(goal, var, _base_node(dt))
    base = step_check.check_case(base0, base_steps, rules, ih=None, ac=ac)
    if base.status == "invalid":
        return GradeResult("invalid", f"base case: {base.reason}", ruleset=ruleset_meta)
    if base.status != "certified":
        return GradeResult("uncertifiable", f"base case: {base.reason}", ruleset=ruleset_meta)
    if not step_check.is_reflexive(base.final, ac):
        return GradeResult("invalid", "base case did not reduce both sides to a common form (t = t)",
                           ruleset=ruleset_meta)
    step_node, rec_vars = _step_node(dt, var)
    if not rec_vars:
        return GradeResult("uncertifiable",
                           f"{dt.name} step constructor has no recursive position", ruleset=ruleset_meta)
    step0 = step_check.substitute(goal, var, step_node)
    # One IH per recursive field — `P(n)` for ℕ, the tail `P(t)` for a list, and BOTH
    # `P(l)` and `P(r)` for a binary tree. Each is P at that recursion field, universal
    # in its accumulators (wildcarded), matching the goal cvc5 co-quantifies. Wildcarding
    # lets the student apply an IH at a *shifted* accumulator (fact_aux at x·(S n), sum at
    # a+h, aux at (a+1) then (a+1)+nodes l); check_case recovers the instance and re-checks
    # which IH each kind-B step used.
    ihs = []
    for rv in rec_vars:
        rv_node = {"type": "variable", "value": rv}
        ihs.append(
            (step_check.generalize_ih(step_check.substitute(goal["slots"]["left"][0], var, rv_node), rv),
             step_check.generalize_ih(step_check.substitute(goal["slots"]["right"][0], var, rv_node), rv)))
    stp = step_check.check_case(step0, step_steps, rules, ih=ihs, ac=ac)
    if stp.status == "invalid":
        return GradeResult("invalid", f"inductive step: {stp.reason}", ruleset=ruleset_meta)
    if stp.status != "certified":
        return GradeResult("uncertifiable", f"inductive step: {stp.reason}", ruleset=ruleset_meta)
    if not step_check.is_reflexive(stp.final, ac):
        return GradeResult("invalid", "inductive step did not reduce both sides to a common form (t = t)",
                           ruleset=ruleset_meta)

    # Every student step is an instance of a cvc5-proven rule and both obligations
    # close. cvc5 backstops the induction leap by certifying the goal.
    if not cvc5_prover.cvc5_available():
        return GradeResult("uncertifiable",
                           "derivation steps are valid but cvc5 is unavailable to certify "
                           "the induction leap", ruleset=ruleset_meta)
    cert = certify(ex)
    if cert.certified:
        try:
            smtlib = build_prove_source(ex)
        except InductionError:            # cannot happen: certify() just built it
            smtlib = ""
        return GradeResult("certified",
                           "every step is an instance of a cvc5-proven rule, and cvc5 certifies "
                           "the induction",
                           smtlib=smtlib, ruleset=ruleset_meta)
    # A `proven_unequal` cannot occur here: `certify(ex)` is cached, and the
    # disprove-first block at the top of this function already returned `refuted`
    # for any refutable goal. So the only remaining outcome is "cvc5 could not
    # certify within budget" -> uncertifiable (route to review).
    return GradeResult("uncertifiable",
                       f"derivation steps are valid but cvc5 did not certify the goal ({cert.method})",
                       ruleset=ruleset_meta)
