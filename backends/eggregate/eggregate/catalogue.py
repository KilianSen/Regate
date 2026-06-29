"""The rewrite-rule catalogue (thesis Table 4 / Appendix A).

This is the *single shared rule source* of Section 4.3.  Each rule is plain data
-- a left/right pattern over the expression model, a direction, and an optional
side condition.  Two engines consume it without duplicating the rules:

  * ``backend.py`` compiles each entry into an egglog rewrite (equality
    saturation, for equivalence grading and hints);
  * ``hints.py`` interprets each entry directly as a directed tree rewrite
    (the step-by-step engine, mirroring the MS1 kernel).

Wildcards ``a``, ``b``, ``c`` (block ``wild``) match arbitrary subtrees.
``NotEqualToConstant`` is the one ``RuleConstraint`` implemented today
(Section 6.3); ``frac_mul_cancel_left`` uses it to discharge ``c != 0``.
"""
from __future__ import annotations

from dataclasses import dataclass

from .conditions import SideCondition
from .model import MathNode, add, eq, frac, from_json, mul, neg, num, sub, to_json


def wild(name: str) -> MathNode:
    return MathNode("wild", name)


a, b, c, d = wild("a"), wild("b"), wild("c"), wild("d")


def nonzero(var: str) -> SideCondition:
    return SideCondition("nonzero", var)


@dataclass(frozen=True)
class Rule:
    """One rewrite rule from a BlockDefinition bean (thesis ``RewriteRule``)."""

    id: str
    owner: str            # the block that owns the rule
    lhs: MathNode         # pattern
    rhs: MathNode         # template
    bidir: bool = False   # B = bidirectional, F = forward-only
    # Guards that must be discharged before the rule may fire (Section 5).
    conditions: tuple[SideCondition, ...] = ()


# Table 4, verbatim.  F = forward-only, B = bidirectional.
CATALOGUE: list[Rule] = [
    # -- Add -------------------------------------------------------------
    Rule("add_comm",       "add", add(a, b), add(b, a), bidir=True),
    Rule("add_assoc",      "add", add(add(a, b), c), add(a, add(b, c)), bidir=True),
    Rule("add_zero_left",  "add", add(num(0), a), a),
    Rule("add_zero_right", "add", add(a, num(0)), a),
    # -- Sub -------------------------------------------------------------
    Rule("sub_zero_right", "sub", sub(a, num(0)), a),
    Rule("sub_self",       "sub", sub(a, a), num(0)),
    Rule("sub_as_add_neg", "sub", sub(a, b), add(a, neg(b)), bidir=True),
    # -- Mul -------------------------------------------------------------
    Rule("mul_comm",        "mul", mul(a, b), mul(b, a), bidir=True),
    Rule("mul_assoc",       "mul", mul(mul(a, b), c), mul(a, mul(b, c)), bidir=True),
    Rule("mul_one_left",    "mul", mul(num(1), a), a),
    Rule("mul_one_right",   "mul", mul(a, num(1)), a),
    Rule("mul_zero_left",   "mul", mul(num(0), a), num(0)),
    Rule("mul_zero_right",  "mul", mul(a, num(0)), num(0)),
    Rule("mul_distrib",       "mul", mul(a, add(b, c)), add(mul(a, b), mul(a, c)), bidir=True),
    Rule("mul_distrib_right", "mul", mul(add(b, c), a), add(mul(b, a), mul(c, a)), bidir=True),
    # -- Fraction --------------------------------------------------------
    Rule("frac_one_denom", "frac", frac(a, num(1)), a),
    Rule("frac_mul_cancel_left", "frac",
         frac(mul(c, a), mul(c, b)), frac(a, b), conditions=(nonzero("c"),)),
    # A genuinely conditional identity: x/x = 1 only when x != 0.  Unconditional,
    # this would let a student "prove" 0/0 = 1.
    Rule("frac_self_one", "frac", frac(a, a), num(1), conditions=(nonzero("a"),)),
    # Definedness-preserving and guard-free: when a denominator is 0 BOTH sides are
    # undefined (the audit's `_differs` treats undefined==undefined). Kept
    # forward-only (the *combining* direction) so reverse "splitting" can't blow up
    # saturation. a/c + b/c = (a+b)/c ; (a/b)·(c/d) = (a·c)/(b·d).
    Rule("frac_add_same_denom", "frac", add(frac(a, c), frac(b, c)), frac(add(a, b), c)),
    Rule("frac_mul",           "frac", mul(frac(a, b), frac(c, d)), frac(mul(a, c), mul(b, d))),
    # -- Negation --------------------------------------------------------
    Rule("neg_neg",     "neg", neg(neg(a)), a, bidir=True),
    Rule("neg_zero",    "neg", neg(num(0)), num(0)),
    Rule("add_inverse", "neg", add(a, neg(a)), num(0)),
    # Sign algebra — all total (always defined) equalities, safe both ways.
    Rule("neg_add",       "neg", neg(add(a, b)), add(neg(a), neg(b)), bidir=True),
    Rule("neg_sub",       "neg", neg(sub(a, b)), sub(b, a), bidir=True),
    Rule("mul_neg_left",  "mul", mul(neg(a), b), neg(mul(a, b)), bidir=True),
    Rule("mul_neg_right", "mul", mul(a, neg(b)), neg(mul(a, b)), bidir=True),
    Rule("frac_neg",      "frac", neg(frac(a, b)), frac(neg(a), b), bidir=True),
    # -- Equality --------------------------------------------------------
    Rule("eq_symm", "eq", eq(a, b), eq(b, a), bidir=True),
]

BY_ID: dict[str, Rule] = {r.id: r for r in CATALOGUE}


def rules(*ids: str) -> list[Rule]:
    """The subset of the catalogue an exercise makes available."""
    return [BY_ID[i] for i in ids]


# ---------------------------------------------------------------------------
# JSON (de)serialization — so a ruleset can travel in a grading request rather
# than being hardcoded (thesis §6.3, instructor-authored rules).
# ---------------------------------------------------------------------------
_COND_KINDS = {"nonzero", "positive", "integer", "constant", "notequal"}


def _condition_to_json(c: SideCondition) -> dict:
    d = {"kind": c.kind, "var": c.var}
    if c.arg is not None:
        d["arg"] = c.arg
    return d


def _condition_from_json(d: dict) -> SideCondition:
    kind = d["kind"]
    if kind not in _COND_KINDS:
        raise ValueError(f"unknown side-condition kind {kind!r}")
    return SideCondition(kind, d["var"], d.get("arg"))


def rule_to_json(r: Rule) -> dict:
    return {"id": r.id, "owner": r.owner,
            "lhs": to_json(r.lhs), "rhs": to_json(r.rhs),
            "bidirectional": r.bidir,
            "conditions": [_condition_to_json(c) for c in r.conditions]}


def rule_from_json(d: dict) -> Rule:
    if "id" not in d or "lhs" not in d or "rhs" not in d:
        raise ValueError("rule needs id, lhs, rhs")
    return Rule(str(d["id"]), str(d.get("owner", "")),
                from_json(d["lhs"]), from_json(d["rhs"]),
                bool(d.get("bidirectional", False)),
                tuple(_condition_from_json(c) for c in d.get("conditions", [])))


def ruleset_from_json(items: list[dict]) -> list[Rule]:
    seen: set[str] = set()
    out: list[Rule] = []
    for d in items:
        r = rule_from_json(d)
        if r.id in seen:
            raise ValueError(f"duplicate rule id {r.id!r}")
        seen.add(r.id)
        out.append(r)
    return out
