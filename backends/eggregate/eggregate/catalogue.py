"""The built-in sample ruleset (thesis Table 4 / Appendix A).

The rule *representation* and the wire (de)serialization live in ``rule.py`` --
that is the contract the engine and the grading request depend on.  This module
is only a **built-in ruleset for tests, demos, and the soundness gate**: the
production path takes its rules from the request (``exercise.ruleset``), not from
here.  Re-exports the representation so existing ``from .catalogue import Rule``
call sites keep working.

Wildcards ``a``, ``b``, ``c`` (block ``wild``) match arbitrary subtrees.
"""
from __future__ import annotations

from .model import add, eq, frac, mul, neg, num, sub
from .rule import (  # noqa: F401  (re-exported for back-compat)
    Rule,
    nonzero,
    rule_from_json,
    rule_to_json,
    ruleset_from_json,
    wild,
)

a, b, c, d = wild("a"), wild("b"), wild("c"), wild("d")


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
