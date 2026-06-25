"""A semantic (numeric) layer: exact evaluation, sound disproof, and the
distinction between "not proven" and "provably unequal".

The proving backends are *proof-theoretic*: they can witness equality (a chain of
rule applications) but a failure is ambiguous -- "not equal, or just not found
within the budget."  This module adds a *model-theoretic* check that resolves the
ambiguity in the safe direction:

  * ``find_counterexample`` plugs random exact-rational values into the free
    variables; if the two terms ever evaluate to *different defined* values, they
    are **provably unequal** -- a sound disproof, no budget caveat.
  * conversely, surviving many random trials is evidence (not proof) of equality.

This is what lets grading return three honest outcomes instead of collapsing an
ambiguous "no proof" into a wrong "unequal" (a false negative).  Arithmetic is
exact (``fractions.Fraction``), and division by zero evaluates to *undefined*
(``None``) rather than crashing or lying.
"""
from __future__ import annotations

import random
from fractions import Fraction

from .model import MathNode

# small pool incl. 0 and negatives, to exercise sign/zero edge cases
_POOL = [Fraction(n) for n in (-3, -2, -1, 0, 1, 2, 3, 5, 7)]


def free_vars(node: MathNode) -> set[str]:
    if node.op in ("variable", "wild"):
        return {node.value}
    out: set[str] = set()
    for k in node.kids:
        out |= free_vars(k)
    return out


def evaluate(node: MathNode, env: dict[str, Fraction]):
    """Exact value of a ground/assigned term, or ``None`` if undefined (÷0)."""
    op = node.op
    if op == "number":
        return Fraction(node.value)
    if op in ("variable", "wild"):
        return env.get(node.value)
    kids = [evaluate(k, env) for k in node.kids]
    if any(k is None for k in kids):
        return None
    if op == "add":
        return kids[0] + kids[1]
    if op == "sub":
        return kids[0] - kids[1]
    if op == "mul":
        return kids[0] * kids[1]
    if op == "frac":                 # kids = [denominator, numerator]
        den, numer = kids[0], kids[1]
        return None if den == 0 else numer / den
    if op == "neg":
        return -kids[0]
    if op == "eq":                   # relational, not a numeric value
        return None
    raise ValueError(f"cannot evaluate {op}")


def find_counterexample(a: MathNode, b: MathNode, trials: int = 300,
                        seed: int = 0) -> dict[str, Fraction] | None:
    """Return a variable assignment where ``a`` and ``b`` differ, else ``None``.

    A returned assignment is a **sound proof of inequality**.  ``None`` means "no
    counterexample found in ``trials``" -- evidence of equality, not a proof.
    """
    rng = random.Random(seed)
    variables = sorted(free_vars(a) | free_vars(b))
    if not variables:                # ground terms: one decisive check
        va, vb = evaluate(a, {}), evaluate(b, {})
        return {} if (va is not None and vb is not None and va != vb) else None
    for _ in range(trials):
        env = {v: rng.choice(_POOL) for v in variables}
        va, vb = evaluate(a, env), evaluate(b, env)
        if va is not None and vb is not None and va != vb:
            return env
    return None


def probably_equal(a: MathNode, b: MathNode, trials: int = 300) -> bool:
    """No counterexample after ``trials`` random points (heuristic, not a proof)."""
    return find_counterexample(a, b, trials) is None
