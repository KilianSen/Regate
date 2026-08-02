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

from .conditions import Assumption
from .model import MathNode

# small pool incl. 0 and negatives, to exercise sign/zero edge cases
_POOL = [Fraction(n) for n in (-3, -2, -1, 0, 1, 2, 3, 5, 7)]

# Exponents beyond this are not worth evaluating exactly (the value explodes and
# a counterexample at a smaller exponent would have been found already).
_MAX_EXPONENT = 64


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
    if op == "succ":
        return kids[0] + 1
    if op == "pow":                  # kids = [base, exponent]
        base, exponent = kids[0], kids[1]
        if exponent.denominator != 1:        # a root, not in the rational fragment
            return None
        e = int(exponent)
        if abs(e) > _MAX_EXPONENT:
            return None
        if base == 0 and e < 0:              # 0^-k is undefined
            return None
        return base ** e
    if op == "eq":                   # relational, not a numeric value
        return None
    # `apply` (protocol 1.1) is a NAMED, uninterpreted function: its meaning lives
    # in the request's recursive `definitions`, which this ℚ evaluator does not
    # unfold. There is no value to compute, so we must not invent one -- raise, and
    # let `_try_evaluate` turn the whole term into "undefined" (see below). Any
    # attempt to "helpfully" return e.g. 0 here would fabricate counterexamples and
    # produce false `proven_unequal` verdicts.
    raise ValueError(f"cannot evaluate {op}")


_EVALUABLE_OPS = frozenset({
    "number", "variable", "wild", "add", "sub", "mul", "frac", "neg", "succ",
    "pow", "eq",
})


def is_evaluable(node: MathNode) -> bool:
    """Is every operator in ``node`` inside the exact-ℚ fragment this module can
    evaluate? ``apply`` (and any unknown op) is not -- see ``audit.audit_rule``,
    which must not report a rule it cannot even evaluate as fuzz-verified."""
    return (node.op in _EVALUABLE_OPS
            and all(is_evaluable(k) for k in node.kids))


def _try_evaluate(node: MathNode, env: dict[str, Fraction]):
    """``evaluate``, but an op outside the rational fragment is *undefined* rather
    than an error -- an unevaluable point can never witness inequality, so
    swallowing it here is sound (it only ever costs us a disproof, never invents
    one).

    This is the load-bearing guarantee for `apply`: a term containing a function
    application evaluates to ``None`` at every point, so ``find_counterexample``
    below can never return an assignment for it -- "cannot decide", never
    "unequal"."""
    try:
        return evaluate(node, env)
    except ValueError:
        return None


def _env_satisfies(env: dict[str, Fraction], assumptions) -> bool:
    """Is this random point admissible under the exercise's declared assumptions?

    A point that violates a declared fact (``x != 0`` at ``x = 0``) is outside the
    exercise's domain and must not be reported as a counterexample. A point where
    the assumed term is itself undefined is likewise rejected.
    """
    for a in assumptions:
        v = _try_evaluate(a.expr, env)
        if v is None:
            return False
        if a.kind == "nonzero" and v == 0:
            return False
        if a.kind == "positive" and v <= 0:
            return False
        if a.kind == "integer" and v.denominator != 1:
            return False
    return True


def find_counterexample(a: MathNode, b: MathNode, trials: int = 300,
                        seed: int = 0,
                        assumptions: frozenset[Assumption] = frozenset(),
                        ) -> dict[str, Fraction] | None:
    """Return a variable assignment where ``a`` and ``b`` differ, else ``None``.

    A returned assignment is a **sound proof of inequality**.  ``None`` means "no
    counterexample found in ``trials``" -- evidence of equality, not a proof.
    Points ruled out by the exercise's ``assumptions`` are never returned: under
    ``x != 0``, ``x = 0`` is not a counterexample to ``x/x = 1``.
    """
    rng = random.Random(seed)
    variables = sorted(free_vars(a) | free_vars(b))
    if not variables:                # ground terms: one decisive check
        if not _env_satisfies({}, assumptions):
            return None
        va, vb = _try_evaluate(a, {}), _try_evaluate(b, {})
        return {} if (va is not None and vb is not None and va != vb) else None
    for _ in range(trials):
        env = {v: rng.choice(_POOL) for v in variables}
        if not _env_satisfies(env, assumptions):
            continue
        va, vb = _try_evaluate(a, env), _try_evaluate(b, env)
        if va is not None and vb is not None and va != vb:
            return env
    return None


def probably_equal(a: MathNode, b: MathNode, trials: int = 300) -> bool:
    """No counterexample after ``trials`` random points (heuristic, not a proof)."""
    return find_counterexample(a, b, trials) is None
