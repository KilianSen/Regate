"""Side conditions for guarded rules (thesis Section 5 "where soundness lives").

Many school identities are *conditional* -- ``x/x = 1`` needs ``x != 0``,
``a/(b) `` needs ``b != 0``, taking a root needs non-negativity, and so on.
Encoded as unconditional rewrites they let an engine "verify" unsound steps.
A guarded rule therefore carries one or more ``SideCondition``s that must be
*discharged* before it may fire.

Discharge is three-valued, which is the honest outcome (cf. the doc's point
that a failed equality check is ambiguous):

  * ``DISCHARGED`` -- provably satisfied (a concrete literal decides it, or the
    student/context declared the matching assumption);
  * ``VIOLATED``   -- provably false (e.g. ``nonzero`` of the literal ``0``);
  * ``OPEN``       -- undecided; the student must discharge it (open decision #3:
    a declared assumption, a spawned sub-goal, or a context check).

This generalises the single ``NotEqualToConstant`` the thesis ships today
(Section 6.3) to a small, extensible vocabulary.
"""
from __future__ import annotations

from dataclasses import dataclass

from .model import MathNode

DISCHARGED = "discharged"
VIOLATED = "violated"
OPEN = "open"


@dataclass(frozen=True)
class SideCondition:
    """A guard on a rule, referring to a wildcard by name.

    kind: 'nonzero' | 'positive' | 'integer' | 'constant' | 'notequal'
    arg:  the constant for 'notequal' (ignored otherwise)
    """

    kind: str
    var: str
    arg: int | None = None

    def describe(self, binding: "MathNode | None" = None) -> str:
        # name the student's actual subtree when we have it, else the wildcard
        from .model import pretty
        who = pretty(binding) if binding is not None else self.var
        if self.kind == "notequal":
            return f"{who} != {self.arg}"
        return {"nonzero": f"{who} != 0",
                "positive": f"{who} > 0",
                "integer": f"{who} is an integer",
                "constant": f"{who} is a constant"}.get(self.kind, self.kind)


@dataclass(frozen=True)
class Assumption:
    """A fact the student/context has declared (discharges an OPEN condition)."""

    kind: str
    expr: MathNode


def _as_number(node: MathNode):
    if node.op != "number":
        return None
    try:
        v = int(node.value)
    except ValueError:
        try:
            return float(node.value)
        except ValueError:
            return None
    return v


def discharge(cond: SideCondition, binding: MathNode,
              assumptions: frozenset[Assumption] = frozenset()) -> str:
    """Decide a side condition against the subtree bound to ``cond.var``."""
    n = _as_number(binding)

    if cond.kind == "constant":
        return DISCHARGED if n is not None else VIOLATED

    if cond.kind == "nonzero":
        if n is not None:
            return DISCHARGED if n != 0 else VIOLATED
    elif cond.kind == "positive":
        if n is not None:
            return DISCHARGED if n > 0 else VIOLATED
    elif cond.kind == "integer":
        if n is not None:
            return DISCHARGED if isinstance(n, int) else VIOLATED
    elif cond.kind == "notequal":
        if n is not None:
            return DISCHARGED if n != cond.arg else VIOLATED
    else:
        raise ValueError(f"unknown side condition {cond.kind!r}")

    # Symbolic / compound binding: decidable only via a declared assumption.
    if Assumption(cond.kind, binding) in assumptions:
        return DISCHARGED
    return OPEN
