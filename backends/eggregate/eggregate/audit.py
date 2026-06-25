"""Soundness fuzzing of the rule catalogue (the design doc's "verify the rules").

Every rewrite rule claims an *equality*: under its side conditions, LHS == RHS
for all values of its wildcards.  If that claim is false, the whole grader is
unsound -- it will happily "verify" a student step that isn't valid (a false
positive).  This module checks the claim semantically: plug random exact-rational
values into the wildcards, discharge the guard numerically, and assert both sides
evaluate equally.  A single divergence is a concrete counterexample.

It also flags guards that are *not load-bearing* (the rule holds even when the
guard is violated) and -- more importantly -- a guarded rule whose guard is
actually necessary (it fails when violated), confirming the guard earns its keep.
This is the cheap, runtime form of "prove the rule library once."
"""
from __future__ import annotations

import random
from dataclasses import dataclass
from fractions import Fraction

from .catalogue import CATALOGUE, Rule
from .conditions import SideCondition
from .model import MathNode
from .semantics import evaluate, free_vars

_POOL = [Fraction(n) for n in (-3, -2, -1, 0, 1, 2, 3, 5, 7)]


def _guard_holds(cond: SideCondition, env: dict[str, Fraction]) -> bool:
    v = env.get(cond.var)
    if v is None:
        return True
    if cond.kind == "nonzero":
        return v != 0
    if cond.kind == "notequal":
        return v != cond.arg
    if cond.kind == "positive":
        return v > 0
    if cond.kind == "integer":
        return v.denominator == 1
    if cond.kind == "constant":
        return True
    raise ValueError(cond.kind)


def _differs(la, ra) -> bool:
    """Definedness-aware inequality: undefined==undefined, undefined != any value.

    A sound rewrite must *preserve definedness* -- turning an undefined LHS (e.g.
    0/0) into a defined RHS (e.g. 1) is itself unsound, which is precisely what a
    missing ``x != 0`` guard does."""
    if (la is None) != (ra is None):
        return True
    return la is not None and la != ra


@dataclass
class RuleAudit:
    rule_id: str
    sound: bool
    counterexample: dict[str, Fraction] | None = None   # guard held but sides differ
    guard_necessary: bool | None = None                  # a violation that breaks equality exists


def audit_rule(rule: Rule, trials: int = 500, seed: int = 0) -> RuleAudit:
    rng = random.Random(seed)
    wilds = sorted(free_vars(rule.lhs) | free_vars(rule.rhs))
    guard_violation_breaks = False
    for _ in range(trials):
        env = {w: rng.choice(_POOL) for w in wilds}
        la, ra = evaluate(rule.lhs, env), evaluate(rule.rhs, env)
        guarded = all(_guard_holds(c, env) for c in rule.conditions)
        if guarded:
            if _differs(la, ra):
                return RuleAudit(rule.id, sound=False, counterexample=env)
        elif rule.conditions and _differs(la, ra):
            # guard violated AND equality breaks -> the guard is doing real work
            guard_violation_breaks = True
    return RuleAudit(rule.id, sound=True,
                     guard_necessary=(guard_violation_breaks if rule.conditions else None))


def audit_catalogue(rules: list[Rule] | None = None, trials: int = 500):
    """Audit every rule; return the list of audits (unsound ones have sound=False)."""
    return [audit_rule(r, trials) for r in (rules or CATALOGUE)]


# ---------------------------------------------------------------------------
# CI gate:  python -m eggregate.audit  [trials]
# Exits non-zero if any rule is unsound, so the rule library can't regress.
# ---------------------------------------------------------------------------
def main(argv: list[str] | None = None) -> int:
    import sys

    argv = sys.argv[1:] if argv is None else argv
    trials = int(argv[0]) if argv else 800
    audits = audit_catalogue(trials=trials)

    unsound = [a for a in audits if not a.sound]
    weak_guards = [a for a in audits if a.sound and a.guard_necessary is False]

    print(f"Rule-library soundness audit  ({trials} random trials/rule, "
          f"exact rational arithmetic)\n" + "-" * 68)
    for a in audits:
        if not a.sound:
            wit = ", ".join(f"{k}={v}" for k, v in a.counterexample.items())
            print(f"  UNSOUND   {a.rule_id:<24} counterexample: {wit}")
        else:
            note = ""
            if a.guard_necessary is True:
                note = "guard load-bearing"
            elif a.guard_necessary is False:
                note = "guard never needed (suspicious)"
            print(f"  ok        {a.rule_id:<24} {note}")
    print("-" * 68)

    if unsound:
        print(f"FAIL: {len(unsound)} unsound rule(s): "
              f"{', '.join(a.rule_id for a in unsound)}")
        return 1
    if weak_guards:
        # a guard that never changes the outcome is dead weight, not unsafe;
        # warn but don't fail the build.
        print(f"WARN: {len(weak_guards)} rule(s) with a guard that never fires: "
              f"{', '.join(a.rule_id for a in weak_guards)}")
    print(f"PASS: all {len(audits)} rules sound.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
