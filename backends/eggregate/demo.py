from __future__ import annotations

from eggregate import (
    add, all_shortest_paths, distance, frac, grade, greedy_hints, mul, num,
    pretty, rules, shortest_path, var, equivalent,
)
from eggregate.model import Path


def fmt_path(p: Path) -> str:
    return "[" + ", ".join(map(str, p)) + "]" if p else "[ ]"


def rule(line=""):
    print(line)


# -- the exercise -----------------------------------------------------------
x = var("x")
source = frac(mul(num(3), add(var("x"), num(0))), mul(num(3), num(1)))
target = x
AVAILABLE = rules(
    "add_zero_right", "frac_mul_cancel_left", "frac_one_denom", "mul_one_right"
)

rule("=" * 70)
rule("  Eggregate -- MS3 e-graph backend, worked example")
rule("=" * 70)
rule(f"  source : {pretty(source)}")
rule(f"  target : {pretty(target)}")
rule(f"  rules  : {', '.join(r.id for r in AVAILABLE)}")

# -- 1. Equivalence grading is path-independent -----------------------------
rule()
rule("1) EQUIVALENCE GRADING (path-independent)")
rule("-" * 70)

# The reference three-step derivation.
reference_chain = [
    ("add_zero_right",       [1, 1], frac(mul(num(3), var("x")), mul(num(3), num(1)))),
    ("frac_mul_cancel_left", [],     frac(var("x"), num(1))),
    ("frac_one_denom",       [],     var("x")),
]
# An ALTERNATIVE valid derivation a student might submit (cancel first).
alt_chain = [
    ("frac_mul_cancel_left", [],     frac(add(var("x"), num(0)), num(1))),
    ("add_zero_right",       [1],    frac(var("x"), num(1))),
    ("frac_one_denom",       [],     var("x")),
]

for label, chain in [("reference derivation", reference_chain), ("alternative derivation", alt_chain)]:
    final = chain[-1][2]
    g = grade(final, target, rules=AVAILABLE)
    rule(f"  {label:<22} ends at {pretty(final):<6} -> grade {g}")
rule("  (RewriteChainGrader would only accept a chain it can replay; the")
rule("   e-graph grader accepts both, because both endpoints share an e-class.)")

# A wrong answer and a not-yet-finished answer.
rule()
wrong = add(var("x"), num(1))
partial = frac(var("x"), num(1))
rule(f"  wrong final     {pretty(wrong):<6} -> grade {grade(wrong, target, rules=AVAILABLE)}")
rule(f"  unfinished      {pretty(partial):<6} -> grade {grade(partial, target, rules=AVAILABLE)}"
     f"   (equivalent to x/1, not yet x)")

# -- 2. The replay trace with the real distance metric ----------------------
rule()
rule("2) REPLAY TRACE with MathNodeDistance to x")
rule("-" * 70)
rule(f"  {'after step':<12}{'state':<20}{'distance':<10}{'partial credit'}")
d0 = distance(source, target)
states = [("—", source)] + [(rid, st) for rid, _, st in reference_chain]
for i, (rid, st) in enumerate(states):
    d = distance(st, target)
    pc = 100 if d == 0 else max(0, min(99, int((1 - d / d0) * 100)))
    label = "(source)" if rid == "—" else str(i - 1)
    rule(f"  {label:<12}{pretty(st):<20}{d:<10}{pc}")

# -- 3. Greedy one-ply hints vs. the MS3 whole-path hint --------------------
rule()
rule("3) HINTS: greedy one-ply vs. MS3 whole-path")
rule("-" * 70)
rule("  Greedy one-ply ranking at the source (what suggestHints returns today):")
for i, app in enumerate(greedy_hints(source, target, AVAILABLE, k=3), 1):
    res = app.result
    rule(f"    {i}. {app.rule_id:<22} at {fmt_path(app.path):<7} "
         f"-> {pretty(res)}   (distance {distance(res, target)})")
rule("  -> ranks 'cancel' first because it removes the most structure in one move,")
rule("     even though a tutor might teach 'clear the +0 first'.")

rule()
plans = all_shortest_paths(source, target, AVAILABLE)
rule(f"  MS3 whole-path: {len(plans)} minimal {len(plans[0])}-step plans reach x. The hinter")
rule("  can pick a pedagogically natural one -- here, clearing the +0 first:")
# Prefer the plan whose first step is add_zero_right ("clear the +0 first").
plan = next((p for p in plans if p[0].rule_id == "add_zero_right"), plans[0])
for i, step in enumerate(plan):
    rule(f"    step {i}: {step.rule_id:<22} at {fmt_path(step.path):<7} -> {pretty(step.state)}")
rule("  -> a full route is available, so guidance can be ordered pedagogically")
rule("     and ranked by progress-to-goal rather than a single greedy move.")

rule()
rule("=" * 70)
rule("  All grades and distances above are computed, not illustrative.")
rule("=" * 70)
