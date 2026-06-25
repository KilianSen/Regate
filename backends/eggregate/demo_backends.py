"""Two proving backends, side by side.

  bfs  -- minimal-chain search over forward rule applications (hints.shortest_path)
  egg  -- saturate a proof-producing e-graph, read the proof off provenance
          (proof_egraph.egg_prove), the way egg's explain_equivalence works.

Run:  .venv/bin/python demo_backends.py
"""
from __future__ import annotations

from eggregate import add, compare, frac, mul, neg, num, print_comparison, rules, sub, var
from eggregate.catalogue import CATALOGUE

x, y = var("x"), var("y")
WORKED = rules("add_zero_right", "frac_mul_cancel_left", "frac_one_denom", "mul_one_right")

CASES = [
    ("worked example (both agree, minimal)",
     frac(mul(num(3), add(x, num(0))), mul(num(3), num(1))), x, WORKED),
    ("double negation",            neg(neg(x)), x, CATALOGUE),
    ("subtraction as add-negate",  sub(x, y), add(x, neg(y)), CATALOGUE),
    ("cancel a literal fraction",  frac(num(6), num(6)), num(1), CATALOGUE),
    ("symmetric goal: x == x+0 (only egg, forward BFS can't go uphill)",
     x, add(x, num(0)), CATALOGUE),
]

print("=" * 72)
print("  Two proving backends: bfs (minimal search) vs egg (saturate + prove)")
print("=" * 72)
for title, s, t, rs in CASES:
    print(f"\n# {title}")
    print_comparison(compare(s, t, rs))

print("\n" + "=" * 72)
print("  egg proves equalities forward BFS can't reach (symmetric / congruence),")
print("  but its proofs are not guaranteed minimal; BFS's are. Use both.")
print("=" * 72)
