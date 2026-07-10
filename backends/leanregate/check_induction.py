#!/usr/bin/env python3
from __future__ import annotations

import argparse
import sys

import lean_induction
import lean_prover


# ---- MathNode builders (the protocol JSON shape; stdlib-only, no eggregate) ----
def num(v): return {"type": "number", "value": str(v)}
def vr(v): return {"type": "variable", "value": v}
def wd(v): return {"type": "wild", "value": v}
def b(t, l, r): return {"type": t, "slots": {"left": [l], "right": [r]}}
def mul(l, r): return b("mul", l, r)
def add(l, r): return b("add", l, r)
def eq(l, r): return b("eq", l, r)
def succ(x): return {"type": "succ", "slots": {"inner": [x]}}
def powr(base, exp): return {"type": "pow", "slots": {"base": [base], "exponent": [exp]}}
def rule(rid, lhs, rhs): return {"id": rid, "lhs": lhs, "rhs": rhs, "bidirectional": False, "conditions": []}

# Standard ℕ-recursive definition of exponentiation, supplied as the request would.
DEFS = [rule("pow_zero", powr(wd("a"), num(0)), num(1)),
        rule("pow_succ", powr(wd("a"), succ(wd("n"))), mul(wd("a"), powr(wd("a"), wd("n"))))]


def ex(goal):
    return {"mode": "induction", "goal": goal, "inductionVar": "n", "definitions": DEFS}


# Goals whose emitted proof MUST kernel-check (CI fails otherwise).
# All three verified against Lean 4.15 + Mathlib.
MUST_PASS = [
    ("1^n = 1", ex(eq(powr(num(1), vr("n")), num(1)))),
    ("a^(m+n) = a^m * a^n",
     ex(eq(powr(vr("a"), add(vr("m"), vr("n"))), mul(powr(vr("a"), vr("m")), powr(vr("a"), vr("n")))))),
    ("a^n * b^n = (a*b)^n",
     ex(eq(mul(powr(vr("a"), vr("n")), powr(vr("b"), vr("n"))), powr(mul(vr("a"), vr("b")), vr("n"))))),
    # IH-free / reflexive: the succ case closes by `simp` alone — guards the
    # `all_goals` wrapper (without it the trailing tactic errors "no goals").
    ("2^n = 2^n", ex(eq(powr(num(2), vr("n")), powr(num(2), vr("n"))))),
]
# Exploratory — logged, never fatal (promote to MUST_PASS once confirmed in CI).
BEST_EFFORT: list = []


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--require-lean", action="store_true",
                    help="fail if the Lean toolchain is unavailable (CI)")
    args = ap.parse_args()

    if not lean_prover.lean_available():
        if args.require_lean:
            print("FAIL: --require-lean but no Lean toolchain "
                  f"(LEANREGATE_LEAN_PROJECT={lean_prover.LEAN_PROJECT!r}, lake on PATH? no)")
            return 1
        print("skipped: no Lean toolchain (set LEANREGATE_LEAN_PROJECT to a built lake project)")
        return 0

    failed = False
    print("MUST PASS:")
    for name, e in MUST_PASS:
        res = lean_induction.certify(e)
        print(f"  {'ok  ' if res.certified else 'FAIL'} {name}"
              + ("" if res.certified else f"\n      {res.detail.strip()[:600]}"))
        failed |= not res.certified
    print("BEST EFFORT (non-fatal):")
    for name, e in BEST_EFFORT:
        res = lean_induction.certify(e)
        print(f"  {'ok  ' if res.certified else '--  '} {name}"
              + ("" if res.certified else f"  ({res.method})"))

    print("\n" + ("induction proofs kernel-check" if not failed else "a MUST-PASS proof did not compile"))
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
