#!/usr/bin/env python3
"""Live cvc5 check: prove the *emitted* induction goals actually settle in cvc5.

`cvc5_induction.build_*_source` generates SMT-LIB for an induction goal; this feeds
a curated set through a real cvc5 binary (`cvc5_prover`) and asserts the MUST_PASS
ones get the expected verdict. It closes the gap unit tests can't: that the
translation produces genuinely solvable SMT, not just plausible-looking text.

    python check_induction.py                # skips cleanly if cvc5 is absent
    python check_induction.py --require-cvc5 # CI: fail if cvc5 is unavailable

Point it at a cvc5 binary via CVC5REGATE_CVC5 (or have `cvc5` on PATH).

The MUST_PASS set deliberately includes goals **outside leanregate's Lean emitter
fragment** — a divisibility goal (`3 ∣ n³−n`), an inequality (`2ⁿ ≥ 1`), and a
recursive-sum equality (`2·Σi = n(n+1)`) — to demonstrate the coverage cvc5 adds,
plus the equality `1ⁿ = 1` that leanregate also proves, and a disproof
(`2ⁿ = n+1` is false) yielding a concrete numeric witness.
"""
from __future__ import annotations

import argparse
import sys

import cvc5_induction
import cvc5_prover


# ---- MathNode builders (the protocol JSON shape; stdlib-only) ----
def num(v): return {"type": "number", "value": str(v)}
def vr(v): return {"type": "variable", "value": v}
def wd(v): return {"type": "wild", "value": v}
def b(t, l, r): return {"type": t, "slots": {"left": [l], "right": [r]}}
def mul(l, r): return b("mul", l, r)
def add(l, r): return b("add", l, r)
def sub(l, r): return b("sub", l, r)
def eq(l, r): return b("eq", l, r)
def ge(l, r): return b("ge", l, r)
def gt(l, r): return b("gt", l, r)
def succ(x): return {"type": "succ", "slots": {"inner": [x]}}
def powr(ba, e): return {"type": "pow", "slots": {"base": [ba], "exponent": [e]}}
def app(name, *args): return {"type": "apply", "value": name, "slots": {"args": list(args)}}
def divides(d, v): return {"type": "divides", "slots": {"divisor": [num(d)], "value": [v]}}
def rule(rid, lhs, rhs): return {"id": rid, "lhs": lhs, "rhs": rhs, "bidirectional": False, "conditions": []}


# Standard ℕ-recursive exponentiation (supplied as the request would carry it).
POW = [rule("pow_zero", powr(wd("a"), num(0)), num(1)),
       rule("pow_succ", powr(wd("a"), succ(wd("k"))), mul(wd("a"), powr(wd("a"), wd("k"))))]
# A recursive sum  Σ_{i=0}^{k} i  : sum(0)=0, sum(S k)=(S k)+sum(k).
SUM = [rule("sum_zero", app("sum", num(0)), num(0)),
       rule("sum_succ", app("sum", succ(wd("k"))), add(succ(wd("k")), app("sum", wd("k"))))]


def ind(goal, defs=POW, domain=None):
    ex = {"mode": "induction", "goal": goal, "inductionVar": "n", "definitions": defs}
    if domain:
        ex["domain"] = domain
    return ex


# (name, request, expected outcome). All verified on cvc5 1.3.4.
MUST_PASS = [
    # Shared with leanregate (equality over pow): the baseline.
    ("1^n = 1", ind(eq(powr(num(1), vr("n")), num(1))), "proven_equal"),
    # OUTSIDE leanregate's emitter — the coverage win:
    ("3 | n^3 - n  (divisibility)",
     ind(divides(3, sub(mul(vr("n"), mul(vr("n"), vr("n"))), vr("n"))), defs=[], domain="int"),
     "proven_equal"),
    ("2^n >= 1  (inequality)",
     ind(ge(powr(num(2), vr("n")), num(1)), domain="int"), "proven_equal"),
    ("2*sum(i) = n*(n+1)  (recursive sum)",
     ind(eq(mul(num(2), app("sum", vr("n"))), mul(vr("n"), add(vr("n"), num(1)))),
         defs=SUM, domain="int"), "proven_equal"),
    # Disproof with a numeric witness (2^n = n+1 fails at n=2):
    ("2^n = n+1  (false -> witness)",
     ind(eq(powr(num(2), vr("n")), add(vr("n"), num(1))), domain="int"), "proven_unequal"),
]

# Translated correctly but cvc5's automation may time out (documented limits):
# two-variable equality and a strengthening-needing inequality. Logged, never fatal.
BEST_EFFORT = [
    ("a^(m+n) = a^m * a^n",
     ind(eq(powr(vr("a"), add(vr("m"), vr("n"))), mul(powr(vr("a"), vr("m")), powr(vr("a"), vr("n")))))),
    ("2^n > n", ind(gt(powr(num(2), vr("n")), vr("n")), domain="int")),
]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--require-cvc5", action="store_true",
                    help="fail if the cvc5 toolchain is unavailable (CI)")
    args = ap.parse_args()

    if not cvc5_prover.cvc5_available():
        if args.require_cvc5:
            print(f"FAIL: --require-cvc5 but no cvc5 binary (CVC5REGATE_CVC5={cvc5_prover.CVC5!r})")
            return 1
        print("skipped: no cvc5 toolchain (set CVC5REGATE_CVC5 or put cvc5 on PATH)")
        return 0

    failed = False
    print(f"cvc5 + Carcara availability: cvc5={cvc5_prover.cvc5_available()} "
          f"carcara={cvc5_prover.carcara_available()}")
    print("MUST PASS:")
    for name, ex, expect in MUST_PASS:
        res = cvc5_induction.certify(ex)
        ok = res.outcome == expect
        extra = f" witness={res.witness}" if res.witness else ""
        print(f"  {'ok  ' if ok else 'FAIL'} {name}  -> {res.outcome} "
              f"(certified={res.certified}, method={res.method}){extra}"
              + ("" if ok else f"\n      expected {expect}; detail: {res.detail[:300]}"))
        failed |= not ok
    print("BEST EFFORT (non-fatal):")
    for name, ex in BEST_EFFORT:
        res = cvc5_induction.certify(ex)
        good = res.outcome in ("proven_equal", "proven_unequal")
        print(f"  {'ok  ' if good else '--  '} {name}  -> {res.outcome} ({res.method})")

    print("\n" + ("emitted induction goals settle in cvc5"
                  if not failed else "a MUST-PASS goal did not get its expected verdict"))
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
