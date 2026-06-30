#!/usr/bin/env python3
"""Live Coq check: prove the *emitted* induction proofs actually kernel-check.

`coq_induction.build_source` generates a Coq `induction n` proof for a goal; this
feeds a curated set through a real Rocq/Coq toolchain (`coq_prover.check_source`)
and asserts the MUST_PASS ones compile. It closes the gap unit tests can't: that
the translation produces genuinely kernel-checkable Coq, not just plausible text.

    python check_induction.py               # skips cleanly if Coq is absent
    python check_induction.py --require-coq # CI: fail if Coq is unavailable

Needs `coqc` (or `rocq`) on PATH; nothing else (standard library only).
"""
from __future__ import annotations

import argparse
import sys

import coq_induction
import coq_prover


# ---- MathNode builders (the protocol JSON shape; stdlib-only) ---------------
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
# All verified against Rocq 9.1.1 (QArith, stdlib only).
MUST_PASS = [
    ("1^n = 1", ex(eq(powr(num(1), vr("n")), num(1)))),
    ("a^(m+n) = a^m * a^n",
     ex(eq(powr(vr("a"), add(vr("m"), vr("n"))), mul(powr(vr("a"), vr("m")), powr(vr("a"), vr("n")))))),
    ("a^n * b^n = (a*b)^n",
     ex(eq(mul(powr(vr("a"), vr("n")), powr(vr("b"), vr("n"))), powr(mul(vr("a"), vr("b")), vr("n"))))),
    # IH-free / reflexive: the succ case closes by `ring` alone — guards that the
    # base/step tactic block does not depend on the IH being usable.
    ("2^n = 2^n", ex(eq(powr(num(2), vr("n")), powr(num(2), vr("n"))))),
]
# Exploratory — logged, never fatal (promote to MUST_PASS once confirmed in CI).
BEST_EFFORT: list = []


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--require-coq", action="store_true",
                    help="fail if the Coq toolchain is unavailable (CI)")
    args = ap.parse_args()

    if not coq_prover.coq_available():
        if args.require_coq:
            print("FAIL: --require-coq but no Coq toolchain (coqc/rocq not on PATH)")
            return 1
        print("skipped: no Coq toolchain (install coq/rocq, e.g. `brew install coq`)")
        return 0

    failed = False
    print("MUST PASS:")
    for name, e in MUST_PASS:
        res = coq_induction.certify(e)
        print(f"  {'ok  ' if res.certified else 'FAIL'} {name}"
              + ("" if res.certified else f"\n      {res.detail.strip()[:600]}"))
        failed |= not res.certified
    print("BEST EFFORT (non-fatal):")
    for name, e in BEST_EFFORT:
        res = coq_induction.certify(e)
        print(f"  {'ok  ' if res.certified else '--  '} {name}"
              + ("" if res.certified else f"  ({res.method})"))

    print("\n" + ("induction proofs kernel-check" if not failed else "a MUST-PASS proof did not compile"))
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
