#!/usr/bin/env python3
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

# ---------------------------------------------------------------------------
# `apply` — n-ary named function application (protocol 1.1). A function arrives as
# DATA: an `apply` node plus a base rule (matching `0`) and a step rule (matching
# `S k`), which coqregate emits as a Coq `Fixpoint`. Both goals below kernel-check
# on Coq 8.20.1, so they are MUST_PASS: they pin that the emitted `{struct n}`
# Fixpoint is accepted by the termination checker, and that `revert`+`cbn [f …]`
# lets `ring` close a step whose IH is applied at a shifted accumulator.
# ---------------------------------------------------------------------------
def ap(f, *args): return {"type": "apply", "value": f, "slots": {"args": list(args)}}


# Two names for the same recursion: provable with the IH at `n` itself.
TWIN_DEFS = [rule("p_zero", ap("p", num(0)), num(1)),
             rule("p_succ", ap("p", succ(wd("k"))), mul(num(2), ap("p", wd("k")))),
             rule("q_zero", ap("q", num(0)), num(1)),
             rule("q_succ", ap("q", succ(wd("k"))), mul(num(2), ap("q", wd("k"))))]

# An ACCUMULATOR function: the step needs the IH at the shifted accumulator
# `x·(S k)`, which is why the emitted proof reverts the ℚ binders before inducting.
FACT_DEFS = [rule("factaux_zero", ap("fact_aux", wd("x"), num(0)), wd("x")),
             rule("factaux_succ", ap("fact_aux", wd("x"), succ(wd("k"))),
                  ap("fact_aux", mul(wd("x"), succ(wd("k"))), wd("k"))),
             rule("fact_zero", ap("fact", num(0)), num(1)),
             rule("fact_succ", ap("fact", succ(wd("k"))),
                  mul(succ(wd("k")), ap("fact", wd("k"))))]

# Defined after the `ap`/DEFS helpers, so appended rather than listed above.
MUST_PASS += [
    ("apply: p n = q n (twin recursive functions)",
     {"mode": "induction", "goal": eq(ap("p", vr("n")), ap("q", vr("n"))),
      "inductionVar": "n", "definitions": TWIN_DEFS}),
    ("apply: fact_aux x n = x * fact n (generalized IH)",
     {"mode": "induction", "goal": eq(ap("fact_aux", vr("x"), vr("n")),
                                      mul(vr("x"), ap("fact", vr("n")))),
      "inductionVar": "n", "definitions": FACT_DEFS}),
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
