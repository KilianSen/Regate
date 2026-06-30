from __future__ import annotations

import time
from dataclasses import replace

from eggregate.backend import equivalent
from eggregate.catalogue import CATALOGUE, rules
from eggregate.hints import shortest_path
from eggregate.model import add, frac, mul, num, var
from eggregate.proof_egraph import ProofEGraph, directed_rules, egg_prove
from eggregate.semantics import find_counterexample

x = var("x")


def _nodes(t):
    return 1 + sum(_nodes(c) for c in t.kids)


def _t(f):
    t0 = time.perf_counter()
    try:
        return f(), time.perf_counter() - t0
    except Exception:
        return None, time.perf_counter() - t0


def bench_a_depth():
    print("A. DEPTH/SIZE on a benign ladder  ((..(x+0)+0..)+0) == x, single rule")
    print(f"{'k':>4}{'nodes':>7}{'bfs(s)':>9}{'egg(s)':>9}{'oracle(s)':>10}{'disprove(s)':>12}")
    one = rules("add_zero_right")
    for k in [1, 2, 4, 8, 16, 32, 64, 128]:
        t = x
        for _ in range(k):
            t = add(t, num(0))
        _, bt = _t(lambda: shortest_path(t, x, one, max_depth=k + 2))
        _, et = _t(lambda: egg_prove(t, x, one, bound=k + 2))
        _, ot = _t(lambda: equivalent(t, x, rules=one, bound=k + 2))
        _, dt = _t(lambda: find_counterexample(t, x))
        print(f"{k:>4}{_nodes(t):>7}{bt:>9.3f}{et:>9.3f}{ot:>10.3f}{dt:>12.4f}")
        if max(bt, et, ot) > 5:
            break


def bench_b_explosion():
    print("\nB. RAW SATURATION growth under FULL catalogue (no early-stop)")
    print(f"{'term':>16}{'iters':>7}{'e-nodes':>9}{'time(s)':>9}")
    dr = directed_rules(CATALOGUE)

    def prod_of_sums(m):
        t = add(var("a0"), var("a1"))
        for i in range(1, m):
            t = mul(t, add(var(f"b{i}0"), var(f"b{i}1")))
        return t

    for label, m in [("1 factor", 1), ("2 factors", 2), ("3 factors", 3)]:
        for b in [2, 4, 6, 8]:
            eg = ProofEGraph()
            eg.add_term(prod_of_sums(m))
            _, dt = _t(lambda: eg.saturate(dr, b))
            print(f"{label:>16}{b:>7}{len(eg.nodes):>9}{dt:>9.3f}")
            if dt > 5:
                print(f"{'':>16}{'(stop: >5s)':>16}")
                break
        print()


def bench_c_rules():
    print("C. COST vs RULE COUNT (duplicated catalogue, fixed term, 3 iters)")
    print(f"{'R':>6}{'directed':>10}{'time(s)':>9}")
    term = frac(mul(num(3), add(x, num(0))), mul(num(3), num(1)))
    for mult in [1, 2, 4, 8, 16]:
        rs = []
        for i in range(mult):
            rs += [replace(r, id=f"{r.id}__{i}") for r in CATALOGUE]
        dr = directed_rules(rs)
        eg = ProofEGraph()
        eg.add_term(term)
        _, dt = _t(lambda: eg.saturate(dr, 3))
        print(f"{len(rs):>6}{len(dr):>10}{dt:>9.3f}")


if __name__ == "__main__":
    bench_a_depth()
    bench_b_explosion()
    bench_c_rules()
