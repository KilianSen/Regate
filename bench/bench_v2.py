#!/usr/bin/env python3
"""
Second-round measurements, with the methodology tightened.

Methodology (applies to every number this script prints):
  * n >= 5 repetitions everywhere, and n = 10 wherever the median lands under 1 s — a
    sub-second figure is where scheduling jitter is proportionally largest, and two runs
    (the previous Tables 14/15) do not support the word "median" at all.
  * Every cell reports median AND min-max, never a bare mean. The spread is the point:
    it is what tells the reader whether the median is meaningful.
  * Cold/nonce discipline is preserved from the earlier harnesses. In-process e-graph
    measurements build a FRESH ProofEGraph per repetition (no cross-rep memoisation), and
    HTTP measurements vary a per-run nonce so no backend can serve a cached verdict.

Measurements:
  1. eggregate rule-count sweep extended past R = 1000 (to R = 10 000), so the "round-trip
     overhead below 1 %" caption is actually true of every row.
  2. leanregate at R = 8 and R = 10 — REQUIRES a leanregate backend; skipped with a loud
     notice when absent rather than extrapolated.
  3. The full saturation grid, all cells, with an explicit cutoff and iterations-to-fixpoint.
  4. The abstention matrix: every conformance fixture through every backend.

  python3 bench_v2.py [1] [2] [3] [4]      # default: all runnable
"""
from __future__ import annotations

import json
import os
import statistics
import subprocess
import sys
import time
from dataclasses import replace

REGATE = os.environ.get("REGATE_PATH", "/home/user/projects/ba/Regate")
sys.path.insert(0, os.path.join(REGATE, "backends", "eggregate"))

# The saturation cutoff. The committed bench.py used `if dt > 5: break`, which cannot have
# produced the 33 s row reported in the thesis — so the value actually used has to be stated.
# This one is stated, and printed in the table header.
CUTOFF_S = float(os.environ.get("BENCH_CUTOFF_S", "60"))

RESULTS: dict = {"cutoff_s": CUTOFF_S}


# ── methodology helpers ──────────────────────────────────────────────────────
def stat(samples: list[float]) -> dict:
    """median + min-max over the raw samples, with n carried so the table can show it."""
    return {
        "n": len(samples),
        "median": statistics.median(samples),
        "min": min(samples),
        "max": max(samples),
        "samples": [round(s, 6) for s in samples],
    }


def measure(fn, min_reps: int = 5, sub_second_reps: int = 10, cap_s: float | None = None) -> dict:
    """Run `fn` at least `min_reps` times; if the median is sub-second, top up to
    `sub_second_reps`. Returns stat(). `cap_s` abandons a cell that is too slow to repeat."""
    samples: list[float] = []
    for i in range(min_reps):
        t0 = time.perf_counter()
        fn()
        samples.append(time.perf_counter() - t0)
        if cap_s is not None and samples[-1] > cap_s:
            return {**stat(samples), "capped": True}
    if statistics.median(samples) < 1.0:
        for _ in range(sub_second_reps - min_reps):
            t0 = time.perf_counter()
            fn()
            samples.append(time.perf_counter() - t0)
    return stat(samples)


def fmt(s: dict, unit: str = "ms") -> str:
    k = 1000.0 if unit == "ms" else 1.0
    return f"{s['median'] * k:>9.1f}  [{s['min'] * k:>8.1f}–{s['max'] * k:>8.1f}]  n={s['n']:<3}"


# ── 1. rule-count sweep, extended past R = 1000 ──────────────────────────────
def m1_rule_sweep():
    from eggregate.catalogue import CATALOGUE
    from eggregate.model import add, frac, mul, num, var
    from eggregate.proof_egraph import ProofEGraph, directed_rules

    x = var("x")
    term = frac(mul(num(3), add(x, num(0))), mul(num(3), num(1)))
    base = len(CATALOGUE)

    print(f"\n=== 1. COST vs RULE COUNT (fixed term, saturate bound 3; catalogue = {base} rules) ===")
    print("Extends the sweep past R = 1000 so that every row really does sit below the 1 % "
          "round-trip-overhead\nthreshold the caption claims. t/R is the per-rule cost the sweep converges to.")
    print(f"\n{'R':>7}{'directed':>10}{'median (ms)':>14}{'min–max (ms)':>26}{'n':>5}{'t/R (µs)':>11}")

    targets = [29, 58, 116, 232, 464, 1000, 3000, 10000]
    rows = []
    for target in targets:
        mult = max(1, round(target / base))
        rs = []
        for i in range(mult):
            rs += [replace(r, id=f"{r.id}__{i}") for r in CATALOGUE]
        dr = directed_rules(rs)
        R = len(rs)

        def once(dr=dr):
            eg = ProofEGraph()          # fresh per repetition — no cross-rep reuse
            eg.add_term(term)
            eg.saturate(dr, 3)

        s = measure(once, cap_s=30)
        per_rule = s["median"] / R * 1e6
        rows.append({"R": R, "directed": len(dr), **s, "per_rule_us": per_rule})
        print(f"{R:>7}{len(dr):>10}{s['median']*1000:>14.1f}"
              f"{f'{s['min']*1000:.1f} – {s['max']*1000:.1f}':>26}{s['n']:>5}{per_rule:>11.1f}")
    RESULTS["m1_rule_sweep"] = rows

    slowest = max(rows, key=lambda r: r["median"])
    print(f"\n  slowest row: R={slowest['R']} at {slowest['median']*1000:.0f} ms — a ~1.4 ms HTTP "
          f"round trip is {1.4/(slowest['median']*1000)*100:.2f} % of it.")


# ── 2. leanregate at R = 8 / R = 10 ──────────────────────────────────────────
LEAN_DIR = os.path.join(REGATE, "backends", "leanregate")


def _lean_env():
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    env["LEANREGATE_LEAN_PROJECT"] = LEAN_DIR
    return env


def m2_lean():
    """Measure leanregate DIRECTLY at R = 8 and R = 10 instead of extrapolating a fit over
    R ∈ {1,2,3,5}. R = 1 is remeasured with proper repetitions too: the previous two runs there
    differed by ~0.8 s, which is exactly what made the fitted intercept soft.

    Every rule is statement-unique per repetition (a nonce in the wildcard name), so the Lean rule
    cache cannot serve a warm proof — this measures cold proving, which is the cost that scales."""
    print("\n=== 2. LEANREGATE cost vs RULE COUNT, measured not fitted ===")

    probe = subprocess.run(
        [sys.executable, "-c",
         "import sys; sys.path.insert(0,'.'); import lean_prover as lp; print(lp.lean_available())"],
        capture_output=True, text=True, cwd=LEAN_DIR, env=_lean_env(), timeout=120)
    if "True" not in probe.stdout:
        print(f"  SKIPPED — lean_available() is False in {LEAN_DIR}. stdout={probe.stdout.strip()[:120]}")
        RESULTS["m2_lean"] = {"skipped": "lean_available False"}
        return
    print(f"  local toolchain OK (elan + prebuilt Mathlib in {LEAN_DIR}/.lake)")
    print(f"\n{'R':>4}{'median (s)':>13}{'min–max (s)':>24}{'n':>5}{'s/rule':>10}  outcome")

    def payload(R, nonce):
        rules, first = [], None
        for k in range(1, R + 1):
            rid = f"r_{nonce}_{k}"
            first = first or rid
            lhs = {"type": "wild", "value": f"a_{nonce}_{k}"}
            for _ in range(k):
                lhs = {"type": "add", "slots": {"left": [lhs], "right": [{"type": "number", "value": "0"}]}}
            rules.append({"id": rid, "owner": "add", "lhs": lhs,
                          "rhs": {"type": "wild", "value": f"a_{nonce}_{k}"},
                          "bidirectional": False, "conditions": []})
        v = {"type": "variable", "value": f"v{nonce}"}
        src = {"type": "add", "slots": {"left": [v], "right": [{"type": "number", "value": "0"}]}}
        return {"protocol": "1.0",
                "exercise": {"mode": "transformation", "source": src, "target": v, "ruleset": rules},
                "submission": {"steps": [{"kind": "A", "rule": first, "path": [], "direction": "forward"}]}}

    rows = []
    for R in [1, 8, 10]:
        seen = {}
        counter = [0]

        def once(R=R, seen=seen, counter=counter):
            counter[0] += 1
            nonce = f"{R}x{counter[0]}x{int(time.time()*1000) % 100000}"
            p = subprocess.run([sys.executable, os.path.join(LEAN_DIR, "grade.py"), "--cli"],
                               input=json.dumps(payload(R, nonce)), capture_output=True, text=True,
                               cwd=LEAN_DIR, env=_lean_env(), timeout=1800)
            try:
                seen["outcome"] = json.loads(p.stdout.strip().splitlines()[-1]).get("outcome")
            except Exception:
                seen["outcome"] = "parse-error"

        s = measure(once, min_reps=5, cap_s=1800)
        rows.append({"R": R, **s, "outcome": seen.get("outcome")})
        print(f"{R:>4}{s['median']:>13.2f}{f'{s["min"]:.2f} – {s["max"]:.2f}':>24}{s['n']:>5}"
              f"{s['median']/R:>10.2f}  {seen.get('outcome')}")

    RESULTS["m2_lean"] = rows
    if len(rows) >= 2:
        r1 = next((r for r in rows if r["R"] == 1), None)
        r10 = next((r for r in rows if r["R"] == 10), None)
        if r1 and r10:
            print(f"\n  R=1 spread is {r1['max']-r1['min']:.2f} s over n={r1['n']} — the soft intercept, now bounded.")
            print(f"  R=10 measured at {r10['median']:.1f} s (median). No extrapolation needed.")


# ── 3. the whole saturation grid ─────────────────────────────────────────────
def m3_saturation_grid():
    from eggregate.catalogue import CATALOGUE
    from eggregate.model import add, mul, var
    from eggregate.proof_egraph import ProofEGraph, directed_rules

    dr = directed_rules(CATALOGUE)
    MAX_NODES = 60_000          # ProofEGraph.saturate's own hard resource bound

    def prod_of_sums(m):
        t = add(var("a0"), var("a1"))
        for i in range(1, m):
            t = mul(t, add(var(f"b{i}0"), var(f"b{i}1")))
        return t

    print(f"\n=== 3. SATURATION GRID, all cells (full catalogue, cutoff = {CUTOFF_S:g} s) ===")
    print("Every cell of m ∈ {1,2,3,4} × bound ∈ {2,4,6,8} is reported, including cells that hit a")
    print("limit — previously only three were published. Convergence is a property of the TERM, not of")
    print("an individual capped run, so it is reported once per m below the block and never as a column")
    print("on a row whose own bound is smaller than the fixpoint. `saturate` now returns its stop reason,")
    print("so a fixpoint is claimed only when a round fired nothing off a COMPLETE match set: a run whose")
    print("match collection was truncated reports `starved`, which looks identical in the node counts")
    print(f"but is not convergence. `nodes` is that cell's e-node count; the cap is max_nodes={MAX_NODES},")
    print("which also bounds matches collected per round.")
    print(f"\n{'m':>3}{'bound':>7}{'e-nodes':>10}{'median (ms)':>14}{'min–max (ms)':>26}{'n':>5}  status")

    rows, summaries = [], []
    for m in [1, 2, 3, 4]:
        term = prod_of_sums(m)

        # Untimed probe sweep over bounds 1..8. The stop reason — not the node count — decides
        # whether the term converged: equal counts on consecutive bounds happen just as readily
        # when the match budget starved the round.
        counts, recs, probe_times, aborted = {}, {}, {}, None
        for b in range(1, 9):
            eg = ProofEGraph()
            eg.add_term(term)
            t0 = time.perf_counter()
            try:
                recs[b] = eg.saturate(dr, b)
            except Exception as e:                       # noqa: BLE001
                aborted = f"{type(e).__name__}: {str(e)[:40]}"
                break
            probe_times[b] = time.perf_counter() - t0
            counts[b] = len(eg.nodes)
            if probe_times[b] > CUTOFF_S:
                aborted = f"cutoff >{CUTOFF_S:g}s at bound {b}"
                break

        # The first bound whose run genuinely converged; `rounds - 1` iterations sufficed, since
        # the final round is the one that fired nothing.
        fixpoint = None
        for b in sorted(recs):
            if recs[b]["stop"] == "fixpoint":
                fixpoint = recs[b]["rounds"] - 1
                break
        truncated_from = next((b for b in sorted(recs) if recs[b]["truncated"]), None)
        node_capped = any(r["stop"] == "node_cap" for r in recs.values())

        for b in [2, 4, 6, 8]:
            if b not in counts:
                rows.append({"m": m, "bound": b, "unmeasured": aborted})
                print(f"{m:>3}{b:>7}{'-':>10}{'-':>14}{'-':>26}{'-':>5}  NOT REACHED ({aborted})")
                continue

            def once(term=term, b=b):
                eg = ProofEGraph()
                eg.add_term(term)
                eg.saturate(dr, b)

            s = measure(once, cap_s=CUTOFF_S)
            # Per-ROW status describes only this run: did it converge, or was it cut short, and by
            # what. It never repeats the term's fixpoint — that belongs to the block summary.
            stop = recs[b]["stop"]
            status = {"fixpoint": "converged", "starved": "starved (match budget)",
                      "node_cap": "node-capped", "bound": "bound-limited",
                      "connected": "connected"}[stop]
            if recs[b]["truncated"] and stop != "starved":
                status += ", matches truncated"
            rows.append({"m": m, "bound": b, "nodes": counts[b], "stop": stop,
                         "truncated": recs[b]["truncated"], **s})
            print(f"{m:>3}{b:>7}{counts[b]:>10}{s['median']*1000:>14.1f}"
                  f"{f'{s["min"]*1000:.1f} – {s["max"]*1000:.1f}':>26}"
                  f"{s['n']:>5}  {status}")

        if fixpoint is not None:
            verdict = f"fixpoint at {fixpoint} iterations"
        elif truncated_from is not None:
            verdict = (f"NO fixpoint within bound 8 — match collection truncated from bound "
                       f"{truncated_from}, so the node counts from there on are starved, not converging")
        else:
            verdict = "no fixpoint within bound 8"
        summaries.append({"m": m, "counts": counts, "fixpoint": fixpoint,
                          "truncated_from": truncated_from, "node_capped": node_capped,
                          "aborted": aborted, "verdict": verdict})
        print(f"    m={m}: node counts by bound {counts}, {verdict}"
              + (f", {aborted}" if aborted else "") + (", node cap hit" if node_capped else ""))
    RESULTS["m3_saturation_grid"] = rows
    RESULTS["m3_convergence_by_term"] = summaries


# ── 4. the abstention matrix ─────────────────────────────────────────────────
BACKENDS = {
    "eggregate": [sys.executable, "-m", "eggregate.server", "--cli"],
    "leanregate": [sys.executable, os.path.join(REGATE, "backends", "leanregate", "grade.py"), "--cli"],
    "coqregate": [sys.executable, os.path.join(REGATE, "backends", "coqregate", "grade.py"), "--cli"],
    "cvc5regate": [sys.executable, os.path.join(REGATE, "backends", "cvc5regate", "grade.py"), "--cli"],
}
OUTCOMES = ["proven_equal", "proven_unequal", "invalid_derivation", "equal_no_certificate", "unknown"]


def m4_abstention_matrix():
    fixtures = sorted(
        os.path.join(REGATE, "conformance", "fixtures", f)
        for f in os.listdir(os.path.join(REGATE, "conformance", "fixtures")) if f.endswith(".json")
    )
    print(f"\n=== 4. ABSTENTION MATRIX — {len(fixtures)} fixtures × {len(BACKENDS)} backends ===")
    print("Every fixture is sent to EVERY backend, not only its declared targets, and the outcome is")
    print("tabulated rather than asserted. `error` is a 400/exit-2 malformed-vocabulary rejection —")
    print("a conformant decline, distinct from `unknown`.")

    # CRITICAL: every backend must be able to reach its prover, or its row measures "binary not
    # on PATH" rather than "abstains by design" — which would make the whole matrix meaningless.
    env = dict(os.environ)
    env["PYTHONPATH"] = os.pathsep.join(
        filter(None, [os.path.join(REGATE, "backends", "eggregate"), env.get("PYTHONPATH", "")])
    )
    tc = os.environ.get("TOOLCHAIN", "/home/user/toolchain")
    env["PATH"] = os.pathsep.join([os.path.join(tc, "bin"), os.path.expanduser("~/.elan/bin"), env.get("PATH", "")])
    env.setdefault("CVC5REGATE_CVC5", os.path.join(tc, "bin", "cvc5"))
    env.setdefault("COQLIB", os.path.join(tc, "lib", "coq"))
    env.setdefault("COQCORELIB", os.path.join(tc, "lib", "coq-core"))
    env.setdefault("OCAMLFIND_CONF", os.path.join(tc, "ocamlfind.conf"))
    env.setdefault("LEANREGATE_LEAN_PROJECT", os.path.join(REGATE, "backends", "leanregate"))
    avail = {
        "cvc5": os.path.isfile(env["CVC5REGATE_CVC5"]),
        "coqc": os.path.isfile(os.path.join(tc, "bin", "coqc")),
        "lean": os.path.isfile(os.path.expanduser("~/.elan/bin/lean")),
        "egglog": True,
    }
    print("  prover availability:", ", ".join(f"{k}={'yes' if v else 'NO'}" for k, v in avail.items()))
    if not all(avail.values()):
        print("  WARNING: a missing prover turns that backend's row into a toolchain artefact, not a design property.")
    RESULTS["m4_prover_availability"] = avail

    tally = {b: dict.fromkeys(OUTCOMES + ["error", "timeout", "crash"], 0) for b in BACKENDS}
    detail = []
    for fx in fixtures:
        req = json.dumps(json.load(open(fx))["request"])
        name = os.path.basename(fx)
        row = {"fixture": name}
        for b, cmd in BACKENDS.items():
            try:
                # 600 s, not 180: fixture 31 is legitimately slow on eggregate's saturation path,
                # and timing out on it would otherwise be miscounted as a crash.
                p = subprocess.run(cmd, input=req, capture_output=True, text=True, timeout=600,
                                   env=env, cwd=os.path.join(REGATE, "backends", "eggregate"))
                out = (p.stdout or "").strip().splitlines()
                obj = json.loads(out[-1]) if out else {}
                key = "error" if "error" in obj else (obj.get("outcome") or "crash")
            except subprocess.TimeoutExpired:
                key = "timeout"                          # slow, but NOT a protocol violation
            except Exception:                            # noqa: BLE001 - a crash IS the datum here
                key = "crash"
            if key not in tally[b]:
                tally[b][key] = 0
            tally[b][key] += 1
            row[b] = key
        detail.append(row)
        print(f"  {name[:44]:<46}" + "".join(f"{row[b][:11]:<13}" for b in BACKENDS))

    hdr = f"\n{'backend':<13}" + "".join(f"{o[:20]:>22}" for o in OUTCOMES) + f"{'error':>9}{'timeout':>9}{'crash':>8}"
    print(hdr)
    print("-" * len(hdr))
    for b in BACKENDS:
        print(f"{b:<13}" + "".join(f"{tally[b][o]:>22}" for o in OUTCOMES)
              + f"{tally[b]['error']:>9}{tally[b]['timeout']:>9}{tally[b]['crash']:>8}")
    RESULTS["m4_abstention"] = {"tally": tally, "detail": detail}


# ── 5. the SAME sweep through the egglog oracle ──────────────────────────────
def m5_egglog_sweep():
    """Reconcile the per-rule constant.

    Measurement 1 sweeps `ProofEGraph.saturate` (the hand-written congruence-closure e-graph)
    and converges to ~2700 µs/rule. The thesis's Table 5 implies ~37 µs/rule — 73x apart, which
    is far too much for machine variance, so the two are almost certainly measuring DIFFERENT
    code paths. eggregate has two: the hand-written ProofEGraph, and the egglog-compiled oracle
    behind `backend.equivalent`. This runs the identical workload through the latter, so the
    thesis can attribute its number to whichever path actually produced it."""
    from eggregate.backend import equivalent
    from eggregate.catalogue import CATALOGUE
    from eggregate.model import add, frac, mul, num, var

    x = var("x")
    lhs = frac(mul(num(3), add(x, num(0))), mul(num(3), num(1)))
    rhs = x
    base = len(CATALOGUE)

    print("\n=== 5. COST vs RULE COUNT through the EGGLOG oracle (backend.equivalent) ===")
    print("Same term and same rule counts as measurement 1, different engine — to identify which")
    print("path Table 5's ~37 µs/rule came from.")
    print(f"\n{'R':>7}{'median (ms)':>14}{'min–max (ms)':>26}{'n':>5}{'t/R (µs)':>11}  result")

    rows = []
    for target in [29, 58, 116, 232, 464, 1000]:
        mult = max(1, round(target / base))
        rs = []
        for i in range(mult):
            rs += [replace(r, id=f"{r.id}__{i}") for r in CATALOGUE]
        R = len(rs)
        seen = {}

        def once(rs=rs, seen=seen):
            seen["v"] = equivalent(lhs, rhs, rules=rs, bound=3)

        try:
            s = measure(once, cap_s=60)
        except Exception as e:                           # noqa: BLE001
            print(f"{R:>7}  ERROR {str(e)[:70]}")
            rows.append({"R": R, "error": str(e)[:120]})
            continue
        rows.append({"R": R, **s, "per_rule_us": s["median"] / R * 1e6, "result": seen.get("v")})
        print(f"{R:>7}{s['median']*1000:>14.1f}"
              f"{f'{s["min"]*1000:.1f} – {s["max"]*1000:.1f}':>26}{s['n']:>5}"
              f"{s['median']/R*1e6:>11.1f}  {seen.get('v')}")
    from eggregate.backend import _ISOLATE
    RESULTS["m5_egglog_sweep"] = {"isolated": _ISOLATE, "rows": rows}
    print(f"\n  process isolation during this sweep: {'ON' if _ISOLATE else 'OFF'}"
          + ("" if _ISOLATE else "  (algorithmic cost — comparable with measurement 1)"))


if __name__ == "__main__":
    which = [a for a in sys.argv[1:] if a in {"1", "2", "3", "4", "5"}] or ["1", "2", "3", "4"]
    if "1" in which:
        m1_rule_sweep()
    if "2" in which:
        m2_lean()
    if "3" in which:
        m3_saturation_grid()
    if "4" in which:
        m4_abstention_matrix()
    if "5" in which:
        m5_egglog_sweep()
    # MERGE, never overwrite: running `bench_v2.py 4` used to clobber the m1/m2/m3 raw samples
    # from earlier invocations, losing measurements that took minutes to produce.
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bench_v2_results.json")
    merged = {}
    if os.path.exists(out):
        try:
            merged = json.load(open(out))
        except Exception:                                # noqa: BLE001
            merged = {}
    merged.update(RESULTS)
    with open(out, "w") as fh:
        json.dump(merged, fh, indent=2)
    print(f"\nraw samples -> {out}")
