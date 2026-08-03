#!/usr/bin/env python3
"""
Measurements 6-9. Same methodology as bench_v2 (see bench/README.md): n >= 5, topped up to
n = 10 when the median is sub-second; median AND min-max on every cell; cold discipline.

  6. Derivation length k          -- replaces Table 12 (pre-bugfix), reports t/k^2
  7. Ruleset size, CARRYING       -- replaces Table 13; the rules are parsed, never matched
  8. Induction by backend         -- replaces Table 15 (n = 2), incl. the 1 s cvc5 budget
  9. Transport baseline           -- one delta, so 1-3 and 6-8 can stay in-process

  python3 bench_v3.py [6] [7] [8] [9]
"""
from __future__ import annotations

import json
import os
import statistics
import subprocess
import sys
import time
import urllib.request

REGATE = os.environ.get("REGATE_PATH", "/home/user/projects/ba/Regate")
EGG = os.path.join(REGATE, "backends", "eggregate")
sys.path.insert(0, EGG)

RESULTS: dict = {}
CUTOFF_S = float(os.environ.get("BENCH_CUTOFF_S", "60"))


def stat(samples: list[float]) -> dict:
    return {"n": len(samples), "median": statistics.median(samples),
            "min": min(samples), "max": max(samples),
            "samples": [round(s, 6) for s in samples]}


def measure(fn, min_reps: int = 5, sub_second_reps: int = 10, cap_s: float | None = None) -> dict:
    samples: list[float] = []
    for _ in range(min_reps):
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


def rng(s: dict) -> str:
    return f"{s['min'] * 1000:.1f} – {s['max'] * 1000:.1f}"


# ── 6. derivation length k ───────────────────────────────────────────────────
def m6_derivation_length():
    """Cost of REPLAYING a k-step derivation, in-process (validate.verify_chain — no e-graph).

    Table 12's Θ(k²) was measured before the bugfix, so it is re-measured here. The spine is
    right-nested `((x+0)+0)+…` with k zeros and the derivation applies `add_zero_right` k times,
    peeling one zero per step. t/k² is the column that shows whether the quadratic term is real;
    it only becomes visible in the hundreds, which is why the sweep runs that far."""
    from eggregate.catalogue import CATALOGUE
    from eggregate.model import add, num, var
    from eggregate.validate import Move, verify_chain

    rule = next(r for r in CATALOGUE if r.id == "add_zero_right")
    x = var("x")

    def spine(k):
        t = x
        for _ in range(k):
            t = add(t, num("0"))
        return t

    print("\n=== 6. DERIVATION LENGTH k (in-process replay, single rule) ===")
    print(f"\n{'k':>6}{'median (ms)':>14}{'min–max (ms)':>26}{'n':>5}{'t/k (µs)':>11}{'t/k² (ns)':>12}")
    rows = []
    for k in [50, 100, 200, 300, 400, 480, 700, 1000]:
        src = spine(k)
        # k steps, each peeling the outermost `+0` at the root.
        moves = [Move(kind="A", path=(), rule=rule) for _ in range(k)]

        def once(src=src, moves=moves):
            verify_chain(src, moves, x)

        s = measure(once, cap_s=CUTOFF_S)
        rows.append({"k": k, **s, "t_per_k_us": s["median"] / k * 1e6,
                     "t_per_k2_ns": s["median"] / (k * k) * 1e9})
        print(f"{k:>6}{s['median']*1000:>14.1f}{rng(s):>26}{s['n']:>5}"
              f"{s['median']/k*1e6:>11.1f}{s['median']/(k*k)*1e9:>12.1f}")
        if s.get("capped"):
            print(f"{'':>6}  (cutoff {CUTOFF_S:g}s reached — sweep stops here)")
            break
    RESULTS["m6_derivation_length"] = rows
    if len(rows) >= 2:
        a, b = rows[0], rows[-1]
        growth = (b["median"] / a["median"]) / ((b["k"] / a["k"]) ** 2)
        print(f"\n  k {a['k']}→{b['k']}: time grew {b['median']/a['median']:.1f}x for a "
              f"{b['k']/a['k']:.0f}x longer derivation.")
        print(f"  Against a pure k² model that is {growth:.2f}x (1.00 = exactly quadratic).")


# ── 7. ruleset size, CARRYING (not saturating) ───────────────────────────────
def m7_carrying_ruleset():
    """The cost of CARRYING rules that are never used.

    This is what old Table 13 measured and what measurement 1 does not: R copies of
    `add_zero_right` under distinct ids, of which the submission matches only the first, so the
    other R−1 are parsed, registered and indexed but never fire. That is the number behind
    "an instructor can grow the palette freely".

    Run it beside m1 (saturating, ~2.70 ms/rule) and label which is which — the pair is the
    result. A per-rule figure quoted without saying which regime it came from is ~70x wrong in
    one direction or the other."""
    from eggregate import service

    def payload(R):
        rules = [{"id": f"azr_{i}", "owner": "add",
                  "lhs": {"type": "add", "slots": {
                      "left": [{"type": "wild", "value": "a"}],
                      "right": [{"type": "number", "value": "0"}]}},
                  "rhs": {"type": "wild", "value": "a"},
                  "bidirectional": False, "conditions": []} for i in range(R)]
        src = {"type": "add", "slots": {"left": [{"type": "variable", "value": "x"}],
                                        "right": [{"type": "number", "value": "0"}]}}
        tgt = {"type": "variable", "value": "x"}
        return {"protocol": "1.1",
                "exercise": {"mode": "transformation", "source": src, "target": tgt,
                             "ruleset": rules},
                "submission": {"steps": [{"kind": "A", "rule": "azr_0", "path": [],
                                          "direction": "forward", "result": tgt}],
                               "final": tgt}}

    print("\n=== 7. RULESET SIZE — CARRYING cost (R−1 rules parsed, never matched) ===")
    print(f"\n{'R':>6}{'median (ms)':>14}{'min–max (ms)':>26}{'n':>5}{'t/R (µs)':>11}  outcome")
    rows = []
    for R in [1, 25, 100, 400, 1000, 3000]:
        req = payload(R)
        seen = {}

        def once(req=req, seen=seen):
            seen["o"] = service.grade(json.loads(json.dumps(req))).get("outcome")

        s = measure(once, cap_s=CUTOFF_S)
        rows.append({"R": R, **s, "per_rule_us": s["median"] / R * 1e6, "outcome": seen.get("o")})
        print(f"{R:>6}{s['median']*1000:>14.1f}{rng(s):>26}{s['n']:>5}"
              f"{s['median']/R*1e6:>11.1f}  {seen.get('o')}")
    RESULTS["m7_carrying_ruleset"] = rows
    if len(rows) >= 2:
        marg = ((rows[-1]["median"] - rows[0]["median"]) / (rows[-1]["R"] - rows[0]["R"])) * 1e6
        print(f"\n  marginal cost per carried rule: {marg:.1f} µs "
              f"(m1's SATURATING cost was ~2700 µs/rule — same axis, different regime)")


# ── 8. induction by backend ──────────────────────────────────────────────────
def m8_induction_by_backend():
    """The certified ℕ fixture through each induction backend, n >= 5 (Table 15 had n = 2).

    cvc5regate appears twice: at its default counterexample budget and at the 1 s budget, because
    §6.3 and the Table 15 caption both quote 1.05 s and that figure is currently derived rather
    than measured."""
    fixture = os.path.join(REGATE, "conformance", "fixtures",
                           "23-induction-certified-inline-ruleset.json")
    req = json.dumps(json.load(open(fixture))["request"])

    tc = os.environ.get("TOOLCHAIN", "/home/user/toolchain")
    env = dict(os.environ)
    env["PATH"] = os.pathsep.join([os.path.join(tc, "bin"), os.path.expanduser("~/.elan/bin"),
                                   env.get("PATH", "")])
    env.setdefault("CVC5REGATE_CVC5", os.path.join(tc, "bin", "cvc5"))
    env.setdefault("COQLIB", os.path.join(tc, "lib", "coq"))
    env.setdefault("COQCORELIB", os.path.join(tc, "lib", "coq-core"))
    env.setdefault("OCAMLFIND_CONF", os.path.join(tc, "ocamlfind.conf"))
    env.setdefault("LEANREGATE_LEAN_PROJECT", os.path.join(REGATE, "backends", "leanregate"))

    lanes = [
        ("coqregate", "coqregate", {}),
        ("leanregate", "leanregate", {}),
        ("cvc5regate (default budget)", "cvc5regate", {}),
        ("cvc5regate (1 s budget)", "cvc5regate", {"CVC5REGATE_DISPROVE_TIMEOUT": "1"}),
    ]
    print("\n=== 8. INDUCTION BY BACKEND (fixture 23, certified ℕ) ===")
    print(f"\n{'backend':<30}{'median (s)':>12}{'min–max (s)':>24}{'n':>5}  outcome")
    rows = []
    for label, backend, extra in lanes:
        cmd = [sys.executable, os.path.join(REGATE, "backends", backend, "grade.py"), "--cli"]
        lane_env = {**env, **extra}
        seen = {}

        def once(cmd=cmd, lane_env=lane_env, seen=seen):
            p = subprocess.run(cmd, input=req, capture_output=True, text=True,
                               env=lane_env, cwd=os.path.dirname(cmd[1]), timeout=600)
            try:
                seen["o"] = json.loads(p.stdout.strip().splitlines()[-1]).get("outcome")
            except Exception:                            # noqa: BLE001
                seen["o"] = "no-parse"

        s = measure(once, cap_s=CUTOFF_S)
        rows.append({"lane": label, "backend": backend, **s, "outcome": seen.get("o")})
        print(f"{label:<30}{s['median']:>12.2f}"
              f"{f'{s["min"]:.2f} – {s["max"]:.2f}':>24}{s['n']:>5}  {seen.get('o')}")
    RESULTS["m8_induction_by_backend"] = rows


# ── 9. transport baseline ────────────────────────────────────────────────────
def m9_transport():
    """One transport delta, so measurements 1-3 and 6-8 can stay in-process honestly.

    A per-row "round-trip overhead %" column invites the reader to compare it against an
    in-process number that never paid it. Measure the fixed cost once instead: GET /health x20
    for the bare round trip, then ONE representative payload both over HTTP and in-process."""
    from eggregate import service

    port = int(os.environ.get("BENCH_PORT", "8137"))
    # The server takes `--port N` on the command line; it does NOT read a PORT env var, and
    # defaults to 8000 — which the docker eggregate container already holds on this host.
    proc = subprocess.Popen([sys.executable, "-m", "eggregate.server", "--port", str(port)],
                            cwd=EGG, env=dict(os.environ),
                            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    base = f"http://127.0.0.1:{port}"
    try:
        for _ in range(50):
            try:
                urllib.request.urlopen(f"{base}/health", timeout=1).read()
                break
            except Exception:                            # noqa: BLE001
                time.sleep(0.2)
        else:
            print("\n=== 9. TRANSPORT BASELINE ===\n  SKIPPED — server did not come up on "
                  f"{base} (is the port taken? set BENCH_PORT)")
            RESULTS["m9_transport"] = {"skipped": "server did not start"}
            return

        print("\n=== 9. TRANSPORT BASELINE ===")
        health = measure(lambda: urllib.request.urlopen(f"{base}/health", timeout=5).read(),
                         min_reps=20, sub_second_reps=20)
        print(f"  GET /health   median {health['median']*1000:.2f} ms  "
              f"[{health['min']*1000:.2f} – {health['max']*1000:.2f}]  n={health['n']}")

        src = {"type": "add", "slots": {"left": [{"type": "variable", "value": "x"}],
                                        "right": [{"type": "number", "value": "0"}]}}
        tgt = {"type": "variable", "value": "x"}
        req = {"protocol": "1.1",
               "exercise": {"mode": "transformation", "source": src, "target": tgt,
                            "rules": ["add_zero_right"]},
               "submission": {"final": tgt}}
        body = json.dumps(req).encode()

        def over_http():
            r = urllib.request.Request(f"{base}/grade", data=body,
                                       headers={"Content-Type": "application/json"})
            urllib.request.urlopen(r, timeout=30).read()

        http_s = measure(over_http)
        inproc_s = measure(lambda: service.grade(json.loads(body)))
        delta = http_s["median"] - inproc_s["median"]
        print(f"  same payload  HTTP      {http_s['median']*1000:8.2f} ms  [{rng(http_s)}]  n={http_s['n']}")
        print(f"                in-process{inproc_s['median']*1000:8.2f} ms  [{rng(inproc_s)}]  n={inproc_s['n']}")
        print(f"\n  transport delta: {delta*1000:.2f} ms  "
              f"({'dominated by transport' if delta > inproc_s['median'] else 'small vs the grading work'})")
        print("  Quote this ONCE, rather than an overhead column per row.")
        RESULTS["m9_transport"] = {"health": health, "http": http_s, "inproc": inproc_s,
                                   "delta_s": delta}
    finally:
        proc.terminate()
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            proc.kill()


if __name__ == "__main__":
    which = [a for a in sys.argv[1:] if a in {"6", "7", "8", "9"}] or ["6", "7", "8", "9"]
    if "6" in which:
        m6_derivation_length()
    if "7" in which:
        m7_carrying_ruleset()
    if "8" in which:
        m8_induction_by_backend()
    if "9" in which:
        m9_transport()
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bench_v2_results.json")
    merged = {}
    if os.path.exists(out):
        try:
            merged = json.load(open(out))
        except Exception:                                # noqa: BLE001
            merged = {}
    merged.update(RESULTS)
    json.dump(merged, open(out, "w"), indent=2)
    print(f"\nraw samples -> {out}")
