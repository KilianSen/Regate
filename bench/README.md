# bench — cross-backend measurements

`bench_v2.py` produces the evaluation numbers. Raw per-repetition samples land in
`bench_v2_results.json` (committed alongside, so a table can be re-derived without re-running).

```sh
. /path/to/toolchain/env.sh          # cvc5, coqc, elan/lean, egglog on PATH
python3 bench_v2.py                  # measurements 1–4
python3 bench_v2.py 5                # just one; results MERGE into the json
```

## Methodology

- **n ≥ 5** everywhere, topped up to **n = 10** whenever the median is sub-second — that is where
  scheduling jitter is proportionally largest.
- Every cell reports **median and min–max**. The spread is the point: it is what tells you whether
  the median means anything. (Measurement 2 at R = 1 has a 3.05–13.50 s spread from a one-off
  warmup — a mean would have hidden it, and two runs would have reported it as fact.)
- **Cold discipline** is preserved: a fresh `ProofEGraph` per repetition, and statement-unique
  Lean rules per repetition so the rule cache cannot serve a warm proof.

## Measurements

| # | What | Notes |
|---|---|---|
| 1 | eggregate cost vs rule count, `ProofEGraph.saturate` | swept to R = 10 005 |
| 2 | leanregate cost vs rule count | R ∈ {1, 8, 10}, measured — not extrapolated |
| 3 | saturation grid, m ∈ {1..4} × bound ∈ {2,4,6,8} | every cell, incl. those hitting a limit |
| 4 | abstention matrix | every fixture × every backend |
| 5 | the measurement-1 workload through the egglog oracle | identifies which engine a number came from |

## Two things to know before quoting a number

**Which engine.** eggregate has two: the hand-written `ProofEGraph` (~2.7 ms/rule) and the
egglog-compiled oracle behind `backend.equivalent` (~1.1 ms/rule). They differ by 2.5×, so any
per-rule figure has to say which one it describes. Measurements 1 and 5 are the same workload
through each.

**Every prover must be present.** Measurement 4 prints a `prover availability` line first. With a
prover missing, that backend abstains for lack of a binary and its row measures the toolchain
rather than the design — cvc5regate reads 14 `proven_equal` / 18 `unknown` without cvc5, and
26 / 3 with it. Do not report a matrix whose availability line has a `NO` in it.

## Cutoffs

`BENCH_CUTOFF_S` (default 60 s) bounds measurement 3. Note the older `bench.py` prints a row and
*then* breaks on `dt > 5`, so its cutoff means "stop after the first cell over 5 s", not "skip
cells over 5 s".

`watchdog.sh` kills any single process above 8 GB (`LIMIT_KB`) while the harness runs. It exists
because eggregate's saturation could grow unbounded — see `proof_egraph.saturate`, where the
`max_nodes` cap is now enforced inside the rewrite loop rather than only between iterations.
Keep the watchdog: it turns a runaway into one failed cell instead of a dead machine.
