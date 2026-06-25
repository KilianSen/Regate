# Does egglog give us proof paths? (empirical finding)

**Short answer: no — not in a usable form.** This matters for the architecture,
because hints and the `N_min` "elegance" metric both want the *rewrite path*
between two terms, and equality saturation does not hand it to you.

## What we tested

Against the locally-built **egglog 13.2.0** (Rust core `egg-smol` rev `2e5657b`,
PyO3 0.29, free-threaded CPython 3.15t):

| Probe | Result |
|---|---|
| `dir(egglog)` / `EGraph` methods for proof/explain | none — only `check`, `extract`, `extract_multiple` |
| low-level `egglog.bindings` | `Prove(span, facts)`, `ProveExists(span, expr)`, `ProveExistsOutput(proof)` exist |
| run `(prove (= x y))` via the text frontend | **panics**: `no :internal-proof-func annotation recorded for sort @ExistsSort` at `src/proofs/proof_extraction.rs:74` |
| `(set-option enable_proofs 1)` | `Unbound symbol enable_proofs` |
| `EGraph(...)` proofs flag | no such option |

So the proof feature is **wired into the Rust core but non-functional**: the
`prove` command parses, dispatches into the proof extractor, and crashes on
missing internal annotations. The `Prove`/`ProveExists` binding primitives feed
that same incomplete machinery. There is no high-level workflow and no enable
switch. This independently confirms the EGRAPHS-2024 report that egglog proof
extraction is planned-but-not-yet-usable.

## Two more facts that point the same way

- **`extract` optimises cost, not proof length.** It returns the lowest-cost
  *term* in an e-class — a different problem from the shortest *rewrite chain*
  between two terms. Even a working extractor would not give `N_min`.
- **A failed `check` is ambiguous.** Equality saturation is sound but
  incomplete: a failed `(check (= a b))` means "not equal, OR not saturated, OR
  ran out of budget." Safe to act on a *pass*, not on a *fail*.

## Consequence for Eggregate (what the code does)

- **egglog is used only as a pass-sound equivalence oracle** (`backend.equivalent`
  / `grade`): a successful `check` after bounded saturation is trusted; a failure
  is reported as "not proven within the bound," never as "provably unequal."
- **Per-step soundness does not use the e-graph at all** (`validate.py`): a step
  is valid by construction because we matched a rule LHS and emitted its RHS.
- **We get proof paths from two backends of our own, not from egglog:**
  - `hints.shortest_path` — BFS over directed rule applications: **minimal** by
    construction, but only over the forward fragment.
  - `proof_egraph.egg_prove` — **our own proof-producing congruence-closure
    e-graph** (provenance spanning tree + `explain`), implemented because
    egglog's proof mode is broken. ~450 LOC; the FMCAD-2022 proof-minimization
    pass is deliberately omitted (proofs are correct, just not minimal — and BFS
    covers the minimal case).

So rather than wait on egglog's planned proof feature or stand up an `egg` (Rust)
`explain_equivalence` microservice, we reimplemented the proof-producing
congruence closure directly in Python. `egg` remains a future option if we ever
need its performance, but it would add a Rust service, its explanations are not
minimal either, and we would still run the BFS for `N_min` — so it currently buys
us nothing the two Python backends don't already provide.
