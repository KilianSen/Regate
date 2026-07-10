# Eggregate

A prototype of the **MS3 e-graph reasoning backend** from the bachelor's thesis
*Extending Artemis with proof-based mathematical exercises* (`main.pdf`,
Sections 4.5 / 5.7 and Appendix B), built on [egglog](https://github.com/egraphs-good/egglog)
equality saturation.

In the thesis MS3 is "designed/planned" but not yet implemented. This package
implements it end to end — and grew into a small, self-contained toolkit for
equational-reasoning exercises: grading, proving, hinting, and soundness checking
over a shared rule catalogue. The two core MS3 capabilities:

1. **Equivalence-based grading** (§4.4) — saturate, then check whether the
   student's final expression lands in the *same e-class* as the target. This is
   **path-independent**: it accepts *any* valid derivation, not just a replay of
   one stored chain.
2. **Multi-step hints** (§B.4) — extract a *whole path* to the goal instead of
   the single greedy next move, so guidance can be ordered pedagogically (e.g.
   "clear the +0 first") and ranked by progress-to-goal.

Built on top of those:

- **Two provers** — a minimal-but-incomplete BFS search and a
  complete-but-non-minimal proof-producing e-graph — with a comparison harness.
- **A soundness & fairness layer** — sound numeric disproof, a three-valued
  grading decision, a trusted proof re-checker, and a rule-library audit gate.
- **Sample-solution-guided search** — instructor reference derivations as
  landmarks that stabilise search and align hints to the intended route.
- **Per-exercise precomputation** — saturate once at authoring time, grade many
  submissions fast.

See **Scaling** and **Limitations** below for where this holds up and where it
doesn't.

## Run it

```sh
.venv/bin/python demo.py            # reproduces Appendix B (Tables 6/7/8)
.venv/bin/python demo_backends.py   # bfs vs egg provers, side by side
.venv/bin/python test_eggregate.py  # tests pinning the thesis numbers + soundness
.venv/bin/python check_rules.py     # CI gate: fails if any rewrite rule is unsound
```

Wire `check_rules.py` into CI so the rule library can't regress — a new or
edited rule that isn't a sound, definedness-preserving equality fails the build
with a concrete counterexample.

The dev `.venv` may be free-threaded CPython 3.15t with a locally-built egglog
wheel — but **the deployable image uses stable CPython 3.13 + the official egglog
wheel**; the patched 3.15t build was for experiments only.

## Deploy as a grading backend (OCI)

Eggregate implements a language-agnostic grading contract,
**[`GRADING_PROTOCOL.md`](../../GRADING_PROTOCOL.md)** (`GradeRequest` → `GradeResponse`,
MathNode JSON). A host learning platform integrates against that contract once and
runs this backend as a self-contained, pluggable container, selected per exercise.
(Artemis is the reference adopter; nothing here depends on it.)

```sh
docker build -t eggregate .
docker run -p 8000:8000 eggregate                 # HTTP: POST /grade, GET /health
docker run -i eggregate --cli < request.json      # batch: stdin -> stdout (OCI per-submission run)
```

The same handler (`service.grade`) sits behind both transports. Grading is
mode-aware: reaching the **target form** is full marks; a value-equivalent but
unsimplified answer earns **partial credit** (the thesis distance formula); a
fabricated step result or a non-equivalent answer is rejected (0, with a numeric
witness); and an inconclusive result returns `score: null` for review — never a
false grade.

**The ruleset travels in the request, not the binary.** An exercise supplies its
own rules inline (`exercise.ruleset`: full pattern/template/guard definitions
with wildcards) or references the built-in catalogue by id (`exercise.rules`).
This realises the thesis's instructor-authored rules (§6.3). The ruleset is
authored and validated **upstream** (a code contribution, reviewed + CI-checked),
so eggregate **trusts it by default** and grades the derivation against it. To
re-check anyway — a not-yet-trusted source, or CI — set `options.verify_rules`
(`options.audit_rules` is the older spelling): the soundness fuzzer runs and
**rejects an unsound rule with a counterexample** (e.g. `x/x → 1` without `x ≠ 0`)
before it can grade anything. The built-in catalogue is only eggregate's own
test/demo/gate fixture, not the production rule source.

## Layout — and how it maps to the thesis

| File | Role | Thesis |
|---|---|---|
| `eggregate/model.py` | `MathNode` typed tree (the persisted JSON shape), alphabetical-slot path encoding, pretty-printer, `MathNodeDistance` metric | §4.1, §5.2, §5.6 |
| `eggregate/matching.py` | the single shared matcher/instantiator (client + server can't diverge) | §4.3, §9 |
| `eggregate/conditions.py` | three-valued side conditions for **guarded rules** (nonzero/positive/integer/…) | §5, §6.3 |
| `eggregate/catalogue.py` | the rewrite-rule catalogue as **one shared data source** | Table 4, §4.3 |
| `eggregate/validate.py` | **step-local validator**: Type-A rule application, Type-B Leibniz substitution, whole-proof replay | §5, doc §3/§5 |
| `eggregate/backend.py` | egglog `Math` datatype, catalogue→ruleset compiler, **bounded** equality saturation, `equivalent` / `grade` (pass-sound oracle) | §4.5, §5.7, §6.3 |
| `eggregate/hints.py` | directed step engine, greedy one-ply `greedy_hints`, and `shortest_path` / `all_shortest_paths` (paths + `N_min`) — **prover #1 (bfs)** | §5.6, §B.4 |
| `eggregate/proof_egraph.py` | a **proof-producing e-graph** (congruence closure + provenance + `explain`) — **prover #2 (egg)** | §4.5; FMCAD 2022 |
| `eggregate/compare.py` | run both provers on one goal and contrast (existence, length, time) | — |
| `eggregate/semantics.py` | exact rational evaluation + **counterexample search** (sound disproof) | §5 soundness |
| `eggregate/audit.py` | **rule-library soundness fuzzer** (catches unsound rules / missing guards) | §5, doc "verify the rules" |
| `eggregate/robust.py` | three-valued `decide_equivalence`, `grade_robust`, and `recheck_proof` (trusted kernel) | §4.4 |
| `eggregate/reference.py` | **sample-solution-guided** proving / hints / progress (landmark search) | §B.4 |
| `eggregate/precompute.py` | **per-exercise e-graph precomputation** — saturate once, grade many | §6.1 |
| `eggregate/service.py` | grading-protocol handler (maps the contract onto the internals) | §5.5 |
| `eggregate/server.py` | CLI + HTTP transports for the protocol | §5.5 |
| `demo.py` / `demo_backends.py` | Appendix B; and the two provers side by side | Appendix B |

The catalogue is consumed by **two engines without duplication** — the egglog
ruleset is *compiled* from it, and the directed stepper/validator *interpret* it
directly through the one shared matcher. This is the thesis's "single shared rule
source, two engines" principle (§4.3), here made literal.

## Division of labour (corrected per the design doc)

The earlier transcript overstated egglog's role. The corrected split:

- **Step-local soundness lives in `validate.py`, not the e-graph.** A step is
  valid *by construction* — we matched a rule's LHS and emitted its RHS. The
  validator returns three-valued results: `valid`, `invalid` (e.g. a violated
  guard, or `0/0 = 1`), or `open` (a guard like `x ≠ 0` the student must
  discharge via a declared assumption).
- **The e-graph is a pass-sound equivalence oracle only.** `equivalent`/`grade`
  trust a successful `check`; a failure means "not proven within the bound," not
  "unequal." It is the right tool for *manual edits* and *macro-steps*, not for
  re-confirming steps the engine just produced.
- **Two provers, both producing proofs (paths), neither relying on
  egglog's broken proof mode.**
  - `bfs` (`hints.shortest_path`): forward search → **minimal** chain, but only
    over the forward-directed fragment (no symmetric/uphill moves).
  - `egg` (`proof_egraph.egg_prove`): our own **proof-producing e-graph** —
    congruence closure + a provenance spanning tree + `explain`, the way egg's
    `explain_equivalence` works (Flatt et al., FMCAD 2022). Handles symmetric and
    congruence-driven equalities BFS can't reach; proofs are **not guaranteed
    minimal**. Saturation stops as soon as the endpoints connect, which keeps the
    AC/distributivity blow-up bounded.

  `compare.py` runs both and reports where they agree/diverge — e.g. `x == x+0`
  is provable by `egg` but not by forward `bfs`. We built our own e-graph because
  egglog's proof extraction is non-functional (see `docs/NOTES-egglog-proofs.md`).
- **Guarded rules are where soundness actually lives.** The oracle only compiles
  literal-decidable guards (so it never blesses `x/x = 1` for symbolic `x`);
  symbolic guards are discharged by the validator against student assumptions.

## Soundness & fairness layer (defending both false positives and false negatives)

A grader has two failure modes, defended separately:

- **False positive (unsound credit).** Defended by requiring a *re-checked
  constructive proof*, not a bare oracle `check`: `robust.recheck_proof` is a
  trusted kernel that independently re-validates every step of whichever backend
  produced the proof (a tampered or buggy certificate is rejected). And the rule
  library itself is fuzzed: `audit.audit_catalogue` plugs random exact rationals
  into each rule and asserts **definedness-preserving** equality — so a missing
  `x ≠ 0` guard (e.g. `x/x → 1`, which lies at `x = 0`) is caught with a
  concrete counterexample. The shipped catalogue audits clean; both guarded
  rules are confirmed load-bearing.
- **False negative (unfair zero).** Defended by never collapsing an ambiguous
  "no proof within budget" into "wrong". `semantics.find_counterexample` gives a
  *sound disproof* (a numeric witness ⇒ genuinely unequal), and
  `robust.decide_equivalence` returns one of four outcomes —
  `PROVEN_EQUAL` (re-checked certificate), `PROVEN_UNEQUAL` (witness),
  `EQUAL_NO_CERTIFICATE` (oracle says yes but no proof — suspicious), or
  `UNKNOWN` (escalate). `grade_robust` maps the last two to `score=None`
  ("send to review"), never a false zero or unearned full marks.

Order matters: `decide_equivalence` **disproves first** (numbers are ground
truth and cheap), then **proves with a re-checked certificate**, then falls back
to the weaker oracle.

## Sample-solution-guided search (stabilising the exponential part)

Blind global search is the exponential cost (see scaling notes). An instructor
authoring an exercise already knows a solution, so `reference.py` lets you supply
it as a **reference derivation** (the sequence of intermediate states) and use it
as landmarks:

- **Proving** decomposes into `k` trivial one-hop searches instead of one global
  search — `guided_prove` returns a stable, reference-aligned proof. `check_reference`
  validates the instructor's own solution and recovers its fine-grained steps.
- **Hints** follow the *intended route*, fixing the §B.4 complaint: at the source,
  greedy picks `frac_mul_cancel_left` ("removes the most structure"), but
  `guided_hint` returns `add_zero_right` — "clear the +0 first". A student who
  **diverges** is re-anchored to the nearest waypoint and steered back onto the
  rail; search only ever covers the gap to a nearby landmark (depth-bounded),
  never the whole problem.
- **Partial credit** is `progress(state, ref)` — fraction of the reference
  travelled, measured *structurally* (in an equational derivation every state is
  value-equal to every other, so only closeness of *form* can measure progress).

## Per-exercise precomputation (saturate once, grade many)

An exercise is authored once and graded for many students, and saturation
depends only on the exercise — so `precompute.py` does it once:

```python
exg = precompute_exercise(source, target, rules, reference=ref)  # author-time
g   = grade_submission(exg, student_final)                       # per student
```

The precomputed graph already holds the target's equivalence class, so a student
whose answer is one of those forms is graded by a **hash lookup + congruence
rebuild with no saturation at all** (`g.saturated is False`); only a genuinely
novel form triggers a small *incremental* saturation seeded from it (early-stop
on the target), never the full base again. Each submission runs on a `clone()`
so they can't contaminate one another. The *score* comes from this fast path;
the *proof* (only when asked) is a fresh early-stopping `egg_prove`. Measured:
scoring 300 submissions amortised is ~2.8× faster than re-checking each from
scratch, and the gap widens with the rule-set size. This is the thesis's §6.1
"up-front saturation cost and storage for fast checks at grading time".

> Implementation note: reconstructing a flat proof from a *rich* saturated graph
> can pick a stale path, so `replay_explanation` degrades gracefully (returns
> `None`) and `egg_prove` falls back to a reliable search rather than raising —
> the latent crash flagged in the limitations is now contained.

## Scaling

Two regimes, set by whether the active rules *expand* terms (distributivity, AC)
or only shrink them: the **benign** regime is linear/polynomial (a 257-node term
with a 128-step proof proves in <0.3 s), the **hostile** regime explodes (three
nested distributable products → 20 k e-nodes). Equality is near-`O(1)`; proof
search is exponential in depth; saturation is exponential in the iteration bound
for AC theories; rule count is *linear* per step. Full analysis, complexity
table, and reproducible numbers in **[`SCALING.md`](docs/SCALING.md)** (run
`.venv/bin/python bench.py`).

## Limitations

Soundness is *empirical, not formal* (random testing, not a verified rule
library); proving is *incomplete both ways* (bounded/forward-only); the egg
backend is *our reimplementation, lightly tested*; scope is *school algebra
only*; and it is *not yet wired into a production host*. Full, tagged breakdown
(deliberate scope vs. immaturity vs. method limits) in
**[`LIMITATIONS.md`](docs/LIMITATIONS.md)**.

## Design notes / known edges

- **Single shared source.** `backend._compile` turns each catalogue `Rule` into
  an egglog rewrite: forward (F) → one-directional `rewrite`; bidirectional (B)
  → `birewrite`; a `NotEqualToConstant` side condition binds the wildcard to an
  `i64` literal guarded by `ne(.., 0)` (this is how `frac_mul_cancel_left`
  discharges `c ≠ 0`). A B-rule with a lone-wildcard side (e.g. `-(-a) ⇄ a`)
  compiles to a forward rewrite from the structured side, since egglog forbids
  rewriting *from* a bare variable; the e-graph union is symmetric regardless.
- **Bounded saturation.** Bidirectional assoc/comm/distrib have no finite
  fixpoint, so saturation is run for a fixed number of iterations
  (`DEFAULT_BOUND = 5`), not to convergence — the "termination/resource bound"
  §6.3 calls for. The worked example's equivalence is found by iteration 3;
  beyond ~5 the distributivity/AC blow-up dominates with no benefit. Larger or
  deeper expressions may need a different bound and will cost more — bounding
  saturation predictably is the open risk the thesis names.
- **Sound, not complete.** Equivalence grading is sound up to the rule theory
  and the bound. A `False` from `equivalent` means "not proven equal within the
  bound", not "provably unequal".
