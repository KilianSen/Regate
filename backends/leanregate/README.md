# Leanregate

A **second grading backend** for Artemis equational-reasoning exercises, speaking
the **same wire protocol** as [Eggregate](../eggregate) (`GRADING_PROTOCOL.md`)
so the two are interchangeable OCI containers, selected per exercise.

Where Eggregate decides equivalence by *equality saturation* (fast, but soundness
is only fuzzed), Leanregate's angle is **formal**: a student's derivation is
graded by checking each step is an instance of a rule the **Lean kernel has
proven** — and the rules **come from the API**. There is no built-in rule library
and no `Basic.lean`: every rule is transmitted in the request and proven at
request time, so soundness always bottoms out in the kernel, never in a hardcoded
table.

## Pieces

- `lean_prover.py` — the **runtime prover**. A transmitted `exercise.ruleset`
  (authored by a *trusted* instructor) is proven **per rule** by a Lean kernel in
  the container. Hybrid: *auto-prove* by translating the MathNode `lhs`/`rhs` (+
  `conditions` as hypotheses) into a `ℚ`-identity goal and discharging it with
  `field_simp; ring` (a sound rule proves itself; an unsound one — a missing `≠ 0`
  guard — is **rejected**); else *proof-carrying*, kernel-checking a `proof`
  tactic block the rule may ship (for rules outside the ring/field fragment). A
  rule Lean accepts certifies steps under it; one it rejects, or one with no
  proof, is dropped — steps using it grade `unknown`. Per-rule outcomes are
  reported in `meta.ruleset`. It calls `lean` directly against a pruned Mathlib
  (`prune_lake.py`); without the toolchain (e.g. the Lean-free conformance CLI)
  nothing can be proven, so rule-based grading degrades to `unknown`.
- `grade.py` + `lean_check.py` — the protocol-conforming entrypoint (CLI + HTTP),
  `backend = "leanregate"`. `grade._prove_ruleset` proves the transmitted ruleset;
  `lean_check` is the formal step-checker that certifies a submitted derivation by
  checking each step is an instance of a just-proven rule. A step that needs a
  side condition Lean would demand (a guarded rule), a rule the kernel could not
  prove, or value-equivalence without a derivation returns `unknown` — honestly
  inconclusive, never a false grade (the protocol's contract).
- `lean_induction.py` — proof by induction over `ℕ`. The student's **base** and
  **inductive-step** derivations are certified by `lean_check.check_induction`
  (the step may substitute the hypothesis `P(k)`); only then does a Lean
  `induction` (Nat.rec) kernel run backstop the `∀n. P(n)` leap and guard against
  inconsistent transmitted `definitions`. An empty or wrong proof is never
  certified.

## Run / deploy

```sh
python grade.py                 # HTTP: POST /grade, GET /health  (port 8000)
python grade.py --cli           # CLI:  GradeRequest stdin -> GradeResponse stdout
make lean                       # fetch Mathlib oleans for the runtime prover
docker build -t leanregate .    # OCI image (Lean toolchain + pruned Mathlib + wrapper)
```

## How the two relate

| | Eggregate | Leanregate |
|---|---|---|
| Equivalence | equality saturation (e-graph) | Lean-checked rule applications |
| Where rules come from | built-in catalogue + audited custom | **the API** — every rule transmitted, no built-in library |
| Soundness of rules | fuzzed (`check_rules.py`) | **kernel-proven at request time** (`lean_prover.py`), else `unknown` |
| Speed | ms, scales to small terms | slower (invokes Lean) |
| Certificate | re-checkable proof chain | Lean proof term |
| Protocol | `GRADING_PROTOCOL.md` | **same** |

Same `GradeRequest`/`GradeResponse`, same CLI/HTTP transports, same MathNode JSON
— so Artemis treats them as one pluggable grader interface.
