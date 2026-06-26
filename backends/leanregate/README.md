# Leanregate

A **second grading backend** for Artemis equational-reasoning exercises, speaking
the **same wire protocol** as [Eggregate](../eggregate) (`GRADING_PROTOCOL.md`)
so the two are interchangeable OCI containers, selected per exercise.

Where Eggregate decides equivalence by *equality saturation* (fast, but soundness
is only fuzzed), Leanregate's angle is **formal**: the rewrite rules are
**proven sound once in Lean**, and a student's derivation is graded by checking
each step is an instance of a proven lemma. This is the gold-standard version of
Eggregate's `check_rules.py` — it answers the top future-work item in
`../../docs/LIMITATIONS.md` (a Lean-verified rule library).

## Status

- `Leanregate/Basic.lean` — the verified rule library (the real deliverable):
  each catalogue rule stated and proven as a `ℚ` identity under its side
  condition. **Seeded with several rules; the rest follow the same pattern.**
  *(Not compiled in the scaffolding environment — needs `lake build` with
  Mathlib.)*
- `grade.py` + `lean_check.py` — a protocol-conforming entrypoint (CLI + HTTP),
  `backend = "leanregate"`, deployable **today**. `lean_check` is the formal
  step-checker: it certifies a submitted derivation by checking each step is an
  instance of a lemma **proven in `Basic.lean`** (its `PROVEN` table mirrors the
  file one-for-one), and attaches the Lean lemma names as the proof. A step that
  needs a side condition Lean would demand (the guarded fraction rules), an
  unknown rule, or value-equivalence without a derivation returns `unknown` —
  honestly inconclusive, never a false grade (the protocol's contract). The
  Python checker runs today; `Basic.lean` is the soundness proof of the rules it
  trusts (compile it with `lake build`).
- `lean_prover.py` — the **runtime prover**, for inline custom rulesets. The
  built-in rules are proven ahead of time in `Basic.lean`; a transmitted
  `exercise.ruleset` (from a *trusted* author — instructor, not student) is
  instead proven **at request time** by a Lean kernel running in the container.
  Per rule, hybrid: *auto-prove* by translating the MathNode `lhs`/`rhs` (+
  `conditions` as hypotheses) into a `ℚ`-identity goal and discharging it with
  `field_simp; ring` (the whole catalogue is in this fragment, so a sound rule
  proves itself and an unsound one — a missing `≠ 0` guard — is **rejected**);
  else *proof-carrying*, kernel-checking a `proof` tactic block the rule may ship
  (for rules outside the ring/field fragment). A rule Lean accepts certifies
  steps under it; one it rejects, or one with no proof, is dropped — steps using
  it grade `unknown`. Proven outcomes per rule are reported in `meta.ruleset`.
  Soundness still bottoms out in the Lean kernel, never the author's word.
  Without the toolchain (e.g. the Lean-free conformance CLI) an inline ruleset
  degrades to `unknown` — honest, never a false grade.

## Run / deploy

```sh
python grade.py                 # HTTP: POST /grade, GET /health  (port 8000)
python grade.py --cli           # CLI:  GradeRequest stdin -> GradeResponse stdout
lake build                      # build & check the verified rule library
docker build -t leanregate .    # OCI image (Lean toolchain + wrapper)
```

## How the two relate

| | Eggregate | Leanregate |
|---|---|---|
| Equivalence | equality saturation (e-graph) | Lean-checked rule applications |
| Soundness of rules | fuzzed (`check_rules.py`) | **proven** — built-ins in `Basic.lean`, transmitted rulesets by the runtime kernel (`lean_prover.py`) |
| Custom rule on the wire | audited (fuzzed), then trusted | **kernel-proven** per rule, else `unknown` |
| Speed | ms, scales to small terms | slower (invokes Lean) |
| Certificate | re-checkable proof chain | Lean proof term |
| Protocol | `GRADING_PROTOCOL.md` | **same** |

Same `GradeRequest`/`GradeResponse`, same CLI/HTTP transports, same MathNode JSON
— so Artemis treats them as one pluggable grader interface.
