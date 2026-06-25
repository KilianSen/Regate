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
- `grade.py` — a protocol-conforming entrypoint (CLI + HTTP), `backend =
  "leanregate"`, deployable **today**: it returns well-formed `GradeResponse`s
  so Artemis can integrate against both backends now, with the formal step-check
  wired in as `Basic.lean` grows. Until then it grades the decidable part
  (reaching the target form) and returns `unknown` where a Lean proof is needed —
  honestly inconclusive, never a false grade (the protocol's contract).

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
| Soundness of rules | fuzzed (`check_rules.py`) | **proven** (`Basic.lean`) |
| Speed | ms, scales to small terms | slower (invokes Lean) |
| Certificate | re-checkable proof chain | Lean proof term |
| Protocol | `GRADING_PROTOCOL.md` | **same** |

Same `GradeRequest`/`GradeResponse`, same CLI/HTTP transports, same MathNode JSON
— so Artemis treats them as one pluggable grader interface.
