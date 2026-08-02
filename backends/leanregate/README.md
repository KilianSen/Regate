# Leanregate

A pluggable grading backend for equational-reasoning exercises in learning
platforms. It implements the language-agnostic grading contract
**[`GRADING_PROTOCOL.md`](../../GRADING_PROTOCOL.md)** (`GradeRequest` →
`GradeResponse`, MathNode JSON, CLI + HTTP transports), so a host platform
integrates against that contract once and runs this backend as a self-contained
container, selected per exercise. (Artemis is the reference adopter; nothing here
depends on it.)

Leanregate's angle is **formal**: a student's derivation is graded by checking
each step is an instance of a rule the **Lean kernel has proven** — and the rules
**come from the API**. There is no built-in rule library and no `Basic.lean`:
every rule is transmitted in the request and proven at request time, so soundness
always bottoms out in the kernel, never in a hardcoded table. The backend is
honest by construction: anything the kernel cannot certify returns `unknown`,
never a false grade.

## Pieces

- `lean_prover.py` — the **runtime prover**. A transmitted `exercise.ruleset`
  (authored upstream by a *trusted* contributor) is proven **per rule** by a Lean
  kernel in the container: the MathNode `lhs`/`rhs` (+ `conditions` as hypotheses)
  is translated into a `ℚ`-identity goal and discharged with `field_simp; ring`
  (a sound rule proves itself; an unsound one — a missing `≠ 0` guard — is
  **rejected**). A rule outside that automatic fragment (e.g. a relational `iff`
  rewrite) is simply unproven; Regate does **not** run a caller-supplied proof
  script (an injection surface), so a rule's `proof` field is ignored. A rule Lean
  accepts certifies steps under it; one it cannot prove is dropped — steps using
  it grade `unknown`. Per-rule outcomes are reported in `meta.ruleset`. It calls
  `lean` directly against a pruned Mathlib (`prune_lake.py`); without the toolchain
  (e.g. the Lean-free conformance CLI) nothing can be proven, so rule-based grading
  degrades to `unknown`.
- `grade.py` + `lean_check.py` — the protocol-conforming entrypoint (CLI + HTTP),
  `backend = "leanregate"`. `grade._prove_ruleset` proves the transmitted ruleset;
  `lean_check` is the formal step-checker that certifies a submitted derivation by
  checking each step is an instance of a just-proven rule. A step that needs a
  side condition Lean would demand (a guarded rule), a rule the kernel could not
  prove, or value-equivalence without a derivation returns `unknown` — honestly
  inconclusive, never a false grade (the protocol's contract).
- `lean_induction.py` — proof by induction over `ℕ` (`mode: "induction"`). The
  student's **base** and **inductive-step** derivations are certified by
  `lean_check.check_induction` (the step may substitute the hypothesis `P(k)`,
  at a *shifted accumulator* if the goal has one — the emitted proof generalizes
  the accumulators before inducting); only then does a Lean `induction` (Nat.rec)
  kernel run backstop the `∀n. P(n)` leap and guard against inconsistent
  transmitted `definitions`. An empty or wrong proof is never certified.
  **Recursive functions travel as data**: both the `pow` node and the `apply` node
  (n-ary *named* function application, protocol 1.1) are compiled from the
  transmitted `definitions` — a base rule `f(…, 0, …)` and a step rule
  `f(…, succ k, …)` recursing on that argument, at any position — into a
  structurally-recursive Lean `def`. A host adds a new operator by transmitting
  its two definition rules; no backend code changes. Lean admits the `def` only if
  its equation compiler proves it terminating, so a bogus "definition" is a compile
  error (`unknown`), never a route to a false certificate. Out of scope and
  declined as `unknown`: `exercise.datatype` (list/tree induction), a function in a
  ℕ position, mutual recursion, and ℕ-truncated subtraction.

## Trust model

`certified: true` rests on the **Lean kernel**: every transmitted rule is proven
at request time, and a derivation is certified only when every step is an instance
of a kernel-proven rule (and, for induction, the `Nat.rec` leap kernel-checks).
The certificate is the set of Lean lemma names plus the proof term Lean accepted.
Without the toolchain present, nothing is proven and rule-based grading is
`unknown`.

Leanregate is the **exception** to Regate's trust-by-default rule (see the
[contract](../../GRADING_PROTOCOL.md)'s trust boundary): its step certificate *is*
a per-rule Lean lemma, so it cannot trust a rule and still emit a certificate — it
always proves. There is therefore no `options.verify_rules` here; proving is the
mechanism, not an opt-in. A rule outside the automatic fragment is unproven and
grades `unknown`, whatever the caller requests.

## Run / deploy

```sh
python grade.py                 # HTTP: POST /grade, GET /health  (port 8000)
python grade.py --cli           # CLI:  GradeRequest stdin -> GradeResponse stdout
make lean                       # fetch Mathlib oleans for the runtime prover
python check_induction.py --require-lean   # CI: emitted induction proofs kernel-check
docker build -f Dockerfile -t leanregate . # OCI image (build context = repo root)
```

The OCI image carries the Lean toolchain + a pruned Mathlib (the transitive
closure of the runtime import surface), so the runtime prover can establish
soundness of a transmitted ruleset live. The image is large (~9 GB) because of
Mathlib's oleans.
