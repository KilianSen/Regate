# Grading Protocol v1.0

A language-agnostic JSON contract for grading a student's equational-reasoning
submission. Any backend that implements it is a drop-in grader for a host learning
platform. Four backends implement it today — **eggregate** (Python / e-graph),
**leanregate** (Lean / formal), **coqregate** (Rocq/Coq, induction only), and
**cvc5regate** (cvc5 SMT, induction only) — so they deploy as interchangeable OCI
containers, selected per exercise. The two induction certifiers answer
non-induction modes with `unknown`; interchangeability therefore holds within a
mode.

## Transports

Transport is unspecified by design. A conforming backend exposes **both**, behind
one handler, so the choice is made at deployment:

- **CLI** — read a `GradeRequest` on stdin, write a `GradeResponse` on stdout,
  exit `0`. A malformed request exits `2` with `{"error": "..."}`. Suits
  per-submission runs in a container or test runner.
- **HTTP** — `POST /grade` with a `GradeRequest` body returns a `GradeResponse`;
  `GET /health` returns `{"status": "ok", "backend": "...", "protocol": "1.0"}`.
  Suits a long-running service.

## Expressions — the MathNode tree

Expressions use the **MathNode** JSON shape: a plain typed tree any host can
produce, deliberately compatible with the reference adopter's persisted format
(Artemis's `MathNodeConverter`). A node is one of:

- a leaf — `{"type": "number" | "variable", "value": "..."}`
- an internal node — `{"type": "...", "slots": {"name": [child], ...}}`

```json
{ "type": "add", "slots": {
  "left":  [{ "type": "variable", "value": "x" }],
  "right": [{ "type": "number", "value": "0" }]
}}
```

The canonical serialization is `eggregate/model.py` (`to_json` / `from_json`).

## GradeRequest

```json
{
  "protocol": "1.0",
  "exercise": {
    "id": "add-zero",
    "mode": "transformation",
    "source": { "type": "add", "slots": { "left": [ ... ], "right": [ ... ] } },
    "target": { "type": "variable", "value": "x" },
    "ruleset": [ { "id": "add_zero_right", "lhs": ..., "rhs": ... } ],
    "options": { "partial_credit": true }
  },
  "submission": {
    "steps": [
      { "rule": "add_zero_right", "path": [], "direction": "forward",
        "kind": "A", "result": { "type": "variable", "value": "x" } }
    ]
  }
}
```

A backend grades the `steps` derivation when present (per-step soundness),
otherwise the `final` expression (endpoint equivalence). At least one must be
non-null.

### `exercise`

| Field | Type | Description |
|---|---|---|
| `id` | string | Exercise identifier. |
| `mode` | `"transformation"` \| `"equation"` \| `"induction"` | Grading mode. Induction uses the shape in [Induction mode](#induction-mode). |
| `source` | MathNode | Start expression. |
| `target` | MathNode \| null | Goal (transformation), or the equality term (equation). |
| `ruleset` | Rule[] | The rules available to the derivation. Travels in the request; see [Rules](#rules). |
| `rules` | id[] \| `"ALL"` | References a backend's built-in catalogue by id. Used **only** when `ruleset` is absent. |
| `reference` | MathNode[] \| null | Optional sample-solution states, `source`..`target`. |
| `assumptions` | Assumption[] \| null | Declared facts that discharge a guarded rule's symbolic side condition (below). |
| `hypotheses` | MathNode[] \| null | Equalities the student may use in a Type-B substitution (below). |
| `options` | Options \| null | Grading options (below). |

The **ruleset travels in the request** and is not hardcoded in the backend. Note
that leanregate has no built-in catalogue — its rules come from the API and are
proven at request time — so it ignores `rules` ids and grades them `unknown`;
supply `ruleset` inline for leanregate. Eggregate supports both.

An **assumption** is `{"kind": "nonzero" | "positive" | "integer" | "constant",
"value": <MathNode>}`. For example, `{"kind": "nonzero", "value": x}` lets the rule
`frac_self_one` (`x/x → 1`) fire; without the matching assumption such a step is
`open` and rejected.

A **hypothesis** is an equality MathNode. A Type-B (Leibniz) step whose equation is
not among the declared hypotheses is out of scope and rejected — this is what keeps
"substitute equals for equals" sound.

### `exercise.options`

| Option | Default | Description |
|---|---|---|
| `partial_credit` | `true` | Award a value-equivalent but unsimplified answer a distance-based score in `1..99` instead of binary `0`/`100`. |
| `bound` | `5` | Starting saturation bound for equivalence search. |
| `want_hint` | `false` | Return a next-step hint. |
| `ac_normalization` | `false` | Treat `+`/`·` as associative-commutative when deciding equivalence and "reached the target form" — never for step legality, where a derivation must still cite the rule it used. |
| `verify_rules` | `false` | Re-establish ruleset soundness at request time instead of taking the caller's warrant. See [Trust boundary](#trust-boundary). |
| `audit_rules` | `false` | Eggregate's older spelling of `verify_rules`. |
| `audit_trials` | `400` | Fuzzing trials when eggregate audits rules. |

### `submission`

| Field | Type | Description |
|---|---|---|
| `final` | MathNode \| null | The student's final expression (endpoint grading). |
| `steps` | Step[] \| null | The student's derivation (per-step grading). |
| `lemmas` | Lemma[] \| null | Auxiliary lemmas proven on the way. |

A **step** is:

| Field | Type | Description |
|---|---|---|
| `rule` | id | The rule applied. |
| `path` | int[] | Rewrite site, alphabetical-slot path encoding. |
| `direction` | `"forward"` \| `"reverse"` | Direction of application. |
| `kind` | `"A"` \| `"B"` | `A` = rule application; `B` = Leibniz substitution. |
| `equation` | [MathNode, MathNode] | Required for kind `B`: a hypothesis or a proven lemma. |
| `result` | MathNode | The resulting expression after the step. |

A **lemma** is `{"source": <MathNode>, "steps": [<Step>, ...]}` — a self-contained
sub-derivation from its own source `L`. Whatever it validly reduces to is `R`, and
the established `L = R` (both directions) joins the Type-B scope for later lemmas
and for the main `steps`. A lemma whose derivation does not type-check establishes
nothing, so a step relying on it is rejected.

### Induction mode

`mode: "induction"` proves `∀n. P(n)` over ℕ and uses a distinct shape:

```json
{
  "exercise": {
    "mode": "induction",
    "goal": { "type": "eq", "slots": { ... } },
    "inductionVar": "n",
    "rules": "ALL",
    "definitions": [ { "id": "pow_succ", "lhs": ..., "rhs": ... } ]
  },
  "submission": {
    "base": { "steps": [ ... ] },
    "step": { "steps": [ ... ] }
  }
}
```

| Field | Type | Description |
|---|---|---|
| `goal` | eq MathNode | `P(n)`: the equality to prove, parametrized by the induction variable. |
| `inductionVar` | string | The variable inducted over ℕ. |
| `rules` | id[] \| `"ALL"` | Catalogue rules available in the obligations. |
| `definitions` | Rule[] | **Trusted** recursive definitions, e.g. `pow(a, S n) → a·pow(a, n)`. |
| `submission.base` | `{steps}` | A derivation proving `P(0)`. |
| `submission.step` | `{steps}` | A derivation proving `P(S n)`, with the IH `P(n)` in scope. |

The grader instantiates `goal` at `0` (base) and at `S n` (step), injects the
induction hypothesis `P(n)` as a Type-B hypothesis (exact-match — sound at the
fixed `n`, never applicable at `S n`), and grades each obligation as an ordinary
equational sub-derivation.

The `base ∧ step ⟹ ∀n. P(n)` leap is the induction schema. An equational backend
has no kernel to certify it, so on success it **defers**: `equal_no_certificate`,
`score: null`, `certified: false`, with `meta.induction = {base, step, schema:
"assumed"}`. It never issues a certified pass for an inductive claim. A backend
with a proof kernel (leanregate, via `Nat.rec`) certifies the leap. Recursive
`definitions` are trusted (definitional), not fuzz-audited like algebraic rules.

## Rules

A rewrite rule, supplied as exercise data. Patterns and templates are MathNodes
that may contain **wildcards** — `{"type": "wild", "value": "a"}` — each matching
any subtree, where the same name denotes the same subtree. Side conditions guard
the rule.

```json
{
  "id": "frac_mul_cancel_left",
  "owner": "frac",
  "lhs": "(c*a)/(c*b)",
  "rhs": "a/b",
  "bidirectional": false,
  "conditions": [ { "kind": "nonzero", "var": "c" } ]
}
```

| Field | Type | Description |
|---|---|---|
| `id` | string | Rule identifier. |
| `owner` | string | Optional, cosmetic. |
| `lhs` | MathNode (with wildcards) | Pattern to match. |
| `rhs` | MathNode (with wildcards) | Template to emit. |
| `bidirectional` | bool | `true` makes the rule usable in reverse. |
| `conditions` | Condition[] | Side conditions: `{"kind": "nonzero" \| "positive" \| "integer" \| "constant" \| "notequal", "var": "c", "arg": 0}`. `arg` applies only to `notequal`. |

### Trust boundary

A ruleset is authored and formally validated once, **upstream**. Rules are a code
contribution — written, reviewed, and CI-checked in the owning platform before
deployment, never authored at runtime — and the backends validate the student's
*derivation* against that already-trusted ruleset. By default a backend takes the
caller's warrant on `exercise.ruleset` and does not re-establish it per submission;
re-proving a ruleset on every grade would cost seconds of kernel time in a
per-submission container. (A backend's built-in catalogue, where it has one, is a
test fixture, not the production rule source — that always travels in the request.)

**The caller warrants that `exercise.ruleset` is sound.** That warrant is
load-bearing, because a backend cannot recover it from anything else it checks. A
kernel that certifies the goal `∀n. 1ⁿ = 1` will also certify a derivation whose
step cites the false rule `a·b = b`, correctly applied: the goal check and the step
check are each sound, and their composition proves nothing. No verdict a backend
computes can repair a bad ruleset.

To discharge the warrant instead of assuming it, set `options.verify_rules` —
re-establish soundness at request time. Eggregate runs its random-rational fuzzer
and rejects the request with a counterexample (`unsound rule 'frac_self_one':
counterexample a=0`); the formal backends prove each rule with an automatic tactic
or solver run. Use this for rules from a source not yet validated, or in CI.
(`options.audit_rules` is eggregate's older spelling.)

Regate does **not** accept a caller-supplied proof for a rule: running an untrusted
proof script is an injection surface, and rule soundness is the caller's upstream
responsibility. A `proof` field on a rule is ignored, and a rule outside a
backend's automatic fragment is simply unproven.

A rule the kernel cannot prove — including a *guarded* rule, whose side condition
the formal backends do not model — is unproven, not false. A step citing it grades
`unknown` (route to review), never `invalid_derivation`: the student applied the
rule they were handed, and it is the exercise that is broken.

Recursive `definitions` are definitional and therefore **always** trusted, in every
mode and whatever `verify_rules` says. They are the slot for "true by declaration";
`ruleset` is not.

Leanregate is a special case: its step certificate *is* a Lean lemma proven per
rule, so it must prove the ruleset to grade at all. It cannot trust a rule, has no
`verify_rules` option, and answers `unknown` for any rule it cannot prove.

## GradeResponse

```json
{
  "protocol": "1.0",
  "backend": "eggregate",
  "backend_version": "1.0.0",
  "outcome": "proven_equal",
  "score": 100,
  "certified": true,
  "proof": [ { "rule": "add_zero_right", "path": [], "direction": "forward",
               "state": { "type": "variable", "value": "x" } } ],
  "witness": null,
  "steps": [ { "index": 0, "status": "valid", "reason": "" } ],
  "hint": null,
  "feedback": "Reached the target form.",
  "meta": { "ms": 12, "saturated": false, "progress": 1.0 }
}
```

| Field | Type | Description |
|---|---|---|
| `protocol` | `"1.0"` | Contract version. |
| `backend` | `"eggregate"` \| `"leanregate"` \| `"coqregate"` \| `"cvc5regate"` | Grading backend. |
| `backend_version` | string | Backend build version. |
| `outcome` | enum | See below. |
| `score` | `0..100` \| null | `null` = inconclusive; route to review. |
| `certified` | bool | Is the verdict backed by a re-checked proof? |
| `proof` | Step[] \| object \| null | Re-checkable certificate; shape is backend-specific (below). `[]` is a valid zero-step certificate; `null` means not certified. |
| `witness` | object \| null | Counterexample assignment for `proven_unequal`, e.g. `{"x": "0"}`. |
| `steps` | StepStatus[] \| null | Per-step results: `{"index", "status": "valid" \| "open" \| "invalid", "reason"}`. |
| `hint` | object \| null | `{"rule", "path", "direction", "remaining"}`. |
| `feedback` | string | Human-readable summary. |
| `meta` | object | Free-form diagnostics (below). |

`outcome` ranges over:

| Value | Meaning |
|---|---|
| `proven_equal` | Certified equivalent; a proof is attached. |
| `proven_unequal` | A counterexample/disproof exists; a witness is attached. |
| `equal_no_certificate` | Believed equal, but no checked proof was produced. |
| `invalid_derivation` | A submitted step is not a valid rule application. |
| `unknown` | Neither proof nor disproof within budget. |

The `proof` shape depends on the backend. Eggregate emits the rewrite chain shown
above (`{rule, path, direction, state}` per step). A formal backend attaches the
artifact it ran:

- coq / lean — `{"engine", "method", "theorem", "source": "<accepted source>"}`
- cvc5 — `{"engine", "method", "smtlib": "<problem>", "expect": "unsat"}`

`meta` is free-form diagnostics — safe to log, not to branch on. Common keys:
`ms` (timing); eggregate adds `saturated` and `progress`; the induction backends
add `induction` (`{var, status/submission, reason}`), `ruleset`
(`{id: {proven, method, detail}}`, per-rule verify status), and cvc5's `rechecked`
(whether the certificate was independently re-checked).

### Response semantics

These rules are contractual. Every backend must honour them.

- **`score` may be `null`.** `equal_no_certificate` and `unknown` are *not* zeros
  — the grader is honestly inconclusive and the caller routes to review. This is
  the protocol's false-negative defence.
- **`outcome` is authoritative; `score` is the mark.** With `partial_credit` on, a
  `score` in `1..99` means "provably equivalent, not yet in the required form". A
  `score` of `0` alongside `outcome: proven_equal` means equivalent but no
  measurable progress toward the target form — it is **not** the same as
  `proven_unequal`, and a caller must not conflate them by reading `score` alone.
- **`certified` distinguishes a checked proof from a bare assertion.**
  `proven_equal` must carry a `proof` the backend or host can re-verify; a backend
  that can only assert equivalence returns `equal_no_certificate`. An empty `proof`
  (`[]`) is a valid zero-step certificate ("already the target form"); `null` is
  not. The formal backends attach the engine artifact they ran.
- **`proven_unequal` must carry a `witness`** (or, for a formal backend, a
  refutation). It is never returned on a mere failure to find a proof.
- **Errors are not grades.** Unknown rule ids, malformed MathNodes, or a missing
  `target` in transformation mode return HTTP 400 / CLI exit 2 with
  `{"error": "..."}`, never a misleading grade.

## Versioning

The contract is versioned by the top-level `protocol` field. A backend rejects a
major version it does not implement; minor additions are backward-compatible.
