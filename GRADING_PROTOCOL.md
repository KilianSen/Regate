# Grading Protocol v1.1

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
  `GET /health` returns `{"status": "ok", "backend": "...", "protocol": "1.1"}`.
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

### `apply` — named function application (since 1.1)

A function call is an `apply` node — the one internal node whose `args` slot holds an **ordered
list** of children rather than a fixed set of named single-child slots:

```json
{ "type": "apply", "value": "fact_aux", "slots": { "args": [
  { "type": "variable", "value": "x" },
  { "type": "variable", "value": "n" }
]}}
```

`apply` is **n-ary and named** (`value` is the function name), **not** curried and **not** an opaque
symbol. It carries no meaning of its own: the function is defined by recursive `definitions` rules in
the request (e.g. `fact_aux(x, 0) → x`, `fact_aux(x, S n) → fact_aux(x·(S n), n)`), which a backend
compiles to a native recursive definition. A backend that does not implement `apply` rejects the
request per [Unimplemented vocabulary](#unimplemented-vocabulary).

## GradeRequest

```json
{
  "protocol": "1.1",
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
| `goal` | relation MathNode | `P(n)`, parametrized by the induction variable. Usually an `eq`; a backend **may** also accept `le`/`lt`/`ge`/`gt` or `divides` (see below). |
| `inductionVar` | string | The variable inducted over the induction datatype (ℕ by default). |
| `datatype` | Datatype \| null | *(since 1.1, optional)* The type of `inductionVar`. Absent ⇒ ℕ (`zero`/`succ`). See [Datatype induction](#datatype-induction). |
| `domain` | `"int"` \| `"rat"` \| null | *(since 1.1, optional)* Numeric domain of the free variables — ℤ or ℚ. Defaults to ℚ (or ℤ for a `divides` goal). |
| `rules` | id[] \| `"ALL"` | Catalogue rules available in the obligations. |
| `definitions` | Rule[] | **Trusted** recursive definitions, e.g. `pow(a, S n) → a·pow(a, n)`. |
| `submission.base` | `{steps}` | A derivation proving `P` at the base constructor (`0` / `nil`). |
| `submission.step` | `{steps}` | A derivation proving `P` at the step constructor (`S n` / `cons h t`), with the IH in scope. |

The `divides` relation (*since 1.1*) is `{"type": "divides", "slots": {"divisor": [<number>],
"value": [<MathNode>]}}`, read `divisor | value`. Non-`eq` goal relations (`le`/`lt`/`ge`/`gt`/
`divides`) and `domain` are optional capabilities: a backend that does not implement them rejects the
request per [Unimplemented vocabulary](#unimplemented-vocabulary) rather than guessing. cvc5regate
implements all of them; the other backends grade `eq` goals only.

#### Datatype induction

By default the induction variable ranges over ℕ. `exercise.datatype` (*since 1.1*) lets it range over
another inductive datatype — lists, binary trees — so an accumulator function can be verified by
structural induction over its data:

```json
"datatype": {
  "name": "Lst",
  "constructors": [
    { "name": "nil",  "fields": [] },
    { "name": "cons", "fields": [ { "name": "h", "sort": "int" }, { "name": "t", "sort": "Lst" } ] }
  ]
}
```

A constructor field whose `sort` is the datatype's own name is a **recursive** position and yields an
inductive hypothesis; other fields carry a numeric sort (`"int"`/`"rat"`). Exactly **one** non-recursive
("base", e.g. `nil`) and **one** recursive ("step", e.g. `cons`) constructor are supported — ℕ, lists,
and binary trees — deliberately short of a general datatype engine. Non-ℕ constructors travel as
[`apply`](#apply--named-function-application-since-11) nodes (`nil`, `cons h t`); ℕ keeps its legacy
`0`/`succ` forms. The `base`/`step` submission derivations are then taken at those two constructors, with
one IH per recursive field (`P(t)` for a list; `P(l)` and `P(r)` for a tree). The recursion argument of a
function is whichever argument the descriptor's constructors are matched against — it need not be last
(`sum l a` recurses on the *first* argument).

A step constructor with **more than one** recursive field (a binary tree's `node l v r`) yields one IH per
field — `P(l)` *and* `P(r)` — both built server-side and both in scope for the step's kind-`B` substitutions;
a kind-`B` step names which instance it uses via its `equation`, and the grader checks it against each IH.

`datatype` is an optional capability: a backend that does not implement it rejects the request per
[Unimplemented vocabulary](#unimplemented-vocabulary). cvc5regate implements ℕ, lists, and binary trees
(one base + one recursive constructor, up to two recursive fields); the other backends grade ℕ induction
only. A **false** datatype goal whose counterexample is a constructor term (not a number) returns `unknown`
rather than a `proven_unequal` without a reportable numeric witness (the `proven_unequal ⇒ witness`
invariant fails safe).

The grader instantiates `goal` at `0` (base) and at `S n` (step), injects the
induction hypothesis `P(n)` as a Type-B hypothesis, and grades each obligation as
an ordinary equational sub-derivation. The induction variable `n` stays fixed in
the IH (it is sound at `n`, never at `S n`).

**Generalized induction hypothesis (*since 1.1*).** When the goal has free
variables besides the induction variable — the *accumulators* of a tail-recursive
function, e.g. `x` in `fact_aux x n = x·fact n` — the IH is **universal in those
accumulators**: `∀x⃗. P(x⃗, n)`, not just `P(x⃗, n)` at the goal's own `x⃗`. A kind-`B`
step may therefore instantiate the IH at a **shifted** accumulator (the inductive
step of `fact_aux x (S n)` unfolds to `fact_aux (x·(S n)) n`, then applies the IH at
`x·(S n)`). The step's `equation` must be that concrete instance `(P.lhs σ, P.rhs σ)`;
the backend recovers `σ` by matching the IH's LHS against the rewritten subterm and
re-checks the instance. This is sound only because the certifying backend proves the
**co-quantified** statement `∀x⃗ n. P(x⃗, n)` — the same universal the IH claims (a
backend that induction-certifies the goal must quantify the induction variable such
that induction is taken over it, not over an accumulator). With no accumulators this
reduces to the exact-match IH, so `1ⁿ = 1`-style goals are unaffected. It is an
optional capability: a backend that cannot translate the goal's vocabulary (e.g. the
`apply` node) declines per [Unimplemented vocabulary](#unimplemented-vocabulary) with
`unknown` — **never** `invalid_derivation` on a derivation it never certified.
cvc5regate implements it; the other backends grade fixed-`n` IHs only.

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
  "protocol": "1.1",
  "backend": "eggregate",
  "backend_version": "0.1.0",
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
| `protocol` | `"1.1"` | Contract version. Backends accept any `1.x` request (minor additions are backward-compatible). |
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

## Unimplemented vocabulary

No backend is required to implement every term node, goal relation, or induction datatype. A backend
that receives a **well-formed** request using vocabulary it does not implement — an `apply` node, a
`divides` goal, a non-ℕ induction datatype — **declines** it in one of two conformant ways, depending
on where it fails:

- **Cannot parse it → malformed.** A backend whose MathNode reader has no representation for the node
  rejects the request: HTTP 400 / CLI exit 2 with `{"error": "..."}`, exactly as for a syntactically
  broken MathNode. (eggregate does this for `apply` — its fixed-arity term model cannot hold an n-ary
  `args` slot.)
- **Parses it but cannot grade it → `unknown`.** A backend that accepts the generic node shape but
  cannot translate it to its kernel returns a valid `GradeResponse` with `outcome: "unknown"`,
  `score: null`. (leanregate and coqregate do this for `apply`.)

Both are honest declines: the host routes to review either way, and neither is a wrong grade. What is
forbidden is a **wrong grade** or an uncaught crash (HTTP 500 / exit 1). This is distinct from, but
lands in the same place as, **mode-decline** — a backend that understands the request but has no kernel
for its mode (an induction certifier asked to grade a `transformation`) always returns `unknown`.

A host selecting a backend, or fanning out across several, treats a decline (400 *or* `unknown`) as a
signal to route elsewhere — never as a submission error surfaced to the student. A backend **may**
advertise the vocabulary it implements via `/health` so the host routes without a probe round-trip;
absent that, discovery is by *try → decline*.

## Versioning

The contract is versioned by the top-level `protocol` field. A backend rejects a
major version it does not implement; minor additions are backward-compatible. A
`1.1` backend therefore accepts a `1.0` request unchanged (the check compares the
major version only), and a host may send either.

### Changelog

- **1.1** — documents the `apply` term node (n-ary named function application, §Expressions),
  the `divides` relation and `exercise.domain` in [Induction mode](#induction-mode), the
  generalized (accumulator-universal) inductive hypothesis, [datatype induction](#datatype-induction)
  (`exercise.datatype` — lists and trees), and the
  [Unimplemented vocabulary](#unimplemented-vocabulary) rule. All additive; a `1.0` request grades
  identically.
- **1.0** — initial contract.
