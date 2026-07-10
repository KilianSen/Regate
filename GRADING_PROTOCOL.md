# Equational-reasoning grading protocol (v1)

A language-agnostic JSON contract for grading a student's equational-reasoning
submission. Any backend that speaks it is a drop-in grader for Artemis; today
**Eggregate** (Python / e-graph) and **Leanregate** (Lean / formal) both
implement it, so they can be deployed as interchangeable OCI containers and
selected per exercise.

Transport is deliberately unspecified — a conforming backend exposes **both**:

- **CLI**: read a `GradeRequest` JSON on stdin, write a `GradeResponse` JSON on
  stdout, exit 0. (Suits per-submission OCI runs, like Artemis test containers.)
- **HTTP**: `POST /grade` with a `GradeRequest` body → `GradeResponse`; `GET
  /health` → `{"status":"ok","backend":..,"protocol":"1.0"}`. (Suits a
  long-running service.)

Same handler behind both, so the choice is a deploy-time decision.

## Expressions

Expressions use the persisted **MathNode** JSON shape (Artemis
`MathNodeConverter`): `{"type","value"?}` for `number`/`variable`, otherwise
`{"type","slots":{name:[child], ...}}`. See `eggregate/model.py`
(`to_json`/`from_json`).

## GradeRequest

```jsonc
{
  "protocol": "1.0",
  "exercise": {
    "id": "string",
    "mode": "transformation" | "equation",
    "source": <MathNode>,                 // start expression
    "target": <MathNode> | null,          // goal (transformation); equality term (equation)

    // The ruleset travels in the request — it is NOT hardcoded in the backend.
    // Either supply full instructor-authored definitions inline:
    "ruleset": [ <Rule>, ... ],
    // ...or reference a backend's built-in catalogue by id (convenience):
    "rules": ["add_zero_right", ...] | "ALL",   // used only if "ruleset" is absent
    // NOTE: leanregate has NO built-in catalogue (rules come from the API and are
    // proven at request time); it ignores "rules" ids and grades them `unknown`.
    // Supply "ruleset" inline for leanregate. Eggregate supports both.

    "reference": [<MathNode>, ...] | null, // optional sample-solution states (source..target)

    // Declared facts that discharge a guarded rule's symbolic side condition,
    // e.g. {"kind":"nonzero","value": x} lets `frac_self_one` (x/x → 1) fire.
    // Without the matching assumption such a step is `open` and rejected.
    "assumptions": [ { "kind": "nonzero"|"positive"|"integer"|"constant",
                       "value": <MathNode> }, ... ],
    // Given equalities the student may use in a Type-B substitution. A kind-B
    // step whose equation is not among these is out of scope (rejected) — this
    // is what keeps "substitute equals for equals" sound.
    "hypotheses": [ <eq MathNode>, ... ],

    // partial_credit (default true): award a value-equivalent but unsimplified
    //   answer a distance-based score in 1..99 instead of a binary 0/100.
    // bound (default 5): the starting saturation bound for equivalence search.
    // ac_normalization (default false): treat +/· as associative-commutative when
    //   deciding equivalence and "reached the target form" — never for step
    //   legality, where a derivation must still cite the rule it used.
    "options": { "partial_credit": true, "bound": 5, "want_hint": false,
                 "ac_normalization": false,
                 "audit_rules": false, "audit_trials": 400 }
  },
  "submission": {
    "final": <MathNode> | null,           // student's final expression, and/or
    "steps": [ { "rule": "id", "path": [1,1],
                 "direction": "forward"|"reverse",
                 "kind": "A"|"B",          // A = rule application, B = Leibniz substitution
                 "equation": [<MathNode>,<MathNode>]?,  // for kind B (a hypothesis or a proven lemma)
                 "result": <MathNode> } ]  | null,

    // Auxiliary lemmas proven on the way (`have L = R := <derivation>`). Each is
    // a self-contained sub-derivation from its own `source` L; whatever it validly
    // reduces to is R, and the established `L = R` (both directions) joins the
    // Type-B scope for later lemmas and the main `steps`. A lemma whose derivation
    // does not type-check establishes nothing -> a step relying on it is rejected.
    "lemmas": [ { "source": <MathNode>, "steps": [ <step>, ... ] }, ... ]
  }
}
```

A backend grades the `steps` derivation when present (per-step soundness), else
the `final` expression (endpoint equivalence). At least one must be non-null.

### Induction mode

`mode: "induction"` proves `∀n. P(n)` over ℕ. It uses a different shape:

```jsonc
"exercise": { "mode": "induction",
  "goal": <eq MathNode>,        // P(n): the equality to prove, parametrized by …
  "inductionVar": "n",          // …this variable (inducted over ℕ)
  "rules": [...] | "ALL",       // catalogue rules available in the obligations
  "definitions": [ <Rule>, ... ] }  // TRUSTED recursive definitions (e.g. pow(a,S n)→a·pow(a,n))
"submission": {
  "base": { "steps": [...] },   // a derivation proving P(0)
  "step": { "steps": [...] } }  // a derivation proving P(S n), with the IH P(n) in scope
```

The grader instantiates `goal` at `0` (base) and at `S n` (step), injects the
induction hypothesis `P(n)` as a **Type-B hypothesis** (exact-match — sound at the
fixed `n`, never applicable at `S n`), and grades each obligation as an ordinary
equational sub-derivation. **The `base ∧ step ⟹ ∀n.P(n)` leap is the induction
schema.** An e-graph/equational backend has no kernel to certify it, so on success
it **defers**: `equal_no_certificate`, `score: null`, `certified: false`, with
`meta.induction = {base, step, schema:"assumed"}` — it never issues a certified
pass for an inductive claim. A backend with a proof kernel (leanregate, via
`Nat.rec`) is what can certify the leap. Recursive `definitions` are trusted
(definitional), not fuzz-audited like algebraic rules.

## Rule

A rewrite rule, as exercise data. Patterns/templates are MathNodes that may
contain **wildcards** — `{"type":"wild","value":"a"}` — matching any subtree
(same name ⇒ same subtree). Side conditions guard the rule.

```jsonc
{
  "id": "frac_mul_cancel_left",
  "owner": "frac",                        // optional, cosmetic
  "lhs": <MathNode-with-wildcards>,        // pattern, e.g. (c*a)/(c*b)
  "rhs": <MathNode-with-wildcards>,        // template, e.g. a/b
  "bidirectional": false,                  // true = usable in reverse
  "conditions": [ { "kind": "nonzero" | "positive" | "integer"
                          | "constant" | "notequal",
                    "var": "c", "arg": 0 } ]   // arg only for "notequal"
}
```

**Custom rules are untrusted.** A backend SHOULD be able to audit a supplied
ruleset for soundness (Eggregate: `options.audit_rules` runs the random-rational
fuzzer and rejects any rule that is not a definedness-preserving equality, with a
counterexample). Authoring-time auditing is preferred; per-request is the safety
net.

**Every formal backend MUST prove each transmitted rule before certifying with
it.** This is not optional, and it is not implied by kernel-checking the goal: a
kernel that certifies only `∀n. 1ⁿ = 1` will happily certify a derivation whose
step cites the false rule `a·b = b`, correctly applied. Applying a false rule
correctly proves nothing. A rule the kernel cannot prove — including a *guarded*
rule, whose side condition the formal backends do not model — is **unproven, not
false**: a step citing it grades `unknown` (route to review), never
`invalid_derivation`. Recursive `definitions` are definitional and therefore
trusted; algebraic rules are not.

## GradeResponse

```jsonc
{
  "protocol": "1.0",
  "backend": "eggregate" | "leanregate",
  "backend_version": "string",
  "outcome": "proven_equal"        // certified equivalent (proof attached)
           | "proven_unequal"      // a counterexample/disproof exists (witness)
           | "equal_no_certificate"// believed equal, no checked proof produced
           | "invalid_derivation"  // a submitted step is not a valid rule application
           | "unknown",            // neither proof nor disproof within budget
  "score": 0..100 | null,          // null = inconclusive -> route to review
  "certified": true | false,       // is the verdict backed by a re-checked proof?
  "proof":   [ { "rule","path","direction","state": <MathNode> } ] | null,
  "witness": { "x": "0", ... } | null,            // counterexample (proven_unequal)
  "steps":   [ { "index": 0, "status": "valid"|"open"|"invalid", "reason": "" } ] | null,
  "hint":    { "rule","path","direction","remaining": 2 } | null,
  "feedback": "human-readable string",
  "meta": { "ms": 12, "saturated": false, "progress": 0.67 }
}
```

### Contract notes

- **`score` may be `null`.** `equal_no_certificate` and `unknown` are *not*
  zeros — the grader is honestly inconclusive; the caller routes to review. This
  is the false-negative defence and every backend must honour it.
- **`outcome` is authoritative; `score` is the mark.** With `partial_credit` on,
  a `score` in `1..99` means "provably equivalent, not yet in the required form".
  A `score` of `0` alongside `outcome: proven_equal` means equivalent but *no
  measurable progress* toward the target form — it is **not** the same as
  `proven_unequal`, and a caller must not conflate them by reading `score` alone.
- **`certified` distinguishes a checked proof from a bare yes.** `proven_equal`
  must carry a `proof` that the backend (or Artemis) can re-verify; a backend
  that can only assert equivalence returns `equal_no_certificate`. An *empty*
  `proof` (`[]`) is a valid zero-step certificate ("already the target form");
  `null` is not. The formal backends attach the engine artifact they ran — the
  accepted Lean/Coq source, or the SMT-LIB problem plus the expected verdict.
- **`proven_unequal` must carry a `witness`** (or, for a formal backend, a
  refutation) — never returned on a mere failure to find a proof.
- Unknown rule ids, malformed MathNodes, or a missing `target` in transformation
  mode → HTTP 400 / CLI exit 2 with `{"error": "..."}`, not a misleading grade.

Versioning is via the top-level `protocol` field; backends reject majors they
don't implement.
