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
    // ...or reference the backend's built-in catalogue by id (convenience):
    "rules": ["add_zero_right", ...] | "ALL",   // used only if "ruleset" is absent

    "reference": [<MathNode>, ...] | null, // optional sample-solution states (source..target)
    "options": { "partial_credit": true, "bound": 5, "want_hint": false,
                 "audit_rules": false, "audit_trials": 400 }
  },
  "submission": {
    "final": <MathNode> | null,           // student's final expression, and/or
    "steps": [ { "rule": "id", "path": [1,1],
                 "direction": "forward"|"reverse",
                 "kind": "A"|"B",          // A = rule application, B = Leibniz substitution
                 "equation": [<MathNode>,<MathNode>]?,  // for kind B
                 "result": <MathNode> } ]  | null
  }
}
```

A backend grades the `steps` derivation when present (per-step soundness), else
the `final` expression (endpoint equivalence). At least one must be non-null.

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
net. A formal backend (Leanregate) requires a proof per custom rule.

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
  "score": 100 | 0 | null,         // null = inconclusive -> route to review
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
- **`certified` distinguishes a checked proof from a bare yes.** `proven_equal`
  must carry a `proof` that the backend (or Artemis) can re-verify; a backend
  that can only assert equivalence returns `equal_no_certificate`.
- **`proven_unequal` must carry a `witness`** (or, for a formal backend, a
  refutation) — never returned on a mere failure to find a proof.
- Unknown rule ids, malformed MathNodes, or a missing `target` in transformation
  mode → HTTP 400 / CLI exit 2 with `{"error": "..."}`, not a misleading grade.

Versioning is via the top-level `protocol` field; backends reject majors they
don't implement.
