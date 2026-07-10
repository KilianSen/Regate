# Integrating Regate into a learning platform

Regate is a **grading backend**, not a platform. It answers one question — *is
this student's algebraic derivation correct, against these rules?* — and returns a
structured verdict. Everything else (exercises, users, auth, persistence, the UI,
routing) belongs to the **host**. This guide is for a platform author wiring
Regate in; the canonical, versioned contract is
[`GRADING_PROTOCOL.md`](GRADING_PROTOCOL.md) — read it for the exact schema.

## The responsibility split

| The **host** owns | **Regate** owns |
|---|---|
| Exercises, the student UI, submissions | Grading a submission against a supplied ruleset |
| The **ruleset** — authored, reviewed, validated *upstream* | Checking each derivation step / equivalence / induction obligation |
| Auth, persistence, rate-limiting, i18n | Emitting a re-checkable verdict (outcome, score, certificate, witness) |
| Which backend grades which exercise | Being honest: `unknown` / `score: null` when it cannot decide |

The load-bearing one is the ruleset. Regate **trusts the ruleset it is handed** —
it does not re-validate it per request (see the trust boundary in the contract).
Rules are meant to be a code contribution in the host, reviewed and CI-checked
before deploy. If you must accept rules from a less-trusted source, set
`options.verify_rules` and Regate will re-check them (fuzzing or kernel proof)
before grading — at a latency cost.

## Two transports, same handler

Every backend exposes both. Pick per deployment; the grading logic is identical.

- **HTTP** (long-running service):
  - `POST /grade` with a `GradeRequest` JSON body → `GradeResponse` JSON.
  - `GET /health` → `{"status":"ok","backend":…,"version":…,"protocol":"1.0"}`.
- **CLI** (per-submission, for a container/test runner): a `GradeRequest` on
  stdin → a `GradeResponse` on stdout, exit 0. A malformed request → exit 2 with
  `{"error":…}`. This suits an OCI "run one container per submission" model.

```sh
# HTTP
curl -s localhost:8000/grade -H 'content-type: application/json' -d @submission.json

# CLI (one-shot container)
docker run -i --rm eggregate --cli < submission.json
```

## The backends, and choosing one

All four speak the same contract and are interchangeable **within a mode**. They
trade speed for the strength of the certificate:

| Backend | Port | Modes | Certificate | Image |
|---|---|---|---|---|
| **eggregate** | 8000 | transformation, equation, induction\* | re-checked rewrite proof | small |
| **leanregate** | 8001 | transformation, equation, induction | Lean kernel proof | ~9 GB |
| **coqregate** | 8002 | induction only | Coq kernel proof | ~1.5 GB |
| **cvc5regate** | 8003 | induction only | SMT problem (+ optional Carcara) | ~60 MB |

\* eggregate grades induction obligations but *defers* the `∀n` leap
(`equal_no_certificate`, `score: null`) — it has no kernel to certify the schema.
The formal backends certify it.

Two ways to route:

- **Static** — the exercise author picks a backend (e.g. "grade this with
  leanregate"). Simplest; what the reference workbench does.
- **Fan-out** — send the *same* request to every applicable backend and combine
  (e.g. take the fast eggregate score, upgrade to `certified` if a formal backend
  agrees). A backend out of scope for the mode returns `unknown`, so fan-out is
  safe.

A backend whose toolchain is absent in its deployment degrades to `unknown` (never
a wrong grade), so a missing Lean/Coq/cvc5 image is a coverage loss, not a hazard.

## Reading a `GradeResponse`

The full schema is in the contract; the rules that matter for a host:

- **`outcome` is authoritative, not `score`.** `proven_equal` with `score: 0`
  means "equivalent but no progress toward the target form" — it is *not* the same
  as `proven_unequal`. Route on `outcome`.
- **`score` may be `null`.** `unknown` and `equal_no_certificate` are honest
  *inconclusive* verdicts — send them to human review, do not treat as zero.
- **`certified: true`** carries a re-checkable `proof`. `equal_no_certificate` is
  "believed equal, no checked proof" — weaker, and never a zero.
- **`proven_unequal`** always carries a numeric `witness` (a counterexample) you
  can show the student.
- **`meta`** is free-form diagnostics: timing, per-rule status (`meta.ruleset`),
  induction detail (`meta.induction`). Safe to log, not to branch on.

Minimal decision for a host:

```
outcome == proven_equal      -> award score (100, or the partial score)
outcome == proven_unequal    -> 0, show witness
outcome == invalid_derivation-> 0, show the failing step
outcome in {unknown, equal_no_certificate} -> route to review (score is null)
```

## Deploying

Each backend builds from the repo root as a self-contained OCI image:

```sh
docker build -f backends/eggregate/Dockerfile -t eggregate .
docker run -p 8000:8000 eggregate            # HTTP service
```

Or run all four together for development / fan-out:

```sh
make up      # docker compose: eggregate :8000, leanregate :8001, coqregate :8002, cvc5regate :8003
```

The images vendor the canonical `GRADING_PROTOCOL.md` at build time, so a running
container is self-describing. There is no CORS on the backends — a browser host
should call them through its own proxy/gateway (the reference workbench does).

## Versioning

The contract is versioned by the top-level `protocol` field (`"1.0"`). A backend
rejects a major it does not implement. Pin the major you integrate against; minor
additions are backward-compatible.

## Conformance

`make conformance` runs a suite of fixtures through every backend's CLI and checks
they agree on the contract (including invariants like *`certified` ⇒ `proof`* and
*`proven_unequal` ⇒ `witness`*). If you write your own backend or fork one, this
is the gate that proves it still implements the same wire contract.
