# Regate

A monorepo of **pluggable equational-reasoning grading backends** for the
[Artemis](https://github.com/ls1intum/Artemis) learning platform — the MS3
deliverable of the bachelor's thesis *Extending Artemis with proof-based
mathematical exercises*.

Four backends grade the same exercises by different proof engines, behind **one
wire contract** ([`GRADING_PROTOCOL.md`](GRADING_PROTOCOL.md)), so Artemis
integrates once and picks a backend per exercise — deployed as interchangeable
OCI containers via Artemis's OCI runtime.

| Backend | Engine | Scope | Notes |
|---|---|---|---|
| **[eggregate](backends/eggregate)** | egglog equality saturation + own e-graph | full derivation grading: proofs, hints, partial credit | fast; per-step soundness by construction |
| **[leanregate](backends/leanregate)** | Lean formal proofs | full derivation grading + induction | proves each transmitted rule with the Lean kernel at request time (its certificate *is* the per-rule lemma); heavy image (~9 GB) |
| **[coqregate](backends/coqregate)** | Coq `induction` (`coqc`) | induction over ℕ (specialist) | kernel-certified; no Mathlib; ~1.5 GB image; attaches the accepted Coq source |
| **[cvc5regate](backends/cvc5regate)** | cvc5 SMT (`--quant-ind`) | induction (specialist) — incl. inequalities & divisibility | broadest induction coverage; disproves with a numeric witness; ~60 MB image; trusts the solver (optional Carcara re-check) |

Same `GradeRequest` → `GradeResponse`, same MathNode JSON, same CLI + HTTP
transports, same request-supplied ruleset. The **conformance suite** proves it.

## Where rules come from, and who validates them

Regate is an **interface**. The rules an exercise uses are not built into any
backend — they travel in each request (`exercise.ruleset`). Their source is an
**upstream code contribution**: rules are written, code-reviewed, and CI-checked
in the owning platform *before* they are ever deployed, never authored at runtime.

So rule soundness is the **caller's** responsibility, established once upstream —
not something a backend re-checks on every submission. Each backend therefore
**trusts the transmitted ruleset by default** and grades the student's derivation
against it. A backend cannot recover a bad ruleset anyway: certifying a true goal
from steps that cite a *false* rule proves nothing, so trust has to be earned
before the request, not during it. See the trust boundary in
[`GRADING_PROTOCOL.md`](GRADING_PROTOCOL.md).

Two consequences worth knowing up front:

- The `options.verify_rules` flag lets a caller ask a backend to *re-establish*
  soundness at request time anyway (eggregate fuzzes rules with random rationals;
  the formal backends prove them) — a self-check for a not-yet-trusted source or CI.
- Regate never runs a caller-supplied proof for a rule (that would be an injection
  surface); a rule outside a backend's automatic fragment is simply unproven.

The **built-in catalogue** (`backends/eggregate/eggregate/catalogue.py`, the 29
Table-4 rules) is **only Regate's own test/demo/gate fixture** — it is not the
production rule source, which is always the request.

## Layout

```
GRADING_PROTOCOL.md      # the canonical contract (single source of truth)
backends/
  eggregate/             # Python e-graph backend (package, tests, Dockerfile, docs/)
  leanregate/            # Lean formal backend (grade.py, lakefile, Dockerfile)
  coqregate/             # Coq induction certifier (grade.py, Dockerfile)
  cvc5regate/            # cvc5 SMT induction certifier (grade.py, Dockerfile)
conformance/             # fixtures + runner: one protocol, every backend
examples/                # the Appendix B exercise as a GradeRequest
docker-compose.yml       # run the backends together
Makefile                 # setup / test / gate / conformance / coq / cvc5 / docker
```

## Quickstart

```sh
make setup          # venv + install eggregate (egglog) [needs uv]
make test           # eggregate test suite
make gate           # soundness gate over the built-in TEST catalogue (fails on an unsound rule)
make conformance    # run every fixture through its target backends' CLIs
make up             # docker compose: eggregate :8000, leanregate :8001, coqregate :8002, cvc5regate :8003
```

Try a request by hand:

```sh
docker compose up --build
curl -s localhost:8000/grade -d @examples/appendix-b.json | python3 -m json.tool
curl -s localhost:8001/health
```

## Why a monorepo

The backends are independent deployables but share one thing that must never
drift: **the protocol**. Keeping them together gives a single canonical
`GRADING_PROTOCOL.md` and a single **conformance suite** (`conformance/`) that
runs the same fixtures through every backend — so a change to any of them that
breaks the contract fails CI. The contract and the examples live once.

See each backend's README for internals; eggregate's `backends/eggregate/docs/`
covers scaling and limitations.
