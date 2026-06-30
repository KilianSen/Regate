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
| **[eggregate](backends/eggregate)** | egglog equality saturation + own e-graph | full derivation grading: proofs, hints, partial credit | fast; rule soundness *fuzzed* (`check_rules.py`) |
| **[leanregate](backends/leanregate)** | Lean formal proofs | full derivation grading + induction | rules come from the API, *proven by the Lean kernel* at request time; certificates are Lean proof terms; heavy image (~9 GB) |
| **[coqregate](backends/coqregate)** | Coq `induction` (`coqc`) | induction over ℕ (specialist) | kernel-certified like leanregate but no Mathlib; ~1.5 GB image |
| **[cvc5regate](backends/cvc5regate)** | cvc5 SMT (`--quant-ind`) | induction (specialist) — incl. inequalities & divisibility | broadest induction coverage; disproves with a numeric witness; ~60 MB image; trusts the solver (optional Carcara re-check) |

Same `GradeRequest` → `GradeResponse`, same MathNode JSON, same CLI + HTTP
transports, same request-supplied ruleset. The **conformance suite** proves it.

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
make gate           # rule-library soundness gate (fails on an unsound rule)
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
