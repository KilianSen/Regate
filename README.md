# Regate

A monorepo of **pluggable equational-reasoning grading backends** for the
[Artemis](https://github.com/ls1intum/Artemis) learning platform — the MS3
deliverable of the bachelor's thesis *Extending Artemis with proof-based
mathematical exercises*.

Two backends grade the same exercises by different proof engines, behind **one
wire contract** ([`GRADING_PROTOCOL.md`](GRADING_PROTOCOL.md)), so Artemis
integrates once and picks a backend per exercise — deployed as interchangeable
OCI containers via Artemis's OCI runtime.

| Backend | Engine | Soundness of rules | Strength |
|---|---|---|---|
| **[eggregate](backends/eggregate)** | egglog equality saturation + own e-graph | fuzzed (`check_rules.py`) | fast; path-independent grading, proofs, hints, partial credit |
| **[leanregate](backends/leanregate)** | Lean formal proofs | **proven** (`Basic.lean`) | trustworthy; certificates are Lean proof terms |

Same `GradeRequest` → `GradeResponse`, same MathNode JSON, same CLI + HTTP
transports, same request-supplied ruleset. The **conformance suite** proves it.

## Layout

```
GRADING_PROTOCOL.md      # the canonical contract (single source of truth)
backends/
  eggregate/             # Python e-graph backend (package, tests, Dockerfile, pyproject)
  leanregate/            # Lean formal backend (grade.py, Basic.lean, lakefile, Dockerfile)
conformance/             # fixtures + runner: both backends, one protocol
examples/                # the Appendix B exercise as a GradeRequest
docs/                    # SCALING, LIMITATIONS, egglog-proofs notes, build notes
docker-compose.yml       # run both backends together
Makefile                 # setup / test / gate / conformance / docker
```

## Quickstart

```sh
make setup          # venv + install eggregate (egglog) [needs uv]
make test           # eggregate test suite
make gate           # rule-library soundness gate (fails on an unsound rule)
make conformance    # run every fixture through BOTH backends' CLIs
make up             # docker compose: eggregate :8000, leanregate :8001
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
runs the same fixtures through both backends — so a change to either that breaks
the contract fails CI. The shared docs (`docs/`) and examples live once.

See each backend's README for internals, and `docs/` for scaling and limitations.
