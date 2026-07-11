# Regate

**Pluggable equational-reasoning grading backends for learning platforms.**
Regate grades a student's algebraic derivation — a chain of rewrites, an
equivalence, or a proof by induction — behind **one language-agnostic wire
contract** ([`GRADING_PROTOCOL.md`](GRADING_PROTOCOL.md)). A host platform
integrates against the contract *once* and picks a backend per exercise;
backends are self-contained OCI containers with a CLI and an HTTP transport, so
they drop into any container/test runner.

Four interchangeable backends grade the same exercises by different proof
engines, from a fast e-graph to formal kernels — trade speed for the strength of
the certificate without changing the integration. Rules and exercises belong to
the **host**; Regate is the grader. See **[Integrating Regate](INTEGRATION.md)**
for the plug-in guide.

> **Origin.** Regate began as the MS3 deliverable of the bachelor's thesis
> *Extending Artemis with proof-based mathematical exercises*.
> [Artemis](https://github.com/ls1intum/Artemis) is the **reference adopter** —
> the MathNode JSON is deliberately compatible with its persisted format — but
> nothing here depends on Artemis, and the contract is platform-neutral.

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

## Soundness model — for a theory / math reader

**The verdict is a four-valued judgement, not a boolean.** A `GradeResponse`'s
`outcome` ranges over `{proven_equal, proven_unequal, equal_no_certificate,
unknown}`, the last two carrying `score: null`. The design deliberately refuses to
collapse "not proved within budget" into "false" — that conflation is the classic
false-negative, and the four-valued codomain is what avoids it. Two dual failure
modes are defended **separately**: a false *positive* (unsound credit) is defended
by requiring a **re-checked certificate**, never a bare oracle bit — `certified:
true ⟹ ∃` a re-verifiable proof object; a false *negative* (an unfair zero) is
defended by mapping every inconclusive judgement to `score: null` (review), never
`0`. Dually, `proven_unequal ⟹ ∃` a concrete witness (a ground assignment /
model) — it is never returned on a mere search failure. The **load-bearing
invariant is soundness by abstention**: no backend ever emits a false certified
pass; where its method cannot decide, it abstains.

**Trusted base, in ascending formality.** What a `certified` verdict rests on
differs by backend, and the certificate's re-checkability tracks it:

| Backend | Trusted base (TCB) | Certificate | Re-checkable by a third party? |
|---|---|---|---|
| eggregate | step validator + exact-ℚ evaluator + the fuzzer's coverage | a rewrite proof, re-validated by an independent kernel (`recheck_proof`) | yes (replay the steps) |
| cvc5regate | cvc5's induction *calculus* (sound) + the solver *implementation* (trusted) | the SMT-LIB problem (+ Alethe/Carcara when exportable) | re-solve; independent re-check pending cvc5 proof export |
| coqregate | the Coq kernel (stdlib `ring`/`field`/`lia`) | the kernel-checked `.v` source | yes (run `coqc`) |
| leanregate | the Lean kernel + Mathlib | the accepted proof term / lemma names | yes (run `lean`) |

**Soundness is relative to that base; completeness is not claimed.** eggregate is
sound *up to the rule theory and a saturation bound* — its equivalence oracle is
one-sided (`False` means "not proved within the bound," not "unequal"), and rule-
library soundness is **empirical** (random-rational fuzzing, `audit.py`), not a
proof. The kernel backends are sound up to a small, standard TCB (a proof
assistant's checker). All four are **incomplete**, and incompleteness is *always*
surfaced as `unknown`, never as a wrong grade: eggregate by its bounded/forward
search, the certifiers by abstaining outside their fragment, cvc5 by timing out on
goals that need a strengthening it will not invent.

**Two standing assumptions.** (i) *Rule soundness* — every backend assumes the
transmitted ruleset consists of sound (definedness-preserving) identities,
discharged **upstream** (see above); this is an explicit precondition, not a
theorem a backend proves, because a certified goal derived from steps citing a
false rule proves nothing. (ii) *Domain* — the semantics is exact rational
arithmetic (ℚ) as a **partial** algebra: division by zero is *undefined*, not an
error or a lie, and a witness is only reported where both sides are defined.
(coqregate proves rational equality as the setoid `Qeq` / `==`, not Leibniz `=` —
the notion `ring`/`field` actually discharge.)

## Layout

```
GRADING_PROTOCOL.md      # the canonical contract (single source of truth)
INTEGRATION.md           # host-facing guide: plug Regate into a platform
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

## Contribution Observability
![ontribution](/docs/contrib.svg)
