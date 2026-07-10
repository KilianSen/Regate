# cvc5regate

A pluggable grading backend for equational-reasoning exercises in learning
platforms. It implements the language-agnostic grading contract
**[`GRADING_PROTOCOL.md`](../../GRADING_PROTOCOL.md)** (`GradeRequest` →
`GradeResponse`, MathNode JSON, CLI + HTTP transports), so a host platform
integrates against that contract once and runs this backend as a self-contained
container, selected per exercise. (Artemis is the reference adopter; nothing here
depends on it.)

cvc5regate is an **induction certifier** built on the **cvc5** SMT solver. It
certifies the `base ∧ step ⟹ ∀n. P(n)` induction schema (`mode: "induction"`)
using cvc5's native structural induction, and it *disproves* false claims with a
concrete numeric witness. Its footprint is a **single ~21 MB solver binary**
(~60 MB as a Docker image), and it covers a broad fragment: equalities,
**inequalities**, **divisibility**, and goals over recursive functions.

## How it works

On `mode: "induction"` cvc5regate grades the **student's derivation**, not just
the bare theorem. `grade_derivation` runs three stages (`cvc5_induction.py` +
`cvc5_prover.py`, the single solver seam):

1. **Disprove first** (cheap): the induction variable is a *free* constant and
   cvc5's recursive-function model finder (`--fmf-fun`) searches for a
   counterexample to the goal. `sat` + a model ⇒ `proven_unequal` with the model
   as a numeric `witness` — returned straight away, before any step grading, so a
   false goal is caught even under a garbage derivation.
2. **Grade the steps**: each step of the `base` (P(0)) and inductive `step`
   (P(S n), with P(n) available) must be a valid instance of a transmitted rule
   (`step_check`, strict), and both obligations must reduce to a reflexive `t = t`.
   A fabricated step ⇒ `invalid_derivation`.
3. **Backstop the leap**: the *negated, universally-quantified* goal with cvc5's
   structural induction (`--quant-ind`). `unsat` ⇒ the theorem holds ⇒
   `proven_equal` / `certified`, with the emitted SMT-LIB attached as the `proof`.

### The ruleset is trusted by default

The transmitted `ruleset` is the caller's responsibility, validated upstream (see
the trust boundary in the [contract](../../GRADING_PROTOCOL.md)); cvc5regate grades
the derivation against it without re-proving it. `options.verify_rules` turns each
rule into its own SMT validity query first — an unsound rule then makes a step
citing it `unknown` (never `invalid_derivation`). Per-rule status is in
`meta.ruleset`. There is no proof-carrying path — a rule's `proof` field is ignored
(cvc5 cannot export a re-checkable proof for this fragment anyway). Recursive
`definitions` are always trusted. Certifying the goal alone does **not** vouch for
the rules: a false rule correctly applied to a true goal is `unknown`, never
certified.

### Why ℕ is a datatype, not `Int`

`(declare-datatype Nat ((zero) (succ (pred Nat))))`. cvc5's automated induction is
*structural* — it fires on datatype constructors. Empirically every supported goal
(`1ⁿ=1`, `3∣n³−n`, the Gauss sum, `2ⁿ≥1`) proves with the `Nat` datatype, while
the same goals with the induction variable a guarded `Int` (`(>= n 0)`) **all time
out**: cvc5 will not synthesise the `n ↦ n+1` induction on a bare integer. So the
induction variable and any exponents are the `Nat` datatype; other variables are
`Real` (the protocol's ℚ) or `Int` (integer-flavoured goals such as divisibility),
with a built-in `val : Nat → Int` coercion where a `Nat` meets arithmetic.

## Supported fragment

A single-variable induction whose goal is a **relation** — `=`, `≤`, `<`, `≥`,
`>`, or `divides` — over `+ − · pow succ` plus recursive functions supplied as
`definitions` (e.g. a `sum`). Verified end-to-end on cvc5 1.3.4 (see
`check_induction.py`):

| goal | verdict | kind |
|---|---|---|
| `1ⁿ = 1` | `proven_equal`, certified | equality |
| `3 ∣ n³ − n` | `proven_equal`, certified | divisibility |
| `2ⁿ ≥ 1` | `proven_equal`, certified | inequality |
| `2·Σᵢ = n(n+1)` | `proven_equal`, certified | recursive sum |
| `2ⁿ = n+1` (false) | `proven_unequal`, witness `n=2` | disproof |

Goals that are *translated correctly* but on which cvc5's automation times out are
reported honestly as `unknown` (never a false grade): some two-variable equalities
such as `aᵐ⁺ⁿ = aᵐ·aⁿ`, and strengthening-needing inequalities such as `2ⁿ > n`
(which need an auxiliary lemma cvc5 does not invent). This is a coverage trade,
not a soundness one.

## Trust model

`certified: true` rests on cvc5's `--quant-ind`, a **sound** induction calculus:
an `unsat` verdict certifies the claim. By default this trusts the solver's word
(no second checker), so the certificate is the solver verdict plus the emitted
SMT-LIB.

When cvc5 can export an **Alethe** proof, cvc5regate re-checks it with the
independent **Carcara** checker (`method = "alethe+carcara"`) — an external
re-verification on top of the solver. (cvc5 1.3.x cannot yet export Alethe for
proofs carrying induction skolems, so for inductive goals this path is currently a
no-op and the verdict rests on the solver; the plumbing activates automatically
for any Alethe-exportable proof and for future cvc5 releases.) Set
`CVC5REGATE_REQUIRE_RECHECK=1` for the protocol-purist stance — certify *only*
when an Alethe proof is Carcara-re-checked; an un-re-checked `unsat` then degrades
to `equal_no_certificate` (honest, not a false grade).

Honesty invariants: `unsat` ⇒ certified `proven_equal`; `sat` + model ⇒
`proven_unequal` + witness; `unknown` / timeout / outside-fragment /
toolchain-absent ⇒ `unknown`. Non-induction modes are out of scope and return
`unknown`.

## Files

- `cvc5_prover.py` — the solver seam: `cvc5_available()` / `carcara_available()`
  probes and `_run_cvc5(...)` (the single mockable call), with content-hash-cached
  `prove()` / `disprove()` and the Alethe-proof + Carcara re-check path.
  stdlib-only Python; the cvc5 (and optional Carcara) binaries are external
  processes.
- `cvc5_induction.py` — translates the induction request to SMT-LIB 2.6 (type
  inference, `define-fun-rec` definitions, negated-forall prove / free-const
  disprove sources) and maps the solver verdicts to protocol outcomes.
  `grade_derivation(ex, sub)` is the grading path (disprove-first, grade the
  student's steps, backstop the leap); `certify(ex)` is the bare-goal oracle it
  calls; `prove_ruleset(ex)` re-solves the ruleset under `verify_rules`.
- `step_check.py` — strict rule-instance checker for the student's steps (shared
  shape with coqregate's, but a deliberately independent copy).
- `grade.py` — protocol entrypoint (CLI + HTTP), `backend = "cvc5regate"`.
- `check_induction.py` — live harness; `--require-cvc5` runs the emitted goals
  through real cvc5 and asserts the MUST_PASS set settles.
- `tests/test_cvc5_prover.py` — translation / wiring tests against a stubbed
  solver seam, plus an availability-gated real-cvc5 run.

## Run / deploy

```sh
python grade.py                 # HTTP: POST /grade, GET /health  (port 8000)
python grade.py --cli           # CLI:  GradeRequest stdin -> GradeResponse stdout
python check_induction.py --require-cvc5   # CI: emitted goals settle in real cvc5
python tests/test_cvc5_prover.py           # unit tests (stub the solver) + gated real run
docker build -f Dockerfile -t cvc5regate . # OCI image (build context = repo root)
```

The cvc5 binary is found on `PATH`, or via `CVC5REGATE_CVC5`; the optional Carcara
checker via `CVC5REGATE_CARCARA`. Timeouts: `CVC5REGATE_TIMEOUT` (prove, default
20 s), `CVC5REGATE_DISPROVE_TIMEOUT` (default 5 s). Install cvc5 with
`pip install cvc5` (Python wheel ships the binary) or download the single static
binary from the [cvc5 releases](https://github.com/cvc5/cvc5/releases).
