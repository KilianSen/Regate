# cvc5regate

A pluggable grading backend for equational-reasoning exercises in learning
platforms. It implements the language-agnostic grading contract
**[`GRADING_PROTOCOL.md`](../../GRADING_PROTOCOL.md)** (`GradeRequest` →
`GradeResponse`, MathNode JSON, CLI + HTTP transports), so a host platform
integrates against that contract once and runs this backend as a self-contained
container, selected per exercise. (Artemis is the reference adopter; nothing here
depends on it.)

cvc5regate is an **induction certifier** built on the **cvc5** SMT solver that
**also grades ordinary `transformation` and `equation` exercises** — the one
non-eggregate backend that is a *general* grader, not just a specialist. It
certifies the `base ∧ step ⟹ ∀n. P(n)` induction schema (`mode: "induction"`)
using cvc5's native structural induction, grades step-by-step transformation
derivations, decides `source ≡ target` equivalence with an SMT oracle, and
*disproves* false claims with a concrete numeric witness. Its footprint is a
**single ~21 MB solver binary** (~60 MB as a Docker image), and it covers a broad
fragment: equalities, **inequalities**, **divisibility**, and goals over recursive
functions.

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

### Non-induction: `transformation` / `equation`

On `mode: "transformation"` (or `"equation"`) cvc5regate grades with two engines,
strongest first (`cvc5_equiv.py` + `_grade_equational` in `grade.py`):

1. **Certify the derivation** (if `steps` are submitted): each step must be a valid
   instance of a transmitted rule (`step_check.check_derivation`, the same strict
   matcher as the induction obligations). A valid chain reaching the target *form*
   is `proven_equal` / certified with the ordered rule instances as the proof —
   **no solver call needed** (rules are trusted by default). A fabricated step ⇒
   `invalid_derivation`.
2. **The SMT equivalence oracle** (`decide_equivalence`) grades the endpoint the
   student reached — used directly for a `final`-only submission, and as the
   backstop when a derivation is valid-but-unfinished or cannot be certified
   symbolically (an unknown/unproven rule, a Leibniz step). Disprove-first: a `sat`
   model of `source ≠ target` ⇒ `proven_unequal` + numeric witness. Then prove:
   `source = target` as a *plain* validity query (`prove_equiv`, no `--quant-ind`)
   ⇒ `unsat` ⇒ `proven_equal`. Reaching the target form is 100; an equivalent but
   unsimplified answer earns partial credit (a structural-distance score, floored
   at 1 for genuine progress; `options.partial_credit: false` makes it binary).

Outcome/score semantics mirror **eggregate** (the reference general grader), so the
two are interchangeable on non-induction exercises. The oracle needs *no* ruleset —
it can prove e.g. `(x+1)(x-1) ≡ x·x−1` that the symbolic backends cannot without a
distributivity rule in the request (fixture `31`). Non-inductive equivalence
queries *can* usually export an Alethe proof, so a `proven_equal` here may be
Carcara-re-checked (`method = "alethe+carcara"`, `meta.equiv.rechecked: true`).

### Declared assumptions scope every query

`exercise.assumptions` reaches **every** SMT path, not just `steps` — the induction
prove/disprove sources and the equivalence oracle's both. SMT-LIB leaves `(/ x 0)`
underspecified, so without them the counterexample search returns `x = 0` as a
"counterexample" to `x/x = 1` even when the exercise declared `x ≠ 0` — a wrong
grade on a correct answer, and a contradiction of eggregate on the same request
(fixture `34`). They are equally load-bearing on the prove side: `x/x = 1` is a
theorem *exactly* under `x ≠ 0`.

- **Disprove**: asserted as constraints on the model, so the search only ranges over
  points the exercise admits.
- **Prove**: an antecedent — `∀x. x ≠ 0 → x/x = 1`.
- **Translated kinds**: `nonzero` (`(not (= t 0))`), `positive` (`(> t 0)`),
  `integer` (`(is_int t)`; trivially true in the ℤ domain).
- **`constant` and any unknown kind DECLINE**: `constant` is a syntactic property of
  the matched subterm ("is a numeral", cf. eggregate's `conditions.discharge`), not a
  constraint on a numeric model, so it has no faithful SMT reading. An assumption
  this backend cannot translate makes the whole query `unknown` — never silently
  dropped, which is exactly what produced the wrong grade.
- **Fail-safe**: before any `proven_unequal`, the witness must be *shown* to satisfy
  the declared assumptions (`witness_respects_assumptions`, re-evaluated over exact
  rationals). Anything unverifiable degrades to `unknown`, mirroring the D4
  `_usable_witness` gate. A malformed assumption is a 400, not a crash.
- **Not** applied to *rule verification*: `options.verify_rules` asks whether a rule
  is valid **as transmitted**, and a rule's wildcards are not the exercise's
  variables, so `build_rule_source` takes assumptions only on explicit opt-in
  (`use_assumptions=True`, used by the equivalence oracle). The trust boundary is
  unchanged.

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

### Named functions (`apply`) — the operator escape hatch

A function call is an `apply` node and the function itself travels as `definitions`,
so a host adds a new operator as **data** rather than as a new MathNode type. Two
definition shapes are accepted, told apart by whether the left-hand side matches a
datatype constructor:

| shape | example `definitions` | emitted |
|---|---|---|
| recursive | `sum(0) → 0`, `sum(S k) → S k + sum(k)` | `define-fun-rec` over a `match` |
| non-recursive | `avg(a, b) → (a+b)/2` | plain `define-fun` (a macro) |

A recursive function needs **both** a base-constructor and a step-constructor rule,
recursing on the same argument position in both (any position; the other arguments
are accumulators and must be named identically in the two rules). A non-recursive
operator is **one** equation over distinct pattern variables whose body does not call
the function itself. Anything else — a missing case, a self-referential `define-fun`,
a mix of the two shapes, a function used with no definition — is declined as
`unknown`, never graded. Note the escape hatch extends the *syntax*, not the fragment:
the body must itself be translatable, so an operator needing a case split (`max`) or a
primitive cvc5regate has no node for is still out of scope. `apply` works in induction
mode, in the equational (`transformation`/`equation`) oracle, in a `ruleset` rule under
`verify_rules`, and in the student's submitted steps (matched symbolically, no solver).

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
toolchain-absent ⇒ `unknown`. This holds for both the induction certifier and the
non-induction equivalence oracle — the only unsupported mode string is anything
other than `induction` / `transformation` / `equation`, which is a `400`.

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
- `cvc5_equiv.py` — the **non-induction equivalence oracle**: builds the plain
  `source = target` prove / free-const disprove SMT sources (reusing the induction
  translator), `decide_equivalence(ex, a, b)` (disprove-first then prove with an
  optional Alethe+Carcara re-check), and a structural `distance` for partial credit.
- `step_check.py` — strict rule-instance checker for the student's steps (shared
  shape with coqregate's, but a deliberately independent copy). `check_case` grades
  an induction obligation; `check_derivation` grades a plain transformation/equation
  derivation with per-step `StepStatus` output.
- `grade.py` — protocol entrypoint (CLI + HTTP), `backend = "cvc5regate"`.
  `_grade_induction` and `_grade_equational` are the two mode dispatchers.
- `check_induction.py` — live harness; `--require-cvc5` runs the emitted goals
  through real cvc5 and asserts the MUST_PASS set settles.
- `tests/test_cvc5_prover.py` — translation / wiring tests against a stubbed
  solver seam, plus an availability-gated real-cvc5 run.
- `tests/test_cvc5_equiv.py` — non-induction grading tests (transformation +
  equation) against the stubbed solver seam: target-form, disproof witness,
  partial credit, derivation certification, and the oracle backstop.
- `tests/test_cvc5_assumptions.py` — `exercise.assumptions` on both SMT paths:
  the guarded-division wrong grade, the untranslatable-kind decline, and the
  witness fail-safe.

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
