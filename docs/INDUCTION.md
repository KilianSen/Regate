# Induction (MS4 direction)

Induction over ℕ — proving `∀n. P(n)` — is the first capability that is *qualitatively
beyond* the equational layer (Type-A rewriting, Type-B substitution, guarded rules,
derived lemmas). This note records why, what this branch builds, and the soundness
guardrails an adversarial review surfaced.

## Why induction is different

Quantifier-free identities over ℚ (`a·(b+c)=a·b+a·c`, `x/x=1` given `x≠0`) are
*decidable* — rewriting / e-graphs / fuzzing handle them. Induction needs three
things the model lacks: an **inductive domain** (ℕ via `0`/`succ`), **recursive
definitions** (the only place induction is *needed* — pure ℚ algebra never is), and
the **induction principle** itself, an axiom *schema*, not an equational rewrite.

But the hard part of the *step case* is already built: the induction hypothesis
`P(n)` is a **hypothesis** (Type-B substitution), and base/step are **sub-derivations**
(like `have`-lemmas). So an `induction n` obligation is: generate two sub-goals —
`P(0)` and `P(S n)` with the IH `P(n)` in scope — and grade each with the existing
step-validator.

## What eggregate can and cannot do (and the honest verdict)

- **Grades the two obligations soundly.** Each is equational; `validate.verify_chain`
  checks every step (Type-A match+guards, Type-B exact-match) and never touches the
  ℚ evaluator or the egglog oracle — so it is sound for `succ`/`pow` and cannot crash
  on them.
- **Cannot certify the leap.** Equality saturation is a *ground* equivalence oracle:
  it cannot represent `∀n`, and a recursive rule `pow(a,S n)→a·pow(a,n)` is simply
  **inert** on a symbolic exponent (its `S n` pattern never matches a bare `n`) — so
  even unbounded saturation proves nothing universal. eggregate therefore **defers**
  on a (correct) inductive claim: `equal_no_certificate` / `score: null` /
  `certified: false`, never a certified pass. (`leanregate`'s `Nat.rec` is what can
  certify the leap; it currently returns `unknown` until that kernel run is wired.)

This split — *grade each case soundly, defer the schema* — is the cleanest
illustration yet of why two backends exist.

## The guardrails (from adversarial review)

Three reviewers red-teamed the design against the code. The surviving must-haves,
all honored here:

1. **The IH enters ONLY as a Type-B hypothesis, never as a Type-A (wildcard) rule.**
   `validate.apply_equation` requires the occurrence to *exactly equal* the equation's
   LHS (`sub != equation.lhs`), with **no wildcard matching** — so `IH: f(n)=g(n)`
   (literal `n`) can rewrite a literal `f(n)` but never `f(S n)`. That is exactly the
   sound behaviour of an induction hypothesis at a fixed arbitrary `n`. Injecting the
   IH as a wildcard *rule* would make Type-A's matcher apply it at `S n` → circular and
   unsound. Conformance fixture `20-induction-circular-ih` pins this: using the IH on
   the `S n` term is rejected (`invalid_derivation`).
2. **Deferral, not a certified pass.** On success eggregate returns
   `equal_no_certificate`/`null` (protocol: `certified:true` requires a re-checkable
   proof of the *whole* claim, which the schema isn't). Fixture `19-induction-valid`.
3. **Recursive definitions are TRUSTED, not ℚ-audited.** The `audit.py` fuzzer checks
   *algebraic identities* by plugging rationals; recursive ℕ definitions are
   definitional and unevaluable over ℚ, so they are not routed through audit (which
   would crash) or the disprove-first ℚ engine (which would spuriously refute an
   ℕ-true goal). Validating recursive *definitions* (well-foundedness/termination) is
   leanregate's job.

## This branch (`feature/induction`)

- `model.py`: `succ` (ℕ successor) and `pow` blocks + `subst_var`. Not in the shipped
  catalogue; never reach the oracle/evaluator.
- `service.py`: `_grade_induction` / `_replay_obligation` — validator-only obligation
  grading with the IH as a Type-B hypothesis and the deferral verdict.
- `grade.py` (leanregate): `induction` mode → `unknown` (honest; awaiting a kernel run).
- `GRADING_PROTOCOL.md`: the `induction` request shape.
- Conformance: `19-induction-valid`, `20-induction-circular-ih`.

### Worked example (verified, graded end-to-end)

Prove **`1^n = 1`** by induction on `n`, with `pow(a,0)→1`, `pow(a,S n)→a·pow(a,n)`:

- **base** `P(0)`: `1^0 = 1` → `pow_zero` → `1 = 1`. ✓
- **step** `P(S n)`: `1^(S n) = 1` → `pow_succ` → `1·1^n = 1` → **IH** `1^n→1` → `1·1 = 1`
  → `mul_one_left` → `1 = 1`. ✓
- verdict: `equal_no_certificate` (both obligations valid; schema assumed).

## Not yet done

- **leanregate certification** — emit a Lean `induction n` proof (with the recursive
  function defined) and kernel-check it via the existing `_run_lean` seam. This is the
  payoff that turns the deferred verdict into a certified one.
- **Frontend** — author an induction exercise and prove the base/step cases (reusing
  the lemma/hypothesis UI).
- **ℕ-typed variables / general function symbols / a ℕ-aware evaluator** — needed before
  custom recursive definitions can be safely admitted or fuzz-cross-checked.
