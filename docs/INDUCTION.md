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
  `certified: false`, never a certified pass. (`leanregate`'s `Nat.rec` is what
  certifies the leap — wired in `lean_induction.py`; see below.)

This split — *grade each case soundly, defer the schema* — is the cleanest
illustration yet of why two backends exist.

## Grade vs. certify — and when a student submission needs each

**Grade** = produce a verdict (`outcome` + `score`). **Certify** = back a *positive*
("they're equal") verdict with a machine-recheckable proof (`certified: true`, which
the protocol *requires* to carry a re-checkable `proof`). Certifying is one possible
*result* of grading, not a separate step — every request is graded; only some results
are certified.

For grading student inductions, **certification is not required** — it is a trust
upgrade, needed in exactly one situation:

- **Certify NOT needed** when a human reviews passes, or the submission is *wrong*, or
  you only want per-step feedback / partial credit. A wrong obligation gives a sound
  `invalid_derivation` / `score: 0` (no kernel involved); a correct one gives
  `equal_no_certificate` / `null` that a tutor signs off. Most classroom grading lives
  here.
- **Certify NEEDED** only to **auto-award full credit on a *correct* inductive proof
  with no human in the loop.** That is the one case eggregate can't serve (no kernel
  for the schema) and leanregate can (`Nat.rec`, kernel-checked → `proven_equal` /
  `certified: true`).

### Why the `∀n` leap specifically needs a sign-off

eggregate is sound because every step is *valid by construction* — a rule match or an
exact-match Type-B substitution — so a **finite** chain yields equivalence by
transitivity. `∀n. P(n)` is not the endpoint of any finite rewrite chain: it quantifies
over infinitely many `n`. The inference `base ∧ step ⟹ ∀n. P(n)` **is the induction
axiom** (Nat.rec / well-founded induction over ℕ) — a primitive of the logic, not a
theorem derivable from the catalogue rules. eggregate has no representation of that
axiom and no kernel to re-check it, so it can confirm the two *premises* (the
obligations) but must *assume* the rule joining them. Honoring its honesty invariant
(never certify an inference it can't independently re-check), it defers that single gap
to a human or to leanregate. The two finite obligations need no sign-off; only the
infinite leap between them does.

### Is eggregate correct on "basic undergrad" inductions?

The limiter is **coverage, not correctness** — eggregate is essentially never
*confidently wrong*, but the slice it can express is narrower than "all undergrad
induction":

- **Within its fragment** — *equalities* over `+ − · pow succ`, single-variable
  structural induction over ℕ, with sound definitions (the sum/product/power-identity
  exercises) — its obligation-checking is sound by construction, false *positives* are
  designed out (incl. the circular-IH error, blocked by exact-match Type-B), and the
  plain-ℕ schema it assumes there is genuinely valid. A `base closed + step closed`
  result is reliable; signing off on it is safe ~always.
- **Outside its fragment it defers (`unknown`), it does not mis-grade** —
  **inequalities** (`2ⁿ > n`, `n! ≥ 2ⁿ`), **strong induction / multiple or shifted base
  cases**, and **existential / divisibility** goals (`3 ∣ n³−n`) cannot be expressed in
  the equality-over-arithmetic model at all. A large fraction of undergrad induction is
  inequalities, so "99% correct" overstates *coverage* even though *correctness* holds
  where it applies.
- **One in-fragment caveat:** recursive `definitions` are **trusted, not audited** (see
  guardrail 3). A wrong/circular definition can make bogus obligations close, so
  in-fragment correctness is conditional on the definitions being sound — which the
  course author controls.

Net: for equality inductions over ℕ with correct definitions, eggregate is reliably
correct and safe to sign off. It trades coverage for never being confidently wrong
(`unknown` instead of a guess) — which is the design intent, and exactly why leanregate
exists to certify the cases that must be trusted automatically.

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
- `grade.py` (leanregate): `induction` mode → `lean_induction.certify` (a real Lean
  `induction n` kernel run); certified → `proven_equal`, else honest `unknown`.
- `GRADING_PROTOCOL.md`: the `induction` request shape.
- Conformance: `19-induction-valid`, `20-induction-circular-ih`.

### Worked example (verified, graded end-to-end)

Prove **`1^n = 1`** by induction on `n`, with `pow(a,0)→1`, `pow(a,S n)→a·pow(a,n)`:

- **base** `P(0)`: `1^0 = 1` → `pow_zero` → `1 = 1`. ✓
- **step** `P(S n)`: `1^(S n) = 1` → `pow_succ` → `1·1^n = 1` → **IH** `1^n→1` → `1·1 = 1`
  → `mul_one_left` → `1 = 1`. ✓
- verdict: `equal_no_certificate` (both obligations valid; schema assumed).

## leanregate certification (built)

`lean_induction.py` turns the deferred verdict into a **certified** one. Given the
induction request it:

1. infers which variables are ℕ (the induction var + any exponents) vs ℚ;
2. derives a Lean recursive definition from the transmitted `definitions`
   (`def pw : ℚ → ℕ → ℚ | a,0 => … | a,(n+1) => …`);
3. emits the theorem and an `induction n with | zero … | succ k ih …` proof;
4. **kernel-checks it** via `lean_prover._run_lean` (the existing Lean seam).

If Lean accepts → `proven_equal` / `certified: true` (`meta.induction.method = "induction"`).
If Lean rejects, the goal is outside the supported fragment, or the toolchain is
absent → `unknown` (never a false grade). So the deployed leanregate container
(Lean + Mathlib) **certifies** `∀n.P(n)`, while the Lean-free dev/conformance env
honestly returns `unknown` — fixture `19-induction-valid` expects exactly that.

The generated `induction n` proofs for `1^n = 1`, `a^(m+n) = a^m·a^n`, and
`a^n·b^n = (a·b)^n` have been **run through a real Lean v4.32.0-rc1 + Mathlib kernel** (not
just inspected): `check_induction.py --require-lean` feeds the emitter's output to
`lean_prover._run_lean` and all three compile. The accept→certified /
reject→unknown wiring is exercised the same way. So the live kernel genuinely
accepts the emitted source — what remains environment-gated is only *having* the
toolchain (the leanregate image / CI's `lean-action` / a local `elan` install).

Supported fragment (first slice): a ℚ-valued equality over `+ - * pow succ` literals,
`pow` defined by its `0`/`succ` rules, the induction variable an exponent. Outside
that ⇒ `unknown`.

## Not yet done

- **Frontend** — author an induction exercise and prove the base/step cases (reusing
  the lemma/hypothesis UI).
- **General recursive functions** — arbitrary function symbols/arities and ℕ→ℚ
  coercions (`sum`, `factorial`) beyond the single `pow` block; a ℕ-aware evaluator so
  eggregate could fuzz-cross-check custom recursive definitions.

## Live Lean check (CI)

`backends/leanregate/check_induction.py` feeds the *emitted* proofs through a real
Lean toolchain (`python check_induction.py --require-lean`) and asserts the MUST_PASS
goals kernel-check. All three currently-supported goals are MUST_PASS and verified
green on Lean v4.32.0-rc1 + Mathlib: `1^n = 1`, `a^(m+n) = a^m·a^n`, `a^n·b^n = (a·b)^n`
(the `BEST_EFFORT` list is now empty). The CI `leanregate` job runs it after
`lean-action` builds the Mathlib-backed project, and the leanregate Docker image runs
it in its Lean build stage (`RUN python check_induction.py --require-lean`) — so a
regressed emitter fails both CI and the image build, never shipping broken Lean. Run
without `--require-lean` it skips cleanly where Lean is absent.

The `succ`-case proof tactic (in `lean_induction.build_source`) is: unfold `pw` and
normalise the exponent (`simp only [pw, Nat.add_eq]`), then `first` over a forward IH
rewrite (`rw [ih]; ring`, closes `1^n`/`a^(m+n)`) and a backward fold
(`rw [← ih]; ring`, closes `a^n·b^n` by folding the product under one `pow`), with
`simp`-based variants and `simp_all` as fallbacks. The fold is reached only after the
forward rewrite fails, so it never loops on an IH with a literal RHS.
