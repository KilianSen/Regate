# Coqregate

A pluggable grading backend for equational-reasoning exercises in learning
platforms. It implements the language-agnostic grading contract
**[`GRADING_PROTOCOL.md`](../../GRADING_PROTOCOL.md)** (`GradeRequest` →
`GradeResponse`, MathNode JSON, CLI + HTTP transports), so a host platform
integrates against that contract once and runs this backend as a self-contained
container, selected per exercise. (Artemis is the reference adopter; nothing here
depends on it.)

Coqregate is a **specialist certifier** for proofs by **induction over ℕ**
(`mode: "induction"`), built on **Rocq (Coq)**. Coq's `ring`/`field`/`lia`/`nia`
ship in the **standard library**, so the toolchain is lightweight (~600 MB, ~1.5 GB
as a Docker image) and fully offline — there is no large external math library to
fetch or build.

## What it does

On `mode: "induction"` it grades the **student's derivation**, not just the bare
theorem. Each submitted step of the `base` (P(0)) and inductive `step` (P(S n),
with the hypothesis P(n) available) must be a valid instance of a transmitted rule
(`step_check`, strict — a value-equal state reached by any other means is
rejected), and both obligations must reduce to a reflexive `t = t`. Only then does
Coq **backstop the `∀n` leap**: it translates the goal + recursive `definitions`
into a `.v` file — a `Fixpoint pw (a:Q)(n:nat) : Q`, a `Theorem regate_induction :
forall …, lhs == rhs`, and a `Proof. intros …; induction n as [| k ih]; … Qed.`
script — and **kernel-checks it** with `coqc` (or `rocq compile`).

Honest by construction (the protocol's contract): every step valid and Coq accepts
the leap → `proven_equal` / `certified: true`, with the accepted Coq source
attached as the `proof`. A fabricated step → `invalid_derivation`. A step citing a
rule outside the certifiable fragment, a goal Coq rejects, a half-empty
submission, or an absent toolchain → `unknown` (honestly inconclusive, never a
false grade). Non-induction modes are out of scope and return `unknown`.

### The ruleset is trusted by default

The transmitted `ruleset` is the caller's responsibility, validated upstream (see
the trust boundary in the [contract](../../GRADING_PROTOCOL.md)); coqregate grades
the derivation against it without re-proving it. Set `options.verify_rules` to
have each rule kernel-proven here first with an automatic tactic — an unsound rule
then makes a step citing it `unknown` (never `invalid_derivation`; the student
applied the rule they were handed). Per-rule status is reported in `meta.ruleset`.
Regate never runs a caller-supplied proof script, so a rule's `proof` field is
ignored. Recursive `definitions` are always trusted.

### Supported fragment (first slice)

A ℚ-valued equality over `+ - *` / `pow` / `succ` / literals, single-variable
structural induction over ℕ, the induction variable an exponent, and `pow`
defined by its `0` / `succ` rules. Anything else ⇒ `unknown`. Verified end-to-end
on **Rocq 9.1.1** for `1^n = 1`, `a^(m+n) = a^m·a^n`, and `a^n·b^n = (a·b)^n`.

### `apply` — named function application (protocol 1.1)

Also supported: the `apply` node, so a host can add a new n-ary operator as
**data** — an `apply` node plus two recursive `definitions` rules — instead of a
new MathNode type wired into every backend. A function is defined by exactly two
transmitted rules, one matching the ℕ base constructor `0` and one matching the
step constructor `S k`, recursing on the constructor-matched argument **at any
position** (`fact_aux(x, S k)` recurses on its second, `sum(S k)` on its first).
Each becomes one Coq `Fixpoint … {struct n}` with a two-branch `match`, emitted in
dependency order; a ℕ index used as a ℚ *value* (`fact (S k) = (S k)·fact k`) goes
through an emitted ℕ→ℚ coercion, and the proof `revert`s the ℚ binders so the
inductive hypothesis is generalized over them.

**ℕ only.** `exercise.datatype` (lists, trees) is not implemented: a definition
that matches a non-ℕ constructor, a non-structural recursive call, mutual
recursion, or a function name that is not a Coq identifier is declined
(`untranslatable` ⇒ `unknown`), never graded. A derivation that instantiates the
IH at a *shifted accumulator* is likewise declined — the emitted Coq proof
generalizes the IH, but `step_check` here recognises it only at the induction
variable, and half-checking a derivation would be a false `invalid_derivation`.

### ℚ equality: `==` (Qeq), not Leibniz `=`

Coq's rationals are `QArith`'s `Q` (numerator `#` denominator). Two `Q` that
denote the same rational — `2#4` and `1#2` — are *Leibniz-distinct* but equal
under `Qeq`, written `==`; the `Q` ring/field instances (and `ring`/`field`) are
declared over **`Qeq`**, not `=`. Coqregate therefore states and proves the goal
as `lhs == rhs` — the mathematically correct notion of rational equality and the
only one `ring`/`field` can discharge.

## Trust model

`certified: true` rests on **two** things: every student step is a valid instance
of a transmitted rule (`step_check`), and the **Coq kernel** accepts the `∀n`
induction proof of the goal (`coqc`, `Qed.`). The certificate attached as `proof`
is the kernel-checked Coq source. Rule *soundness* is the caller's upstream
responsibility, not re-checked at grade time unless `options.verify_rules` asks —
kernel-checking the goal alone does **not** vouch for the rules, so a false rule
correctly applied to a true goal is `unknown`, never certified. A reject, an
out-of-fragment goal, a bad step, or an absent toolchain all yield the honest
outcome, never a false grade.

## Files

- `coq_prover.py` — the kernel seam: `coq_available()` (looks for `coqc`/`rocq`)
  and `check_source(source) -> (ok, detail)` which compiles a generated `.v` in a
  scratch dir, content-hash cached. stdlib-only Python.
- `coq_induction.py` — translates the induction request to Coq and emits the
  `induction n` proof. `grade_derivation(ex, sub)` is the grading path (grade the
  student's base/step steps, then backstop the leap); `certify(ex)` is the
  bare-goal oracle it calls; `prove_ruleset(ex)` re-proves the ruleset under
  `verify_rules`.
- `step_check.py` — strict rule-instance checker for the student's steps (shared
  shape with cvc5regate's, but a deliberately independent copy).
- `grade.py` — protocol entrypoint (CLI + HTTP), `backend = "coqregate"`.
- `check_induction.py` — live-kernel CI harness; feeds the emitted proofs through
  real `coqc`/`rocq` and asserts the MUST_PASS goals compile.
- `tests/test_coq_prover.py` — translation / emitter / wiring tests that run
  **without** Coq installed (the kernel seam is stubbed).

## Run / deploy

```sh
python grade.py                  # HTTP: POST /grade, GET /health  (port 8000)
python grade.py --cli            # CLI:  GradeRequest stdin -> GradeResponse stdout
python check_induction.py --require-coq    # CI: kernel-check the emitted proofs
brew install coq                 # macOS toolchain (or: apt-get install coq)
docker build -f Dockerfile -t coqregate .  # OCI image (build context = repo root)
```
