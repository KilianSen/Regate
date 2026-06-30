# Coqregate

A grading backend for Artemis equational-reasoning exercises. It implements the
language-agnostic grading contract **[`GRADING_PROTOCOL.md`](../../GRADING_PROTOCOL.md)**
(`GradeRequest` → `GradeResponse`, MathNode JSON, CLI + HTTP transports), so
Artemis integrates against that contract once and runs this backend as a
self-contained, pluggable container, selected per exercise.

Coqregate is a **specialist certifier** for proofs by **induction over ℕ**
(`mode: "induction"`), built on **Rocq (Coq)**. Coq's `ring`/`field`/`lia`/`nia`
ship in the **standard library**, so the toolchain is lightweight (~600 MB, ~1.5 GB
as a Docker image) and fully offline — there is no large external math library to
fetch or build.

## What it does

On `mode: "induction"` it translates the goal `∀n. P(n)` and the transmitted
recursive `definitions` into a Coq `.v` file — a `Fixpoint pw (a:Q)(n:nat) : Q`,
a `Theorem regate_induction : forall …, lhs == rhs`, and a `Proof. intros …;
induction n as [| k ih]; … Qed.` script using `simpl`/`ring` — and
**kernel-checks it** with `coqc` (or `rocq compile`).

Honest by construction (the protocol's contract): Coq accepts → `proven_equal` /
`certified: true`; Coq rejects, the goal is outside the supported fragment, or the
toolchain is absent → `unknown` (honestly inconclusive, never a false grade).
Non-induction modes are out of scope and return `unknown`.

### Supported fragment (first slice)

A ℚ-valued equality over `+ - *` / `pow` / `succ` / literals, single-variable
structural induction over ℕ, the induction variable an exponent, and `pow`
defined by its `0` / `succ` rules. Anything else ⇒ `unknown`. Verified end-to-end
on **Rocq 9.1.1** for `1^n = 1`, `a^(m+n) = a^m·a^n`, and `a^n·b^n = (a·b)^n`.

### ℚ equality: `==` (Qeq), not Leibniz `=`

Coq's rationals are `QArith`'s `Q` (numerator `#` denominator). Two `Q` that
denote the same rational — `2#4` and `1#2` — are *Leibniz-distinct* but equal
under `Qeq`, written `==`; the `Q` ring/field instances (and `ring`/`field`) are
declared over **`Qeq`**, not `=`. Coqregate therefore states and proves the goal
as `lhs == rhs` — the mathematically correct notion of rational equality and the
only one `ring`/`field` can discharge. (See the header of `coq_induction.py`.)

## Trust model

`certified: true` rests on the **Coq kernel**: the emitted `.v` is checked by
`coqc`, and only a `Qed.`-accepted proof term is treated as a certificate (the
certificate is the kernel-checked Coq source). A reject, an out-of-fragment goal,
or an absent toolchain all yield `unknown`, never a false grade.

## Files

- `coq_prover.py` — the kernel seam: `coq_available()` (looks for `coqc`/`rocq`)
  and `check_source(source) -> (ok, detail)` which compiles a generated `.v` in a
  scratch dir, content-hash cached. stdlib-only Python.
- `coq_induction.py` — translates the induction request to Coq, emits the
  `induction n` proof, and certifies it via `coq_prover`. `certify(ex) ->
  CertifyResult`.
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
