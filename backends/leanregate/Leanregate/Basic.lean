/-
Leanregate — the verified rule library.

Each rewrite rule from the shared catalogue is stated and proven as a rational
identity, under its side condition. This is the formal counterpart to
Eggregate's `check_rules.py`: where that *fuzzes* soundness with random rationals,
this *proves* it. A graded derivation is sound iff every step is an instance of
one of these lemmas (the step-checker that consumes these proofs is future work).

Targets Lean 4 + Mathlib. Division by zero is 0 by Lean's convention, so the
fraction rules carry the same `≠ 0` hypotheses the catalogue guards encode.

NOTE: not compiled in the scaffolding environment; run `lake build`.
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Leanregate

variable (a b c : ℚ)

-- Add
theorem add_comm'       : a + b = b + a            := by ring
theorem add_assoc'      : (a + b) + c = a + (b + c) := by ring
theorem add_zero_left   : 0 + a = a                := by ring
theorem add_zero_right  : a + 0 = a                := by ring

-- Sub
theorem sub_zero_right  : a - 0 = a                := by ring
theorem sub_self'       : a - a = 0                := by ring
theorem sub_as_add_neg  : a - b = a + (-b)         := by ring

-- Mul
theorem mul_comm'       : a * b = b * a            := by ring
theorem mul_assoc'      : (a * b) * c = a * (b * c) := by ring
theorem mul_one_left    : 1 * a = a                := by ring
theorem mul_one_right   : a * 1 = a                := by ring
theorem mul_zero_left   : 0 * a = 0                := by ring
theorem mul_zero_right  : a * 0 = 0                := by ring
theorem mul_distrib     : a * (b + c) = a * b + a * c := by ring

-- Negation
theorem neg_neg'        : -(-a) = a                := by ring
theorem add_inverse     : a + (-a) = 0             := by ring

-- Fraction (guarded: the catalogue's nonzero side conditions)
theorem frac_one_denom  : a / 1 = a                := by simp
theorem frac_self_one (h : a ≠ 0) : a / a = 1      := div_self h
theorem frac_mul_cancel_left (h : c ≠ 0) :
    (c * a) / (c * b) = a / b := by
  rw [mul_div_mul_left a b h]

/-- A guarded rule that is UNSOUND without its hypothesis — the `x/x = 1` case
    `check_rules.py` catches at `x = 0`. Here the type *forces* the hypothesis:
    you cannot state it without `a ≠ 0`, so the unsound version is unprovable. -/
example : ¬ (∀ a : ℚ, a / a = 1) := by
  intro h; have := h 0; simp at this

end Leanregate
