import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

def pw : ℚ → ℕ → ℚ
  | a, 0 => (1 : ℚ)
  | a, (n + 1) => (a * (pw a n))

theorem regate_induction :∀ (n : ℕ), (pw (1 : ℚ) n) = (1 : ℚ) := by
  intro n
  induction n with
  | zero => first | simp_all [pw] | (simp [pw]; ring) | ring
  | succ k ih => simp only [pw, Nat.add_eq]; first | (rw [ih]; ring) | (rw [← ih]; ring) | (simp only [ih]; ring) | (simp only [← ih]; ring) | simp_all [pw, ih]
