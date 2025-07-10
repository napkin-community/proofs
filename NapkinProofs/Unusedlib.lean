import Aesop
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Rat.Init
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic.Lemma
import Mathlib.Analysis.InnerProductSpace.PiL2

--
-- Series of unused lemmas
--
example {a : ℕ} : a < 2 ↔ a = 0 ∨ a = 1 :=
  have ltor (h : a < 2) : a = 0 ∨ a = 1 := match a with | 0 | 1 => by decide
  have rtol (h : a = 0 ∨ a = 1) : a < 2 := match a with | 0 | 1 => by decide
  ⟨ltor, rtol⟩

example {a : ℕ} : (2 ∣ a) ∨ ¬(2 ∣ a) := by
  cases (Nat.mod_two_eq_zero_or_one a) with
  | inl even => left; exact Nat.dvd_of_mod_eq_zero even
  | inr odd => aesop

example {a : ℕ} : (a % 2 = 0) ↔ 2 ∣ a :=
  have ltor : a % 2 = 0 → 2 ∣ a := by
    intro h
    apply Nat.dvd_of_mod_eq_zero
    exact h
  have rtol : 2 ∣ a → a % 2 = 0 := by
    intro h
    apply Nat.mod_eq_zero_of_dvd
    exact h
  ⟨ltor, rtol⟩

example {a : ℕ} : (a % 2 = 1) ↔ ¬(2 ∣ a) := by simp

example {a : ℚ} {n : ℤ} (h : a = n) : a.den = 1 ∧ a.num = n := by
  aesop

example {x y : ℝ} : ‖!₂[x, y]‖ ^ 2 = ‖!₂[x, 0]‖ ^ 2 + ‖!₂[0, y]‖ ^ 2 := by
  repeat rw [PiLp.norm_sq_eq_of_L2]
  aesop
