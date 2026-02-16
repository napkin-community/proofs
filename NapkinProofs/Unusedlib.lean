import Aesop
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Rat.Init
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic.Lemma
import Mathlib.Analysis.InnerProductSpace.PiL2

import NapkinProofs.Obviouslib


/-
# Series of unused lemmas
-/
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


/-
## Prove termination of Ackermann function
-/
private def ackermann (m n : ℕ) : ℕ :=
  match m, n with
  | 0, n => n + 1
  | m + 1, 0 => ackermann m 1
  | m + 1, n + 1 => ackermann m (ackermann (m + 1) n)

-- NOTE: Since for natural numbers 0 - 1 = 0, n - 1 < n is simply not true.
-- Therefore, if you define ackermann function as below, Lean cannot
-- automatically prove termination.
private partial def ackermann0 (m n : ℕ) : ℕ :=
  match m, n with
  | 0, n => n + 1
  | m, 0 => ackermann0 (m - 1) 1
  | m, n => ackermann0 (m - 1) (ackermann0 m (n - 1))


/-
## Triangular numbers

###### References
- https://en.wikipedia.org/wiki/Triangular_number
-/
private def tri (n : ℕ) : ℕ := (n * (n + 1)) / 2

#guard (Array.range 12).map tri = #[0, 1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66]

private lemma tri_succ (n : ℕ) : tri (n + 1) = tri n + n + 1 := by
  calc
    tri (n + 1)
      = 2 * (tri (n + 1)) / 2             := by rw [Nat.mul_div_cancel_left _ (by decide)]
    _ = 2 * ((n + 1) * (n + 2) / 2) / 2   := by rw [tri]
    _ = (n + 1) * (n + 2) / 2             := by rw [Nat.mul_div_cancel_left' (Even.two_dvd (Nat.even_mul_succ_self (n + 1)))]
    _ = (n * (n + 1) + 2 * (n + 1)) / 2   := by ring_nf
    _ = n * (n + 1) / 2 + 2 * (n + 1) / 2 := by rw [nat_div_add_of_dvd (Even.two_dvd (Nat.even_mul_succ_self n)) (Nat.dvd_mul_right 2 _) (by decide)]
    _ = tri n + (n + 1)                   := by rw [tri, Nat.mul_div_cancel_left _ (by decide)]


/-
## Proof that `1` is not accessible w.r.t. `<` on the closed interval [0, 1]
-/
-- Closed interval [0, 1]
private abbrev I : Type := { x : ℝ // x ∈ Set.Icc (0 : ℝ) 1 }
-- Relation `<` on the closed interval [0, 1]
private def r (a b : I) : Prop := a.1 < b.1
-- The point `1` in the closed interval [0, 1]
private def oneI : I := ⟨1, by simp [Set.Icc]⟩
-- Descending chain `n ↦ 1 / 2^n` (always in [0, 1])
private noncomputable def chain (n : Nat) : I :=
  ⟨(1 : ℝ) / (2 : ℝ) ^ n, by
    refine ⟨by positivity, ?_⟩
    refine (div_le_one (pow_pos (by norm_num : (0 : ℝ) < 2) n)).2 ?_
    simpa using (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))⟩
-- Proof
private theorem one_not_accessible : ¬Acc r oneI := by
  refine (not_acc_iff_exists_descending_chain (r := r) (x := oneI)).2 ?_
  refine ⟨chain, ?_, ?_⟩
  · exact Subtype.ext (by simp [chain, oneI])
  ·
    intro n
    change (1 : ℝ) / (2 : ℝ) ^ (n + 1) < (1 : ℝ) / (2 : ℝ) ^ n
    have hpos : 0 < (2 : ℝ) ^ n := by positivity
    have hlt : (2 : ℝ) ^ n < (2 : ℝ) ^ (n + 1) := by
      rw [pow_succ]
      exact lt_mul_of_one_lt_right hpos (by norm_num : (1 : ℝ) < 2)
    simpa using (one_div_lt_one_div_of_lt hpos hlt)
