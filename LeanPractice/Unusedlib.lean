import Mathlib.Data.Rat.Lemmas

--
-- Series of unused lemmas
--
lemma lt2_is_0or1 (a : ℕ) : a < 2 ↔ a = 0 ∨ a = 1 := by
  have ltor : a < 2 → a = 0 ∨ a = 1 := by
    intro h
    cases h with
    | refl => decide
    | step => simp_all
  exact ⟨ltor, by aesop⟩

lemma nat_is_even_or_odd (a : ℕ) : (a % 2 = 0) ∨ (a % 2 = 1) := by
  rw [← lt2_is_0or1]
  exact Nat.mod_lt a (by decide)

lemma nat_is_2dvd_or_not (a : ℕ) : (2 ∣ a) ∨ ¬(2 ∣ a) := by
  have h : (a % 2 = 0) ∨ (a % 2 = 1) := by apply nat_is_even_or_odd
  cases h with
  | inl even => left; exact Nat.dvd_of_mod_eq_zero even
  | inr odd => simp_all

lemma even_is_2dvd (a : ℕ) : (a % 2 = 0) ↔ 2 ∣ a := by
  have ltor : a % 2 = 0 → 2 ∣ a := by
    intro h
    apply Nat.dvd_of_mod_eq_zero
    exact h
  have rtol : 2 ∣ a → a % 2 = 0 := by
    intro h
    apply Nat.mod_eq_zero_of_dvd
    exact h
  exact ⟨ltor, rtol⟩

lemma odd_is_not_2dvd (a : ℕ) : (a % 2 = 1) ↔ ¬(2 ∣ a) := by simp
