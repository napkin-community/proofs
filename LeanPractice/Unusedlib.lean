import LeanPractice.Obviouslib

--
-- Series of unused lemmas
--
lemma lt2_is_0or1 (a : ℕ) : a < 2 ↔ a = 0 ∨ a = 1 :=
  have ltor (h : a < 2) : a = 0 ∨ a = 1 := match a with | 0 | 1 => by decide
  have rtol (h : a = 0 ∨ a = 1) : a < 2 := match a with | 0 | 1 => by decide
  ⟨ltor, rtol⟩

lemma nat_is_2dvd_or_not (a : ℕ) : (2 ∣ a) ∨ ¬(2 ∣ a) := by
  cases (Nat.mod_two_eq_zero_or_one a) with
  | inl even => left; exact Nat.dvd_of_mod_eq_zero even
  | inr odd => simp_all

lemma even_is_2dvd (a : ℕ) : (a % 2 = 0) ↔ 2 ∣ a :=
  have ltor : a % 2 = 0 → 2 ∣ a := by
    intro h
    apply Nat.dvd_of_mod_eq_zero
    exact h
  have rtol : 2 ∣ a → a % 2 = 0 := by
    intro h
    apply Nat.mod_eq_zero_of_dvd
    exact h
  ⟨ltor, rtol⟩

lemma odd_is_not_2dvd (a : ℕ) : (a % 2 = 1) ↔ ¬(2 ∣ a) := by simp
