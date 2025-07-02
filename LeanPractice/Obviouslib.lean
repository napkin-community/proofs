import Mathlib.Data.Rat.Lemmas

--
-- Series of obvious lemmas
--
lemma div_gcd_dvd (a b : ℕ) : a / b.gcd a ∣ a := by
  use b.gcd a
  rw [Nat.div_mul_self_eq_mod_sub_self, Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right b a), Nat.sub_zero]

lemma two_dvd_trans_contrapose {a b : ℕ} (h0 : ¬(2 ∣ b)) (h1 : a ∣ b) : ¬(2 ∣ a) := by
  intro h2
  exact h0 (Nat.dvd_trans h2 h1)

lemma rat_odd_denom_add {a b : ℚ} (ha : ¬(2 ∣ a.den)) (hb : ¬(2 ∣ b.den)) : ¬(2 ∣ (a + b).den) := by
  have hx : ¬(2 ∣ (a.den * b.den)) := by
    simp_all [Nat.mul_mod]
  have hy : (a + b).den ∣ (a.den * b.den) := by
    simp_all [Rat.add_def, Rat.normalize, div_gcd_dvd (a.den * b.den) (a.num * ↑b.den + b.num * ↑a.den).natAbs]
  exact two_dvd_trans_contrapose hx hy

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
