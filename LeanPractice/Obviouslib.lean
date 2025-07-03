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

