import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring

--
-- Series of obvious lemmas
--
lemma div_gcd_dvd (a b : ℕ) : a / b.gcd a ∣ a := by
  use b.gcd a
  rw [Nat.div_mul_self_eq_mod_sub_self, Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right b a), Nat.sub_zero]

lemma two_dvd_trans_contrapose {a b : ℕ} (h0 : ¬(2 ∣ b)) (h1 : a ∣ b) : ¬(2 ∣ a) := by
  intro h2
  exact h0 (Nat.dvd_trans h2 h1)

theorem rat_odd_denom_add {a b : ℚ} (ha : ¬(2 ∣ a.den)) (hb : ¬(2 ∣ b.den)) : ¬(2 ∣ (a + b).den) := by
  have hx : ¬(2 ∣ (a.den * b.den)) := by
    simp_all [Nat.mul_mod]
  have hy : (a + b).den ∣ (a.den * b.den) := by
    simp_all [Rat.add_def, Rat.normalize, div_gcd_dvd (a.den * b.den) (a.num * ↑b.den + b.num * ↑a.den).natAbs]
  exact two_dvd_trans_contrapose hx hy

lemma nz_le2_is_0or1 {a : ℕ} (hnz : a ≠ 0) (hle : a ≤ 2) : a = 1 ∨ a = 2 :=
  match a with | 1 | 2 => by decide

lemma even_iff_abs_even {a : ℤ} : a % 2 = 0 ↔ a.natAbs % 2 = 0 :=
  have ltor (h : a % 2 = 0) : a.natAbs % 2 = 0 := by
    rw [← Int.dvd_iff_emod_eq_zero, ← Int.dvd_natAbs, Int.dvd_natCast, Nat.dvd_iff_mod_eq_zero] at h
    exact h
  have rtol (h : a.natAbs % 2 = 0) : a % 2 = 0 := by
    rw [← Int.dvd_iff_emod_eq_zero, ← Int.dvd_natAbs, Int.dvd_natCast, Nat.dvd_iff_mod_eq_zero]
    exact h
  ⟨ltor, rtol⟩

lemma odd_iff_abs_odd {a : ℤ} : a % 2 = 1 ↔ a.natAbs % 2 = 1 :=
  have ltor (h : a % 2 = 1) : a.natAbs % 2 = 1 := by
    contrapose! h
    simp_all
    rw [even_iff_abs_even]
    exact h
  have rtol (h : a.natAbs % 2 = 1) : a % 2 = 1 := by
    contrapose! h
    simp_all
    rw [← even_iff_abs_even]
    exact h
  ⟨ltor, rtol⟩

lemma odd_iff_coprime2 {a : ℕ} : a % 2 = 1 ↔ a.Coprime 2 :=
  have ltor (h : a % 2 = 1) : a.Coprime 2 := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h]
    decide
  have rtol (h : a.Coprime 2) : a % 2 = 1 := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec] at h
    have := Nat.mod_two_eq_zero_or_one a
    aesop
  ⟨ltor, rtol⟩

lemma odd_mul2_mod4_eq2 {a : ℤ} (h : a % 2 = 1) : (a * 2) % 4 = 2 := by
  rw [Int.emod_eq_iff (by decide)] at h
  have ⟨_, _, h⟩ := h
  have h : 2 ∣ (a - 1) := by simp_all [← @Int.dvd_neg 2 (a - 1)]
  rcases h with ⟨k, h⟩
  have h : a - 1 = k * 2 := by simp_all [Int.mul_comm]
  rw [Eq.comm, eq_sub_iff_add_eq, Eq.comm] at h
  have h : a * 2 = k * 4 + 2 := by rw [h]; ring
  aesop

lemma denom2rat_fact {a : ℚ} (h : a.den = 2) : (a.num * 2) % 4 = 2 := by
  have h := a.reduced
  have h : ¬(2 ∣ a.num.natAbs) := by simp_all [odd_iff_coprime2]; exact h
  have h : a.num % 2 = 1 := by simp_all [odd_iff_abs_odd]
  exact odd_mul2_mod4_eq2 h

lemma rat_denom_le2_add {a b : ℚ} (ha : a.den ≤ 2) (hb : b.den ≤ 2) : (a + b).den ≤ 2 := by
  have ha : a.den = 1 ∨ a.den = 2 := nz_le2_is_0or1 a.den_nz ha
  have hb : b.den = 1 ∨ b.den = 2 := nz_le2_is_0or1 b.den_nz hb

  rcases ha with (ha | ha) <;> rcases hb with (hb | hb)

  -- case (1, 1)
  have h : (a + b).den = 1 := by simp [Rat.add_def, Rat.normalize]; simp [ha, hb]
  rw [h]
  decide

  -- case (1, 2)
  have h := b.reduced
  have h : (a.num * 2 + b.num).gcd 2 = 1 := by aesop
  have h : (a.num * 2 + b.num).natAbs.gcd 2 = 1 := h
  have h : (a + b).den = 2 := by simp_all [Rat.add_def, Rat.normalize]
  simp_all

  -- case (2, 1)
  have h := a.reduced
  have h : (a.num + b.num * 2).gcd 2 = 1 := by aesop
  have h : (a.num + b.num * 2).natAbs.gcd 2 = 1 := h
  have h : (a + b).den = 2 := by simp_all [Rat.add_def, Rat.normalize]
  simp_all

  -- case (2, 2)
  have h : (a.num * 2 + b.num * 2) % 4 = 0 := by
    rw [Int.add_emod, denom2rat_fact ha, denom2rat_fact hb]
    decide
  have h : 4 ∣ (a.num * 2 + b.num * 2) := Int.dvd_of_emod_eq_zero h
  have h : ↑((a.num * 2 + b.num * 2).gcd 4) = (4 : ℤ) := by
    have hx := @Int.gcd_eq_right_iff_dvd 4 (a.num * 2 + b.num * 2) (by decide)
    simp_all [hx]
  have h : (a.num * 2 + b.num * 2).gcd 4 = 4 := by
    rw [← (@Nat.cast_inj ℤ)]
    exact h
  have h : (a.num * 2 + b.num * 2).natAbs.gcd 4 = 4 := h
  have h : (a + b).den = 1 := by simp_all [Rat.add_def, Rat.normalize]
  simp_all
