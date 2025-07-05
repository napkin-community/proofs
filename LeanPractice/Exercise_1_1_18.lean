import LeanPractice.Obviouslib
import Mathlib.Tactic.Linarith

/-
# Exercise 1.1.18. Which of these are groups?

(a) Rational numbers with odd denominators (in simplest form), where the
operation is addition. (This includes integers, written as n/1, and 0 = 0/1).
-/
def RatOddDenom : Type := { q : ℚ // ¬(2 ∣ q.den) }

instance : Add RatOddDenom where
  add a b := ⟨a.val + b.val, by exact rat_odd_denom_add a.property b.property⟩
instance : Zero RatOddDenom where
  zero := ⟨mkRat 0 1, by simp⟩
instance : Neg RatOddDenom where
  neg a := ⟨-a.val, by simp [a.property]⟩
instance : AddCommGroup RatOddDenom where
  add_assoc a b c := by apply Subtype.eq; exact Rat.add_assoc a.val b.val c.val
  zero_add a := by apply Subtype.eq; exact Rat.zero_add a.val
  add_zero a := by apply Subtype.eq; exact Rat.add_zero a.val
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by apply Subtype.eq; exact Rat.neg_add_cancel a.val
  add_comm a b := by apply Subtype.eq; exact Rat.add_comm a.val b.val

/-
(b) The set of rational numbers with denominator at most 2, where the operation is addition.
-/
def RatDenomLE2 : Type := { q : ℚ // q.den ≤ 2 }

instance : Add RatDenomLE2 where
  add a b := ⟨a.val + b.val, by exact rat_denom_le2_add a.property b.property⟩
instance : Zero RatDenomLE2 where
  zero := ⟨mkRat 0 1, by simp⟩
instance : Neg RatDenomLE2 where
  neg a := ⟨-a.val, by simp [a.property]⟩
instance : AddCommGroup RatDenomLE2 where
  add_assoc a b c := by apply Subtype.eq; exact Rat.add_assoc a.val b.val c.val
  zero_add a := by apply Subtype.eq; exact Rat.zero_add a.val
  add_zero a := by apply Subtype.eq; exact Rat.add_zero a.val
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by apply Subtype.eq; exact Rat.neg_add_cancel a.val
  add_comm a b := by apply Subtype.eq; exact Rat.add_comm a.val b.val

/-
(c) The set of rational numbers with denominator at most 2, where the operation is multiplication.
-/
theorem rat_denom_le2_no_mul_group
  (grp : Group RatDenomLE2)
  (h : ∀ {a b : RatDenomLE2}, (grp.mul a b).val = a.val * b.val)
: False
:= by
  have h0 := rat_denom_le2_mul
  push_neg at h0
  obtain ⟨va, vb, ha, hb, hab_not⟩ := h0
  let ab := grp.mul ⟨va, ha⟩ ⟨vb, hb⟩
  let hab := ab.property
  have h: ab.val.den = (va * vb).den := by rw [h]
  linarith

/-
(d) The set of nonnegative integers, where the operation is addition.
-/
theorem nat_no_add_group
  (grp : AddGroup ℕ)
  (h : ∀ {a : ℕ}, a ≠ 0 → a + (-a) = 0)
: False
:= by
  specialize h (a := 1)
  aesop
