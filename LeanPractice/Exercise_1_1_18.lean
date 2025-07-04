import LeanPractice.Obviouslib

/-
# Exercise 1.1.18. Which of these are groups?

(a) Rational numbers with odd denominators (in simplest form), where the
operation is addition. (This includes integers, written as n/1, and 0 = 0/1).
-/

def RatOddDenom : Type := { q : ℚ // ¬(2 ∣ q.den) }

instance : Add RatOddDenom where add a b := ⟨a.val + b.val, by exact rat_odd_denom_add a.property b.property⟩
instance : Zero RatOddDenom where zero := ⟨mkRat 0 1, by simp⟩
instance : Neg RatOddDenom where neg a := ⟨-a.val, by simp [a.property]⟩

instance : AddCommGroup RatOddDenom where
  add_assoc a b c := by apply Subtype.eq; exact Rat.add_assoc a.val b.val c.val
  zero_add a := by apply Subtype.eq; exact Rat.zero_add a.val
  add_zero a := by apply Subtype.eq; exact Rat.add_zero a.val
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by apply Subtype.eq; exact Rat.neg_add_cancel a.val
  add_comm a b := by apply Subtype.eq; exact Rat.add_comm a.val b.val
