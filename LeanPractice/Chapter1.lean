import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Complex.Circle
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

import LeanPractice.Obviouslib

/-
# Example 1.1.1 (Additive integers)

The pair (ℤ, +) is a group: ℤ = {. . . , −2, −1, 0, 1, 2, . . . } is the set and
the associative operation is addition. Note that
• The element 0 ∈ ℤ is an identity: a + 0 = 0 + a = a for any a.
• Every element a ∈ ℤ has an additive inverse: a + (−a) = (−a) + a = 0.
We call this group ℤ.
-/
instance : AddCommGroup ℤ := by infer_instance

/-
# Example 1.1.2 (Nonzero rationals)
Let ℚ^× be the set of *nonzero rational numbers*. The pair (ℚ^×, ·) is a group: the set
is ℚ^× and the associative operation is *multiplication*.
Again we see the same two nice properties.
• The element 1 ∈ ℚ^× is an identity: for any rational number, a · 1 = 1 · a = a.
• For any rational number x ∈ ℚ^×, we have an inverse x^−1, such that

    x · x^−1 = x^−1 · x = 1.
-/
instance : CommGroup ℚˣ := by infer_instance
example : ℚˣ ≃ { q : ℚ // q ≠ 0 } where
  toFun q := ⟨q.val, q.ne_zero⟩
  invFun q := Units.mk0 q.val q.property
  left_inv q := by aesop
  right_inv q := by aesop

/-
# Example 1.1.6 (Non-Examples of groups)
• The pair (ℚ, ·) is NOT a group. (Here ℚ is rational numbers.) While there is
  an identity element, the element 0 ∈ ℚ does not have an inverse.
-/
example : ¬(∀ {a : ℚ}, a * a⁻¹ = 1) := by
  push_neg
  use 0
  linarith

/-
• The pair (Z, ·) is also NOT a group. (Why?)
-/
example (grp : Group ℤ) : ¬(∀ {a : ℤ}, a * a⁻¹ = 1) := by
  push_neg
  use 0
  linarith

/-
• Let Mat_2×2(ℝ) be the set of 2 × 2 real matrices. Then (Mat_2×2(ℝ), ·)
  (where · is matrix multiplication) is NOT a group.
-/
example : ¬(∀ {a : (Matrix (Fin 2) (Fin 2) ℝ)}, a * a⁻¹ = 1) := by
  intro h
  let zero : (Matrix (Fin 2) (Fin 2) ℝ) := 0
  specialize h (a := zero)
  have : zero⁻¹ = zero := by simp [zero]
  aesop

/-
# Example 1.1.7 (Complex unit circle)
Let S^1 denote the set of complex numbers z with absolute value one; that is

    S^1 := {z ∈ ℂ | |z| = 1}

Then (S^1, ×) is a group
-/
noncomputable instance : CommGroup Circle := by infer_instance
noncomputable example : Circle ≃ { z : ℂ // ‖z‖ = 1 } where
  toFun z := ⟨z, by aesop⟩
  invFun z := ⟨z.val, by aesop⟩
  left_inv z := by aesop
  right_inv z := by aesop

/-
# Example 1.1.8 (Addition mod n)
Here is an example from number theory: Let n > 1 be an integer, and consider the
residues (remainders) modulo n. These form a group under addition. We call this
the **cyclic group of order n**, and denote it as Z/nZ, with elements 0, 1, . . . . The
identity is 0.
-/
instance (n : ℕ) : AddCommGroup (ZMod n) := by infer_instance

/-
# Example 1.1.9 (Multiplication mod p)
Let p be a prime. Consider the *nonzero residues modulo* p, which we denote by
(Z/pZ)^×. Then ((Z/pZ)^×, ×) is a group.
-/
instance (p : ℕ) [Fact p.Prime] : CommGroup (ZMod p)ˣ := by infer_instance

/-
# Question 1.1.10. Why do we need the fact that p is prime?
-/
example : ¬(∀ {n : ℕ} [NeZero n], Fintype.card (ZMod n)ˣ = n - 1) := by
  intro h
  specialize h (n := 4)
  have : Fintype.card (ZMod 4)ˣ = 2 := by decide
  tauto

/-
# Example 1.1.11 (General linear group)
Let n be a positive integer. Then GL_n(ℝ) is defined as the set of n×n real matrices
which have nonzero determinant. It turns out that with this condition, every matrix
does indeed have an inverse, so (GL_n(ℝ), ×) is a group, called the general linear
group.
-/
instance (n : ℕ) [NeZero n] : Group (Matrix.GeneralLinearGroup (Fin n) ℝ) := by
  infer_instance

/-
# Example 1.1.12 (Special linear group)
Following the example above, let SL_n(ℝ) denote the set of n × n matrices whose
determinant is actually 1. Again, for linear algebra reasons it turns out that
(SL_n(ℝ), ×) is also a group, called the special linear group.
-/
instance (n : ℕ) [NeZero n] : Group (Matrix.SpecialLinearGroup (Fin n) ℝ) := by
  infer_instance

-- TODO

/-
# Exercise 1.1.18. Which of these are groups?

(a) Rational numbers with odd denominators (in simplest form), where the
operation is addition. (This includes integers, written as n/1, and 0 = 0/1).
-/
def RatOddDenom := { q : ℚ // ¬(2 ∣ q.den) }

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
def RatDenomLE2 := { q : ℚ // q.den ≤ 2 }

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
example (grp : Group RatDenomLE2) : ¬(∀ {a b : RatDenomLE2}, (a * b).val = a.val * b.val) := by
  intro h
  have h0 := rat_denom_le2_mul
  push_neg at h0
  obtain ⟨a, b, ha, hb, hab_not⟩ := h0
  let a : RatDenomLE2 := ⟨a, ha⟩
  let b : RatDenomLE2 := ⟨b, hb⟩
  have := (a * b).property
  have : (a * b).val.den = (a.val * b.val).den := by rw [h]
  linarith

/-
(d) The set of nonnegative integers, where the operation is addition.
-/
example (grp : AddGroup ℕ) : ¬(∀ {a : ℕ}, a + (-a) = 0) := by
  intro h
  specialize h (a := 1)
  linarith
