import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Basis.VectorSpace
import LeanPractice.Obviouslib

/-
# Problem 11B† (Product of traces)
Let T : V → V and S : W → W be linear maps of finite-dimensional vector spaces V
and W. Define T ⊗ S : V ⊗ W → V ⊗ W by λv ⊗ w.T(v) ⊗ S(w). Prove that:

    Tr(T ⊗ S) = Tr(T) Tr(S).
-/
theorem trace_tensor_product_eq_mul_trace
  -- k ∈ Field
  {𝕜 : Type} [Field 𝕜]
  -- V, W ∈ FDVect_k
  {V : Type} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
  {W : Type} [AddCommGroup W] [Module 𝕜 W] [FiniteDimensional 𝕜 W]
  -- T : V → V
  (T : V →ₗ[𝕜] V)
  -- S : W → W
  (S : W →ₗ[𝕜] W)
: -- Tr(T ⊗ S) = Tr(T) Tr(S)
  LinearMap.trace 𝕜 (TensorProduct 𝕜 V W) (TensorProduct.map T S) = LinearMap.trace 𝕜 V T * LinearMap.trace 𝕜 W S
:= by
  let VW := TensorProduct 𝕜 V W
  let TS := TensorProduct.map T S

  let B_V := Module.finBasis 𝕜 V
  let Tr_T := LinearMap.trace 𝕜 V T
  let mat_T := LinearMap.toMatrix B_V B_V T
  let Tr_mat_T := mat_T.trace
  let h_T := LinearMap.trace_eq_matrix_trace 𝕜 B_V T
  let h_T : Tr_T = Tr_mat_T := by aesop

  let B_W := Module.finBasis 𝕜 W
  let Tr_S := LinearMap.trace 𝕜 W S
  let mat_S := LinearMap.toMatrix B_W B_W S
  let Tr_mat_S := mat_S.trace
  let h_S := LinearMap.trace_eq_matrix_trace 𝕜 B_W S
  let h_S : Tr_S = Tr_mat_S := by aesop

  let B_VW := Module.finBasis 𝕜 VW
  let Tr_TS := LinearMap.trace 𝕜 VW TS
  let mat_TS := LinearMap.toMatrix B_VW B_VW TS
  let Tr_mat_TS := mat_TS.trace
  let h_TS := LinearMap.trace_eq_matrix_trace 𝕜 B_VW TS
  let h_TS : Tr_TS = Tr_mat_TS := by aesop

  let h : Tr_mat_TS = Tr_mat_T * Tr_mat_S := by
    sorry

  rw [← h_T, ← h_S, ← h_TS] at h
  exact h
