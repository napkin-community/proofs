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
:= LinearMap.trace_tensorProduct' T S
