/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Fredholm.ClosedRange

/-!
# Composition of Fredholm operators

This file proves that the composite of two Fredholm operators between Banach spaces is Fredholm
and that its index is the sum of their indices. It also records the corresponding statements for
powers of a Fredholm endomorphism.

The finite-dimensional kernel and cokernel statements for a composite are algebraic. Closedness
of its range then follows from `ContinuousLinearMap.isClosed_range_of_finiteDimensional_coker`.
Index additivity reuses Mathlib's `LinearMap.index_comp`, whose proof is the six-term exact
sequence

`0 → ker T → ker (S ∘ T) → ker S → coker T → coker (S ∘ T) → coker S → 0`.

These results supply the compositional calculus for the Fredholm operators and index theory in
Lane F0 of the analytic Heegaard Floer roadmap.

## Main declarations

* `TauCeti.IsFredholm.comp`: a composite of Fredholm operators is Fredholm.
* `TauCeti.ContinuousLinearMap.index_comp`: the index of a composite is the sum of the indices.
* `TauCeti.IsFredholm.pow`: every power of a Fredholm endomorphism is Fredholm.
* `TauCeti.ContinuousLinearMap.index_pow`: the index of the `n`th power is `n` times the index.

The conventions and the composition theorem follow McDuff--Salamon,
*J-holomorphic Curves and Symplectic Topology*, Appendix A.1.
-/

public section

namespace TauCeti

open Module

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]

variable {T : E →L[𝕜] F} {S : F →L[𝕜] G}

/-- The composite of two Fredholm operators is Fredholm.

Only the source and target of the composite need to be complete: completeness of the intermediate
space is not used. -/
theorem IsFredholm.comp (hS : IsFredholm S) (hT : IsFredholm T) :
    IsFredholm (S.comp T) := by
  letI := hT.finiteDimensional_ker
  letI := hT.finiteDimensional_coker
  letI := hS.finiteDimensional_ker
  letI := hS.finiteDimensional_coker
  apply IsFredholm.of_finiteDimensional_ker_coker
  · rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.ker_comp]
    infer_instance
  · rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp]
    infer_instance

namespace ContinuousLinearMap

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace G] in
/-- The Fredholm index is additive under composition. -/
@[simp]
theorem index_comp (S : F →L[𝕜] G) (T : E →L[𝕜] F)
    (hS : IsFredholm S) (hT : IsFredholm T) :
    index (S.comp T) = index S + index T := by
  letI := hT.finiteDimensional_ker
  letI := hT.finiteDimensional_coker
  letI := hS.finiteDimensional_ker
  letI := hS.finiteDimensional_coker
  simp only [index_eq_finrank_sub]
  rw [ContinuousLinearMap.toLinearMap_comp]
  have h := LinearMap.index_comp (f := (T : E →ₗ[𝕜] F)) (S : F →ₗ[𝕜] G)
  simpa only [LinearMap.index_eq_finrank_sub] using h

end ContinuousLinearMap

section Pow

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {A : X →L[𝕜] X}

/-- Every natural-number power of a Fredholm endomorphism is Fredholm. -/
theorem IsFredholm.pow (hA : IsFredholm A) : ∀ n : ℕ, IsFredholm (A ^ n)
  | 0 => by
      rw [pow_zero, ContinuousLinearMap.one_def]
      exact isFredholm_id
  | n + 1 => by
      rw [pow_succ, ContinuousLinearMap.mul_def]
      exact (hA.pow n).comp hA

namespace ContinuousLinearMap

/-- The index of the `n`th power of a Fredholm endomorphism is `n` times its index. -/
@[simp]
theorem index_pow (A : X →L[𝕜] X) (hA : IsFredholm A) (n : ℕ) :
    index (A ^ n) = (n : ℤ) * index A := by
  induction n with
  | zero =>
      simp only [pow_zero, ContinuousLinearMap.one_def, index_id, Nat.cast_zero, zero_mul]
  | succ n ih =>
      rw [pow_succ, ContinuousLinearMap.mul_def,
        index_comp (A ^ n) A (hA.pow n) hA, ih]
      push_cast
      ring

end ContinuousLinearMap

end Pow

end TauCeti
