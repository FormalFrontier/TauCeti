/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Fredholm.Basic

/-!
# Composition of Fredholm operators

This file proves that, over a complete nontrivially normed scalar field, the composite of two
Fredholm operators between normed spaces is Fredholm and that its index is the sum of their
indices. It also records the corresponding statements for powers of a Fredholm endomorphism.

Fredholmness of a composite follows by composing the continuous quasi-inverses supplied by
Mathlib's Fredholm API.
Index additivity reuses Mathlib's `LinearMap.index_comp`, whose proof is the six-term exact
sequence

`0 → ker T → ker (S ∘ T) → ker S → coker T → coker (S ∘ T) → coker S → 0`.

These results supply the compositional calculus for the Fredholm operators and index theory in
Lane F0 of the analytic Heegaard Floer roadmap.

## Main declarations

* `ContinuousLinearMap.IsFredholm.comp`: a composite of Fredholm operators is Fredholm.
* `TauCeti.ContinuousLinearMap.index_comp`: the index of a composite is the sum of the indices.
* `ContinuousLinearMap.IsFredholm.pow`: every power of a Fredholm endomorphism is Fredholm.
* `TauCeti.ContinuousLinearMap.index_pow`: the index of the `n`th power is `n` times the index.

The conventions and the composition theorem follow McDuff--Salamon,
*J-holomorphic Curves and Symplectic Topology*, Appendix A.1.
-/

public section

namespace TauCeti

open Module

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable {T : E →L[𝕜] F} {S : F →L[𝕜] G}

/-- Over a complete nontrivially normed scalar field, the composite of two Fredholm operators is
Fredholm. -/
theorem _root_.ContinuousLinearMap.IsFredholm.comp
    (hS : ContinuousLinearMap.IsFredholm S) (hT : ContinuousLinearMap.IsFredholm T) :
    ContinuousLinearMap.IsFredholm (S.comp T) := by
  obtain ⟨T', hT'⟩ := hT.exists_isQuasiInverse
  obtain ⟨S', hS'⟩ := hS.exists_isQuasiInverse
  refine ContinuousLinearMap.IsFredholm.of_isQuasiInverse (v := T'.comp S') ?_
  simpa only [ContinuousLinearMap.toLinearMap_comp] using hT'.comp hS'

namespace ContinuousLinearMap

omit [CompleteSpace 𝕜] in
/-- The Fredholm index is additive under composition. -/
@[simp]
theorem index_comp (S : F →L[𝕜] G) (T : E →L[𝕜] F)
    (hS : ContinuousLinearMap.IsFredholm S) (hT : ContinuousLinearMap.IsFredholm T) :
    index (S.comp T) = index S + index T := by
  letI := hT.finite_ker
  letI := hT.finite_coker
  letI := hS.finite_ker
  letI := hS.finite_coker
  simp only [index_eq_finrank_sub]
  rw [ContinuousLinearMap.toLinearMap_comp]
  have h := LinearMap.index_comp (f := (T : E →ₗ[𝕜] F)) (S : F →ₗ[𝕜] G)
  simpa only [LinearMap.index_eq_finrank_sub] using h

end ContinuousLinearMap

section Pow

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {A : X →L[𝕜] X}

/-- Over a complete nontrivially normed scalar field, every natural-number power of a Fredholm
endomorphism is Fredholm. -/
theorem _root_.ContinuousLinearMap.IsFredholm.pow (hA : ContinuousLinearMap.IsFredholm A) :
    ∀ n : ℕ, ContinuousLinearMap.IsFredholm (A ^ n)
  | 0 => by
      rw [pow_zero, ContinuousLinearMap.one_def]
      exact isFredholm_id
  | n + 1 => by
      rw [pow_succ, ContinuousLinearMap.mul_def]
      exact (hA.pow n).comp hA

namespace ContinuousLinearMap

/-- The index of the `n`th power of a Fredholm endomorphism is `n` times its index. -/
@[simp]
theorem index_pow (A : X →L[𝕜] X) (hA : ContinuousLinearMap.IsFredholm A) (n : ℕ) :
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
