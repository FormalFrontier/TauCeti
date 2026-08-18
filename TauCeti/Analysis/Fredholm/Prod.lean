/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Index
public import TauCeti.LinearAlgebra.Quotient.Prod

/-!
# Products of Fredholm operators

This file proves that the Cartesian product of two Fredholm operators is Fredholm and that its
index is the sum of the two indices. This is elementary bookkeeping needed for the block
decompositions and finite-dimensional reductions in the Fredholm substrate of the analytic
Heegaard Floer roadmap.

The proof identifies the kernel and range of the product operator with the products of the
individual kernels and ranges, and counts the cokernel with `Submodule.finrank_quotient_prod`.

## Main declarations

* `ContinuousLinearMap.IsFredholm.prodMap`: a product of Fredholm operators is Fredholm.
* `TauCeti.ContinuousLinearMap.index_prodMap`: the Fredholm index is additive under products.
-/

public section

namespace TauCeti

open Module

variable {K E₁ E₂ F₁ F₂ : Type*}
variable [NontriviallyNormedField K]
variable [NormedAddCommGroup E₁] [NormedSpace K E₁]
variable [NormedAddCommGroup E₂] [NormedSpace K E₂]
variable [NormedAddCommGroup F₁] [NormedSpace K F₁]
variable [NormedAddCommGroup F₂] [NormedSpace K F₂]

variable {T : E₁ →L[K] F₁} {S : E₂ →L[K] F₂}

/-- The Cartesian product of two Fredholm operators is Fredholm. -/
lemma _root_.ContinuousLinearMap.IsFredholm.prodMap
    (hT : ContinuousLinearMap.IsFredholm T) (hS : ContinuousLinearMap.IsFredholm S) :
    ContinuousLinearMap.IsFredholm (T.prodMap S) := by
  have := hT.finite_ker
  have := hS.finite_ker
  have := hT.finite_coker
  have := hS.finite_coker
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `LinearMap.isStrictMap_prodMap` is stated for the underlying linear maps.
    change Topology.IsStrictMap ⇑((T : E₁ →ₗ[K] F₁).prodMap (S : E₂ →ₗ[K] F₂))
    exact LinearMap.isStrictMap_prodMap hT.isStrictMap hS.isStrictMap
  · rw [ContinuousLinearMap.coe_prodMap T S, LinearMap.range_prodMap]
    exact hT.isClosed_range.prod hS.isClosed_range
  · rw [ContinuousLinearMap.coe_prodMap T S, LinearMap.ker_prodMap]
    exact (Submodule.prodEquiv _ _).symm.finiteDimensional
  · rw [ContinuousLinearMap.coe_prodMap T S, LinearMap.range_prodMap]
    exact (Submodule.quotientProdEquiv _ _).symm.finiteDimensional
  · rw [ContinuousLinearMap.coe_prodMap T S, LinearMap.ker_prodMap]
    obtain ⟨PT, hPT⟩ := hT.closedComplemented_ker
    obtain ⟨PS, hPS⟩ := hS.closedComplemented_ker
    let P : E₁ × E₂ →L[K] E₁ × E₂ :=
      (T.ker.subtypeL.prodMap S.ker.subtypeL).comp (PT.prodMap PS)
    refine ⟨P.codRestrict (T.ker.prod S.ker) ?_, ?_⟩
    · rintro ⟨x, y⟩
      exact ⟨(PT x).property, (PS y).property⟩
    · rintro ⟨⟨x, y⟩, hx, hy⟩
      apply Subtype.ext
      -- Rewrite the corestricted product projection as its two component projections.
      rw [ContinuousLinearMap.coe_codRestrict_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_prodMap', ContinuousLinearMap.coe_prodMap', Prod.map_apply,
        Prod.map_apply, Submodule.subtypeL_apply, Submodule.subtypeL_apply, hPT ⟨x, hx⟩,
        hPS ⟨y, hy⟩]

namespace ContinuousLinearMap

/-- The index is additive under Cartesian products when both kernels and cokernels are finite
dimensional. -/
private lemma index_prodMap_of_finiteDimensional (T : E₁ →L[K] F₁) (S : E₂ →L[K] F₂)
    [FiniteDimensional K (LinearMap.ker (T : E₁ →ₗ[K] F₁))]
    [FiniteDimensional K (LinearMap.ker (S : E₂ →ₗ[K] F₂))]
    [FiniteDimensional K (F₁ ⧸ LinearMap.range (T : E₁ →ₗ[K] F₁))]
    [FiniteDimensional K (F₂ ⧸ LinearMap.range (S : E₂ →ₗ[K] F₂))] :
    index (T.prodMap S) = index T + index S := by
  simp only [index_eq_finrank_sub]
  rw [ContinuousLinearMap.coe_prodMap T S, LinearMap.ker_prodMap, LinearMap.range_prodMap]
  simp only [(Submodule.prodEquiv _ _).finrank_eq,
    Submodule.finrank_quotient_prod, finrank_prod]
  omega

/-- The Fredholm index is additive under Cartesian products of Fredholm operators. -/
@[simp]
lemma index_prodMap (T : E₁ →L[K] F₁) (S : E₂ →L[K] F₂)
    (hT : ContinuousLinearMap.IsFredholm T) (hS : ContinuousLinearMap.IsFredholm S) :
    index (T.prodMap S) = index T + index S := by
  let := hT.finite_ker
  let := hS.finite_ker
  let := hT.finite_coker
  let := hS.finite_coker
  exact index_prodMap_of_finiteDimensional T S

end ContinuousLinearMap

end TauCeti
