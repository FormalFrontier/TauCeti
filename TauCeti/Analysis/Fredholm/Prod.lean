/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Fredholm.Basic

/-!
# Products of Fredholm operators

This file proves that the Cartesian product of two Fredholm operators is Fredholm and that its
index is the sum of the two indices. This is elementary bookkeeping needed for the block
decompositions and finite-dimensional reductions in the Fredholm substrate of the analytic
Heegaard Floer roadmap.

The proof identifies the kernel and range of the product operator with the products of the
individual kernels and ranges. It also records the corresponding linear equivalence between the
cokernel of a product submodule and the product of the two cokernels.

## Main declarations

* `TauCeti.IsFredholm.prodMap`: a product of Fredholm operators is Fredholm.
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

namespace Submodule

/-- A product submodule, as a module, is the product of the two submodules. -/
private def prodSubtypeEquiv (p : Submodule K F₁) (q : Submodule K F₂) :
    ↥(p.prod q) ≃ₗ[K] p × q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun x := ⟨(x.1.1, x.2.1), x.1.2, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The quotient by a product of submodules is linearly equivalent to the product of the
quotients. This is kept private because the construction is general Mathlib infrastructure; only
its Fredholm consequences form the public API of this file. -/
private noncomputable def quotientProdEquiv (p : Submodule K F₁) (q : Submodule K F₂) :
    ((F₁ × F₂) ⧸ p.prod q) ≃ₗ[K] (F₁ ⧸ p) × (F₂ ⧸ q) := by
  let f : F₁ × F₂ →ₗ[K] (F₁ ⧸ p) × (F₂ ⧸ q) := p.mkQ.prodMap q.mkQ
  have hker : LinearMap.ker f = p.prod q := by
    simp [f]
  let g : ((F₁ × F₂) ⧸ p.prod q) →ₗ[K] (F₁ ⧸ p) × (F₂ ⧸ q) :=
    (p.prod q).liftQ f hker.ge
  refine LinearEquiv.ofBijective g ⟨?_, ?_⟩
  · exact LinearMap.ker_eq_bot.mp
      (Submodule.ker_liftQ_eq_bot (p.prod q) f hker.ge hker.le)
  · rintro ⟨⟨x⟩, ⟨y⟩⟩
    refine ⟨(p.prod q).mkQ (x, y), ?_⟩
    simp only [g, Submodule.mkQ_apply, Submodule.liftQ_apply, f, LinearMap.prodMap_apply,
      Submodule.Quotient.quot_mk_eq_mk]

/-- The cokernel of a product submodule has dimension equal to the sum of the dimensions of the
two cokernels. -/
private lemma finrank_quotient_prod (p : Submodule K F₁) (q : Submodule K F₂)
    [FiniteDimensional K (F₁ ⧸ p)] [FiniteDimensional K (F₂ ⧸ q)] :
    finrank K ((F₁ × F₂) ⧸ p.prod q) = finrank K (F₁ ⧸ p) + finrank K (F₂ ⧸ q) := by
  rw [(quotientProdEquiv p q).finrank_eq, finrank_prod]

end Submodule

variable {T : E₁ →L[K] F₁} {S : E₂ →L[K] F₂}

/-- The Cartesian product of two Fredholm operators is Fredholm. -/
lemma IsFredholm.prodMap (hT : IsFredholm T) (hS : IsFredholm S) :
    IsFredholm (T.prodMap S) := by
  haveI := hT.finiteDimensional_ker
  haveI := hS.finiteDimensional_ker
  haveI := hT.finiteDimensional_coker
  haveI := hS.finiteDimensional_coker
  refine ⟨?_, ?_, ?_⟩
  · rw [ContinuousLinearMap.coe_prodMap T S, LinearMap.ker_prodMap]
    exact (Submodule.prodSubtypeEquiv _ _).symm.finiteDimensional
  · rw [ContinuousLinearMap.coe_prodMap T S, LinearMap.range_prodMap]
    exact hT.isClosed_range.prod hS.isClosed_range
  · rw [ContinuousLinearMap.coe_prodMap T S, LinearMap.range_prodMap]
    exact (Submodule.quotientProdEquiv _ _).symm.finiteDimensional

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
  simp only [(Submodule.prodSubtypeEquiv _ _).finrank_eq,
    Submodule.finrank_quotient_prod, finrank_prod]
  omega

/-- The Fredholm index is additive under Cartesian products of Fredholm operators. -/
@[simp]
lemma index_prodMap (T : E₁ →L[K] F₁) (S : E₂ →L[K] F₂)
    (hT : IsFredholm T) (hS : IsFredholm S) :
    index (T.prodMap S) = index T + index S := by
  letI := hT.finiteDimensional_ker
  letI := hS.finiteDimensional_ker
  letI := hT.finiteDimensional_coker
  letI := hS.finiteDimensional_coker
  exact index_prodMap_of_finiteDimensional T S

end ContinuousLinearMap

end TauCeti
