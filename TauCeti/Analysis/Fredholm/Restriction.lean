/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Comp
public import TauCeti.Analysis.Fredholm.Criteria

/-!
# Fredholm operators from finite-codimension restrictions

Let `T : E →L[𝕜] F` carry a closed finite-codimensional subspace `E₁` into a closed
finite-codimensional subspace `F₁`. Mathlib's `ContinuousLinearMap.IsFredholm.of_restrict`
shows that `T` is Fredholm when the induced operator `E₁ →L[𝕜] F₁` is. This file records the
accompanying index formula: the index of `T` is the index of the restriction plus
`codim E₁ - codim F₁`. It is a basic reduction for the Fredholm-operator substrate in Lane F0
of the analytic Heegaard Floer roadmap, in particular when an operator is first controlled
after discarding finitely many modes.

## Main declarations

* `TauCeti.ContinuousLinearMap.index_restrict`: the index formula for the restriction of a
  continuous linear map to closed finite-codimensional subspaces.

The finite-codimension reduction and index convention follow McDuff--Salamon,
*J-holomorphic Curves and Symplectic Topology*, Appendix A.1. The proof factors `T` through
the inclusions of the subspaces and applies Mathlib's composition formula for the index.
-/

public section

namespace TauCeti

open Module

variable {K E F : Type*} [NontriviallyNormedField K] [CompleteSpace K]
variable [NormedAddCommGroup E] [NormedSpace K E]
variable [NormedAddCommGroup F] [NormedSpace K F]
variable {T : E →L[K] F} {E₁ : Submodule K E} {F₁ : Submodule K F}

namespace ContinuousLinearMap

/-- The index of the restriction of a continuous linear map from `E` to `F` to closed
finite-codimensional subspaces `E₁` and `F₁` is the index of the full operator minus `codim E₁`
plus `codim F₁`. -/
@[simp]
theorem index_restrict (hE₁ : IsClosed (E₁ : Set E)) [E₁.CoFG]
    (hF₁ : IsClosed (F₁ : Set F)) [F₁.CoFG] (hT : Set.MapsTo T E₁ F₁)
    (hT₁ : ContinuousLinearMap.IsFredholm (T.restrict hT)) :
    index (T.restrict hT) = index T - (finrank K (E ⧸ E₁) : ℤ) + finrank K (F ⧸ F₁) := by
  have hTfull := ContinuousLinearMap.IsFredholm.of_restrict hE₁ hF₁ hT hT₁
  have hιE := Submodule.isFredholm_subtypeL hE₁
  have hιF := Submodule.isFredholm_subtypeL hF₁
  have hfactor : T.comp E₁.subtypeL = F₁.subtypeL.comp (T.restrict hT) := by
    ext x
    exact (congrArg Subtype.val (ContinuousLinearMap.restrict_apply hT x)).symm
  have hdom := index_comp T E₁.subtypeL hTfull hιE
  have hcod := index_comp F₁.subtypeL (T.restrict hT) hιF hT₁
  have hEindex : index E₁.subtypeL = -(finrank K (E ⧸ E₁) : ℤ) := by
    rw [index_of_injective E₁.subtypeL Subtype.val_injective,
      Submodule.toLinearMap_subtypeL, Submodule.range_subtype]
  have hFindex : index F₁.subtypeL = -(finrank K (F ⧸ F₁) : ℤ) := by
    rw [index_of_injective F₁.subtypeL Subtype.val_injective,
      Submodule.toLinearMap_subtypeL, Submodule.range_subtype]
  rw [hfactor, hcod, hEindex, hFindex] at hdom
  omega

end ContinuousLinearMap

end TauCeti

end
