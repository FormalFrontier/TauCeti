/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Fredholm.Comp
public import TauCeti.Analysis.Fredholm.Criteria

/-!
# Fredholm operators from finite-codimension restrictions

Let `T : E →L[𝕜] F` carry a closed finite-codimensional subspace `E₁` into a closed
finite-codimensional subspace `F₁`. If the induced operator `E₁ →L[𝕜] F₁` is Fredholm,
then so is `T`. The index of `T` is the index of the restriction plus `codim E₁ - codim F₁`.

The proof chooses topological complements `E = E₁ ⊕ E₀` and `F = F₁ ⊕ F₀`. Extending the
restricted operator by projection onto `E₁` and inclusion from `F₁` gives a Fredholm operator
which agrees with `T` on `E₁`; their difference therefore has finite-dimensional range. The result
then follows from stability under finite-rank perturbations.

This is the finite-codimension reduction recorded as the missing
`ContinuousLinearMap.IsFredholm.of_restrict` in Mathlib's Fredholm API. It is a basic reduction for
the Fredholm-operator substrate in Lane F0 of the analytic Heegaard Floer roadmap, in particular
when an operator is first controlled after discarding finitely many modes.

## Main declarations

* `ContinuousLinearMap.IsFredholm.of_restrict`: a continuous linear map is Fredholm when its
  restriction between closed finite-codimensional subspaces is Fredholm.
* `TauCeti.ContinuousLinearMap.index_restrict`: the corresponding index formula.

The finite-codimension reduction and index convention follow McDuff--Salamon,
*J-holomorphic Curves and Symplectic Topology*, Appendix A.1. The proof reuses Mathlib's
topological complements and quasi-inverse characterization of Fredholm operators.
-/

public section

namespace TauCeti

open Module

section Topological

variable {K E F : Type*} [NontriviallyNormedField K] [CompleteSpace K]
variable [AddCommGroup E] [Module K E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul K E] [T2Space E]
variable [AddCommGroup F] [Module K F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul K F] [T2Space F]
variable {T : E →L[K] F} {E₁ : Submodule K E} {F₁ : Submodule K F}

omit [CompleteSpace K] [IsTopologicalAddGroup E] [ContinuousSMul K E] [T2Space E] in
private theorem isFredholm_subtypeL {p : Submodule K E} (hp : IsClosed (p : Set E)) [p.CoFG] :
    ContinuousLinearMap.IsFredholm p.subtypeL where
  isStrictMap := (Submodule.isEmbedding_subtypeL p).isStrictMap
  isClosed_range := by
    rw [Submodule.toLinearMap_subtypeL, Submodule.range_subtype]
    exact hp
  finite_ker := by
    rw [Submodule.toLinearMap_subtypeL, Submodule.ker_subtype]
    infer_instance
  finite_coker := by
    rw [Submodule.toLinearMap_subtypeL, Submodule.range_subtype]
    infer_instance
  closedComplemented_ker := by
    rw [Submodule.toLinearMap_subtypeL, Submodule.ker_subtype]
    exact Submodule.closedComplemented_bot

/-- A continuous linear map between Hausdorff topological vector spaces is Fredholm if its
restriction between closed finite-codimensional subspaces is Fredholm. -/
theorem _root_.ContinuousLinearMap.IsFredholm.of_restrict (hE₁ : IsClosed (E₁ : Set E))
    [E₁.CoFG] (hF₁ : IsClosed (F₁ : Set F)) [F₁.CoFG] (hT : Set.MapsTo T E₁ F₁)
    (hT₁ : ContinuousLinearMap.IsFredholm (T.restrict hT)) :
    ContinuousLinearMap.IsFredholm T := by
  obtain ⟨E₀, hE⟩ :=
    (Submodule.ClosedComplemented.of_finiteDimensional_quotient hE₁).exists_isTopCompl
  obtain ⟨F₀, hF⟩ :=
    (Submodule.ClosedComplemented.of_finiteDimensional_quotient hF₁).exists_isTopCompl
  letI : FiniteDimensional K E₀ :=
    .of_fg <| (inferInstance : E₁.CoFG).fg_of_isCompl hE.isCompl
  letI : FiniteDimensional K F₀ :=
    .of_fg <| (inferInstance : F₁.CoFG).fg_of_isCompl hF.isCompl
  let P : E →L[K] E₁ := E₁.projectionOntoL E₀ hE
  let ι : F₁ →L[K] F := F₁.subtypeL
  let S : E →L[K] F := ι.comp ((T.restrict hT).comp P)
  obtain ⟨Q, hQ⟩ := hT₁.exists_isQuasiInverse
  have hS : ContinuousLinearMap.IsFredholm S := by
    apply ContinuousLinearMap.IsFredholm.of_isQuasiInverse
      (v := (E₁.subtypeL.comp Q).comp (F₁.projectionOntoL F₀ hF))
    simpa only [S, P, ι, ContinuousLinearMap.toLinearMap_comp,
      Submodule.toLinearMap_subtypeL, Submodule.toLinearMap_projectionOntoL] using
      ((LinearMap.isQuasiInverse_subtype_projectionOnto hE.isCompl).comp hQ).comp
        (LinearMap.isQuasiInverse_subtype_projectionOnto hF.isCompl).symm
  have hS_on (x : E₁) : S (x : E) = T x := by
    simp only [ContinuousLinearMap.comp_apply, Submodule.projectionOntoL_apply_left,
      Submodule.coe_subtypeL, Submodule.subtype_apply, S, ι, P]
    exact congrArg Subtype.val (ContinuousLinearMap.restrict_apply hT x)
  have hker : E₁ ≤ LinearMap.ker ((T - S : E →L[K] F) : E →ₗ[K] F) := by
    intro x hx
    rw [LinearMap.mem_ker]
    exact sub_eq_zero.mpr (hS_on ⟨x, hx⟩).symm
  have hfinite :
      FiniteDimensional K (LinearMap.range ((T - S : E →L[K] F) : E →ₗ[K] F)) :=
    (Submodule.fg_iff_finiteDimensional _).mp
      (LinearMap.ker_coFG_iff_hasFiniteRange.mp
        (Submodule.CoFG.of_le hker inferInstance)).fg_range
  open scoped LinearMap.FiniteRangeSetoid in
    obtain ⟨Q', hQ'⟩ := hS.exists_isQuasiInverse
    apply ContinuousLinearMap.IsFredholm.of_isQuasiInverse (v := Q')
    apply hQ'.congr (Setoid.refl _)
    rw [LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange]
    exact (Submodule.fg_iff_finiteDimensional _).mpr hfinite

end Topological

variable {K E F : Type*} [NontriviallyNormedField K] [CompleteSpace K]
variable [NormedAddCommGroup E] [NormedSpace K E]
variable [NormedAddCommGroup F] [NormedSpace K F]
variable {T : E →L[K] F} {E₁ : Submodule K E} {F₁ : Submodule K F}

namespace ContinuousLinearMap

/-- The index of the restriction of a continuous linear map from `E` to `F` to closed
finite-codimensional subspaces `E₁` and `F₁` is the index of the full operator minus `codim E₁`
plus `codim F₁`. -/
theorem index_restrict (hE₁ : IsClosed (E₁ : Set E)) [E₁.CoFG]
    (hF₁ : IsClosed (F₁ : Set F)) [F₁.CoFG] (hT : Set.MapsTo T E₁ F₁)
    (hT₁ : ContinuousLinearMap.IsFredholm (T.restrict hT)) :
    index (T.restrict hT) = index T - (finrank K (E ⧸ E₁) : ℤ) + finrank K (F ⧸ F₁) := by
  have hTfull := ContinuousLinearMap.IsFredholm.of_restrict hE₁ hF₁ hT hT₁
  have hιE := isFredholm_subtypeL hE₁
  have hιF := isFredholm_subtypeL hF₁
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
