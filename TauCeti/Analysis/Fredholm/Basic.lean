/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic

/-!
# Fredholm operators

This file connects Mathlib's analytic notion of a **Fredholm operator** to the nonlinear-analysis
substrate of the analytic Heegaard Floer roadmap (Lane F0, "Fredholm operators and index theory").
All Fredholm hypotheses use `ContinuousLinearMap.IsFredholm` directly. That predicate asks for a
strict map with closed range, finite-dimensional kernel and cokernel, and a topologically
complemented kernel. Between Banach spaces over an `IsRCLikeNormedField` the strictness,
closed-range and complemented-kernel conditions are automatic, so the predicate is *equivalent*
there to finite dimensionality of the kernel and cokernel alone; that equivalence is proved and
exposed as `TauCeti.isFredholm_iff_finite_ker_coker` in `TauCeti.Analysis.Fredholm.ClosedRange`.
Outside that setting `ContinuousLinearMap.IsFredholm` is genuinely stronger, and it is the notion
intended throughout.

## Main declarations

* `TauCeti.isFredholm_of_finiteDimensional`: every operator between finite-dimensional spaces is
  Fredholm.
* `ContinuousLinearMap.IsFredholm.neg`, `ContinuousLinearMap.IsFredholm.smul`: Fredholmness is
  preserved by negation and by nonzero scalar multiples.
* `ContinuousLinearMap.IsFredholm.comp_equiv` and
  `ContinuousLinearMap.IsFredholm.equiv_comp`: composing with a continuous linear equivalence on
  either side preserves Fredholmness. Mathlib provides stronger `↔` versions over complete scalar
  fields; these implications hold over any `NontriviallyNormedField`.

The Fredholm index and its elementary API live in `TauCeti.Analysis.Fredholm.Index`.
-/

public section

namespace TauCeti

open Module

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

section FiniteDimensional

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- Every continuous linear map between finite-dimensional spaces is Fredholm. -/
lemma isFredholm_of_finiteDimensional (T : E →L[𝕜] F) : ContinuousLinearMap.IsFredholm T where
  isStrictMap := T.isStrictMap_of_finiteDimensional
  isClosed_range := (LinearMap.range (T : E →ₗ[𝕜] F)).closed_of_finiteDimensional
  finite_ker := inferInstance
  finite_coker := inferInstance
  closedComplemented_ker :=
    Submodule.ClosedComplemented.of_finiteDimensional_of_le
      Submodule.closedComplemented_top le_top

end FiniteDimensional

/-- A nonzero scalar multiple of a Fredholm operator is Fredholm. -/
lemma _root_.ContinuousLinearMap.IsFredholm.smul {T : E →L[𝕜] F}
    (hT : ContinuousLinearMap.IsFredholm T) {c : 𝕜} (hc : c ≠ 0) :
    ContinuousLinearMap.IsFredholm (c • T) where
  isStrictMap := by
    -- `IsStrictMap` is phrased for functions; unfold the bundled scalar action to match it.
    change Topology.IsStrictMap (fun x ↦ c • T x)
    exact (Homeomorph.smulOfNeZero c hc).comp_isStrictMap_iff.mpr hT.isStrictMap
  isClosed_range := by
    rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.range_smul _ _ hc]
    exact hT.isClosed_range
  finite_ker := by
    rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.ker_smul _ _ hc]
    exact hT.finite_ker
  finite_coker := by
    rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.range_smul _ _ hc]
    exact hT.finite_coker
  closedComplemented_ker := by
    rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.ker_smul _ _ hc]
    exact hT.closedComplemented_ker

/-- The negation of a Fredholm operator is Fredholm. -/
lemma _root_.ContinuousLinearMap.IsFredholm.neg {T : E →L[𝕜] F}
    (hT : ContinuousLinearMap.IsFredholm T) : ContinuousLinearMap.IsFredholm (-T) := by
  simpa using hT.smul (c := -1) (by norm_num)

section CompEquiv

variable {T : E →L[𝕜] F}

/-- A continuous linear equivalence carries a complemented submodule to a complemented
submodule. -/
private lemma closedComplemented_map_continuousLinearEquiv (e : E ≃L[𝕜] F)
    (p : Submodule 𝕜 E) (hp : p.ClosedComplemented) :
    (p.map (e : E →ₗ[𝕜] F)).ClosedComplemented := by
  obtain ⟨P, hP⟩ := hp
  let ep := e.submoduleMap p
  refine ⟨ep.toContinuousLinearMap.comp (P.comp (e.symm : F →L[𝕜] E)), ?_⟩
  intro y
  have h := congrArg ep (hP (ep.symm y))
  simpa only [ep, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.submoduleMap_apply,
    ContinuousLinearEquiv.submoduleMap_symm_apply,
    ep.apply_symm_apply] using h

/-- The kernel of `e.comp T` is the kernel of `T`, since `e` is injective. Used by
`ContinuousLinearMap.IsFredholm.equiv_comp`. -/
private lemma ker_equiv_comp (T : E →L[𝕜] F) (e : F ≃L[𝕜] G) :
    LinearMap.ker (((e : F →L[𝕜] G).comp T : E →L[𝕜] G) : E →ₗ[𝕜] G) =
      LinearMap.ker (T : E →ₗ[𝕜] F) := by
  rw [ContinuousLinearMap.toLinearMap_comp]
  rw [ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]
  rw [LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.2 e.injective)]

/-- The range of `T.comp e` is the range of `T`, since `e` is surjective. Used by
`ContinuousLinearMap.IsFredholm.comp_equiv`. -/
private lemma range_comp_equiv (T : E →L[𝕜] F) (e : G ≃L[𝕜] E) :
    LinearMap.range ((T.comp (e : G →L[𝕜] E) : G →L[𝕜] F) : G →ₗ[𝕜] F) =
      LinearMap.range (T : E →ₗ[𝕜] F) := by
  rw [ContinuousLinearMap.toLinearMap_comp]
  rw [ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]
  rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 e.surjective)]

/-- The kernel of `T.comp e` is the image of the kernel of `T` under `e⁻¹`. Used by
`ContinuousLinearMap.IsFredholm.comp_equiv`. -/
private lemma ker_comp_equiv (T : E →L[𝕜] F) (e : G ≃L[𝕜] E) :
    LinearMap.ker ((T.comp (e : G →L[𝕜] E) : G →L[𝕜] F) : G →ₗ[𝕜] F) =
      (LinearMap.ker (T : E →ₗ[𝕜] F)).map (e.toLinearEquiv.symm : E →ₗ[𝕜] G) := by
  rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.ker_comp]
  rw [ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]
  rw [Submodule.comap_equiv_eq_map_symm]

/-- Postcomposing a Fredholm operator with a continuous linear equivalence yields a Fredholm
operator.

This is the `mpr` direction of Mathlib's `ContinuousLinearMap.isFredholm_equiv_comp`, which
states the `↔` and so is stronger, but assumes a complete scalar field. Transporting the structure
fields directly proves this implication over any `NontriviallyNormedField`. -/
lemma _root_.ContinuousLinearMap.IsFredholm.equiv_comp
    (hT : ContinuousLinearMap.IsFredholm T) (e : F ≃L[𝕜] G) :
    ContinuousLinearMap.IsFredholm ((e : F →L[𝕜] G).comp T) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Expose function composition so the homeomorphism strictness lemma applies.
    change Topology.IsStrictMap (fun x ↦ e (T x))
    exact e.toHomeomorph.comp_isStrictMap_iff.mpr hT.isStrictMap
  · rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp]
    simpa [Submodule.map_coe] using e.isClosed_image.2 hT.isClosed_range
  · rw [ker_equiv_comp T e]
    exact hT.finite_ker
  · rw [ContinuousLinearMap.toLinearMap_comp,
      ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap, LinearMap.range_comp]
    have := hT.finite_coker
    exact (Submodule.Quotient.equiv _ _ e.toLinearEquiv rfl).finiteDimensional
  · rw [ker_equiv_comp T e]
    exact hT.closedComplemented_ker

/-- Precomposing a Fredholm operator with a continuous linear equivalence yields a Fredholm
operator.

This is the `mpr` direction of Mathlib's `ContinuousLinearMap.isFredholm_comp_equiv`, which
states the `↔` and so is stronger, but assumes a complete scalar field. Transporting the structure
fields directly proves this implication over any `NontriviallyNormedField`. -/
lemma _root_.ContinuousLinearMap.IsFredholm.comp_equiv (hT : ContinuousLinearMap.IsFredholm T)
    (e : G ≃L[𝕜] E) :
    ContinuousLinearMap.IsFredholm (T.comp (e : G →L[𝕜] E)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Expose function composition so the homeomorphism strictness lemma applies.
    change Topology.IsStrictMap (fun x ↦ T (e x))
    exact e.toHomeomorph.isStrictMap_comp_iff.mpr hT.isStrictMap
  · rw [range_comp_equiv T e]
    exact hT.isClosed_range
  · rw [ker_comp_equiv T e]
    have := hT.finite_ker
    exact (e.symm.submoduleMap _).finiteDimensional
  · rw [range_comp_equiv T e]
    exact hT.finite_coker
  · rw [ker_comp_equiv T e]
    exact closedComplemented_map_continuousLinearEquiv e.symm _ hT.closedComplemented_ker

end CompEquiv

end TauCeti
