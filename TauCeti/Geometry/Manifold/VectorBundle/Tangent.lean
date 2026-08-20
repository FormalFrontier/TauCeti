/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Tangent bundles of open submanifolds

This file identifies the tangent spaces of an open submanifold with those of its ambient manifold
and shows that, near each point, the inverse tangent-bundle trivializations agree under that
identification.

## Main results

* `TauCeti.Manifold.tangentSpaceOpenEquiv`: the canonical continuous linear equivalence between
  the tangent space of an open submanifold and the ambient tangent space.
* `TauCeti.Manifold.mfderiv_subtype_val`: the differential of the inclusion is the canonical
  tangent-space equivalence.
* `TauCeti.Manifold.eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq`: near a point, the
  inverse tangent-bundle trivializations agree through this equivalence.
-/

public section

open Bundle Filter Manifold TopologicalSpace
open scoped Bundle Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The canonical identification between the tangent space of an open submanifold and the ambient
tangent space. Both are Mathlib's type synonym for the common model vector space. -/
noncomputable def tangentSpaceOpenEquiv {U : Opens M} (x : U) :
    TangentSpace I x ≃L[𝕜] TangentSpace I (x : M) where
  toFun v := v
  invFun v := v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

theorem tangentSpaceOpenEquiv_apply {U : Opens M} (x : U) (v : TangentSpace I x) :
    tangentSpaceOpenEquiv (I := I) x v = v := by
  exact (rfl)

theorem tangentSpaceOpenEquiv_symm_apply {U : Opens M} (x : U)
    (v : TangentSpace I (x : M)) :
    (tangentSpaceOpenEquiv (I := I) x).symm v = v := by
  exact (rfl)

/-- In inherited charts, the tangent-bundle coordinate changes of an open submanifold and its
ambient manifold agree locally. -/
private theorem eventually_tangentBundleCore_coordChange_open_eq
    [IsManifold I 1 M] {U : Opens M} (x : U) :
    ∀ᶠ y in nhds x,
      (tangentBundleCore I U).coordChange (achart H x) (achart H y) y =
        (tangentBundleCore I M).coordChange
          (achart H (x : M)) (achart H (y : M)) (y : M) := by
  rcases mem_nhds_iff.mp
      (Opens.chartAt_subtype_val_symm_eventuallyEq (H := H) U (x := x)) with
    ⟨V, hV, hVopen, hxV⟩
  have hxV' : chartAt H x x ∈ V := by
    simpa [Opens.chartAt_eq] using hxV
  have hVevent : ∀ᶠ y in nhds x, chartAt H x y ∈ V :=
    ((chartAt H x).continuousAt (by simp)).eventually (hVopen.mem_nhds hxV')
  filter_upwards [hVevent] with y hyV
  have hinv : (chartAt H (x : M)).symm =ᶠ[nhds (chartAt H (x : M) (y : M))]
      Subtype.val ∘ (chartAt H x).symm :=
    Filter.eventuallyEq_of_mem (hVopen.mem_nhds hyV) hV
  have hIsymm : Tendsto I.symm
      (nhds (I (chartAt H (x : M) (y : M))))
      (nhds (chartAt H (x : M) (y : M))) := by
    have hc : Tendsto I.symm
        (nhds (I (chartAt H (x : M) (y : M))))
        (nhds (I.symm (I (chartAt H (x : M) (y : M))))) :=
      I.continuous_symm.continuousAt
    simpa only [I.left_inv] using hc
  have htrans := Filter.EventuallyEq.comp_tendsto
    (hinv.fun_comp (↑I ∘ chartAt H (y : M))) hIsymm
  have hd : fderivWithin 𝕜
      (((↑I ∘ chartAt H (y : M)) ∘ (chartAt H (x : M)).symm) ∘ I.symm)
        (Set.range I) (I (chartAt H (x : M) (y : M))) =
      fderivWithin 𝕜
        (((↑I ∘ chartAt H (y : M)) ∘ Subtype.val ∘ (chartAt H x).symm) ∘ I.symm)
          (Set.range I) (I (chartAt H (x : M) (y : M))) :=
    htrans.fderivWithin_eq_of_nhds
  ext z
  simpa [tangentBundleCore_coordChange_achart, Function.comp_def, Opens.chartAt_eq,
    tangentSpaceOpenEquiv_apply] using DFunLike.congr_fun hd.symm z

/-- The differential of the inclusion of an open submanifold is the canonical tangent-space
identification. -/
theorem mfderiv_subtype_val {U : Opens M} (x : U) :
    mfderiv I I (Subtype.val : U → M) x =
      (tangentSpaceOpenEquiv (I := I) x).toContinuousLinearMap := by
  ext v
  change mfderiv I I (Subtype.val : U → M) x v = v
  rw [mfderiv]
  simp only [contMDiff_subtype_val.mdifferentiableAt one_ne_zero, ↓reduceIte]
  have h : writtenInExtChartAt I I x (Subtype.val : U → M) =ᶠ[
      nhdsWithin (extChartAt I x x) (Set.range I)] id := by
    have hmem : I.symm ⁻¹' (chartAt H x).target ∩ Set.range I ∈
        nhdsWithin (extChartAt I x x) (Set.range I) := by
      rw [← I.image_eq (chartAt H x).target]
      exact (chartAt H x).extend_image_target_mem_nhds (mem_chart_source H x)
    filter_upwards [hmem] with y hy
    rcases hy with ⟨hyT, ⟨z, rfl⟩⟩
    have hzT : z ∈ (chartAt H x).target := by
      simpa only [Set.mem_preimage, I.left_inv] using hyT
    simp only [writtenInExtChartAt, Function.comp_apply, extChartAt,
      OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm, I.left_inv, id_eq]
    rw [show ((chartAt H x).symm z : M) = (chartAt H (x : M)).symm z from
      (chartAt H (x : M)).subtypeRestr_symm_apply ⟨x⟩ hzT]
    simp only [(chartAt H (x : M)).right_inv
        ((chartAt H (x : M)).subtypeRestr_target_subset ⟨x⟩ hzT)]
  have hxRange : extChartAt I x x ∈ Set.range I :=
    ⟨chartAt H x x, rfl⟩
  rw [h.fderivWithin_eq_of_mem hxRange,
    fderivWithin_id
      (I.uniqueDiffOn.uniqueDiffWithinAt hxRange)]
  rfl

/-- Near a point of an open submanifold, its inverse tangent-bundle trivialization agrees with the
ambient inverse trivialization under the canonical tangent-space identification. -/
theorem eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq
    [IsManifold I 1 M] {U : Opens M} (x : U) :
    ∀ᶠ y in nhds x, ∀ z : E,
      tangentSpaceOpenEquiv (I := I) y
          ((trivializationAt E (TangentSpace I : U → Type _) x).symmL 𝕜 y z) =
        (trivializationAt E (TangentSpace I : M → Type _) (x : M)).symmL 𝕜 (y : M) z := by
  filter_upwards [
    (trivializationAt E (TangentSpace I : U → Type _) x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I : U → Type _) x),
    continuousAt_subtype_val.eventually
      ((trivializationAt E (TangentSpace I : M → Type _) (x : M)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) (x : M))),
    eventually_tangentBundleCore_coordChange_open_eq (I := I) x] with y hyU hyM hcoord
  intro z
  have hyU' : y ∈ (chartAt H x).source := by
    simpa using hyU
  have hyM' : (y : M) ∈ (chartAt H (x : M)).source := by
    exact hyM
  rw [TangentBundle.symmL_trivializationAt_eq_core hyU',
    TangentBundle.symmL_trivializationAt_eq_core hyM']
  -- The preceding rewrites identify the two `symmL` maps with core coordinate changes, but their
  -- applications still use the definitional identification `TangentSpace I b = E`. The following
  -- `change` intentionally unfolds those map coercions and the local `tangentSpaceOpenEquiv`; no
  -- application-level rewrite lemma exposes this conversion.
  change (tangentBundleCore I U).coordChange (achart H x) (achart H y) y z =
    (tangentBundleCore I M).coordChange (achart H (x : M)) (achart H (y : M)) (y : M) z
  exact DFunLike.congr_fun hcoord z

end TauCeti.Manifold
