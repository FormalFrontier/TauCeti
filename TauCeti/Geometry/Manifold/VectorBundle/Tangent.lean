/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Tangent bundles of open submanifolds

This file identifies the tangent spaces and the local tangent-bundle trivializations of an open
submanifold with those of its ambient manifold.

## Main results

* `TauCeti.Manifold.tangentSpaceOpenEquiv`: the canonical continuous linear equivalence between
  the tangent space of an open submanifold and the ambient tangent space.
* `TauCeti.Manifold.tangentSpaceOpenEquiv_trivializationAt_symmL_eventuallyEq`: near a point, the
  inverse tangent-bundle trivializations agree through this equivalence.
-/

public section

open Bundle Filter Manifold TopologicalSpace
open scoped Bundle Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The canonical identification between the tangent space of an open submanifold and the ambient
tangent space. Both are Mathlib's type synonym for the common model vector space. -/
@[expose]
noncomputable def tangentSpaceOpenEquiv {U : Opens M} (x : U) :
    TangentSpace I x ≃L[ℝ] TangentSpace I (x : M) where
  toFun v := v
  invFun v := v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

@[simp]
theorem tangentSpaceOpenEquiv_apply {U : Opens M} (x : U) (v : TangentSpace I x) :
    tangentSpaceOpenEquiv (I := I) x v = v := by
  rfl

@[simp]
theorem tangentSpaceOpenEquiv_symm_apply {U : Opens M} (x : U)
    (v : TangentSpace I (x : M)) :
    (tangentSpaceOpenEquiv (I := I) x).symm v = v := by
  rfl

/-- Near a point of an open submanifold, its inverse tangent-bundle trivialization agrees with the
ambient inverse trivialization under the canonical tangent-space identification. -/
theorem tangentSpaceOpenEquiv_trivializationAt_symmL_eventuallyEq
    [IsManifold I 1 M] {U : Opens M} (x : U) :
    ∀ᶠ y in nhds x, ∀ z : E,
      tangentSpaceOpenEquiv (I := I) y
          ((trivializationAt E (TangentSpace I : U → Type _) x).symmL ℝ y z) =
        (trivializationAt E (TangentSpace I : M → Type _) (x : M)).symmL ℝ (y : M) z := by
  rcases mem_nhds_iff.mp
      (Opens.chartAt_subtype_val_symm_eventuallyEq (H := H) U (x := x)) with
    ⟨V, hV, hVopen, hxV⟩
  have hxV' : chartAt H x x ∈ V := by
    simpa [Opens.chartAt_eq] using hxV
  have hVevent : ∀ᶠ y in nhds x, chartAt H x y ∈ V :=
    ((chartAt H x).continuousAt (by simp)).eventually (hVopen.mem_nhds hxV')
  filter_upwards [
    (trivializationAt E (TangentSpace I : U → Type _) x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I : U → Type _) x),
    continuousAt_subtype_val.eventually
      ((trivializationAt E (TangentSpace I : M → Type _) (x : M)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) (x : M))),
    hVevent] with y hyU hyM hyV
  intro z
  have hyU' : y ∈ (chartAt H x).source := by
    simpa using hyU
  have hyM' : (y : M) ∈ (chartAt H (x : M)).source := by
    exact hyM
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
  have hd : fderivWithin ℝ
      (((↑I ∘ chartAt H (y : M)) ∘ (chartAt H (x : M)).symm) ∘ I.symm)
        (Set.range I) (I (chartAt H (x : M) (y : M))) =
      fderivWithin ℝ
        (((↑I ∘ chartAt H (y : M)) ∘ Subtype.val ∘ (chartAt H x).symm) ∘ I.symm)
          (Set.range I) (I (chartAt H (x : M) (y : M))) :=
    htrans.fderivWithin_eq_of_nhds
  rw [TangentBundle.symmL_trivializationAt_eq_core hyU',
    TangentBundle.symmL_trivializationAt_eq_core hyM']
  change (tangentBundleCore I U).coordChange (achart H x) (achart H y) y z =
    (tangentBundleCore I M).coordChange (achart H (x : M)) (achart H (y : M)) (y : M) z
  simpa [tangentBundleCore_coordChange_achart, Function.comp_def, Opens.chartAt_eq,
    tangentSpaceOpenEquiv] using DFunLike.congr_fun hd.symm z

end TauCeti.Manifold
