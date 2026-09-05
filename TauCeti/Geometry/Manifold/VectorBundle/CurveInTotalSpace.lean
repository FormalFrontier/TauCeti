/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

/-!
# Differentiating a curve into the total space of a fibre bundle

A curve `z` into the total space of a fibre bundle is read, near a parameter `t`, in the chart of
the total space centred at `z t`.  By `FiberBundle.extChartAt` that chart is the trivialization at
the base point `(z t).proj` followed by the base chart there, so the reading of `z` is the pair of
its base curve read in the base chart and of its fibre coordinate read in that trivialization.
This file turns that observation into a criterion: the curve has a manifold derivative within a
parameter set exactly when it is continuous there and those two coordinate readings have
derivatives.

The criterion is the form in which a curve into a vector bundle is compared with a pair of
ordinary derivatives, and in particular the form in which an integral curve of a vector field on
a tangent bundle is unpacked into an equation on its base curve and one on its velocity.

## Main results

* `TauCeti.Manifold.hasMFDerivWithinAt_totalSpace_curve_iff`: the manifold derivative of a curve
  into a total space, within a parameter set, read as the pair of the derivative of its base
  curve in the base chart and of the derivative of its fibre coordinate in the trivialization,
  both taken at the current point of the curve.
* `TauCeti.Manifold.hasMFDerivAt_totalSpace_curve_iff`: its unrestricted case.

-/

public section

open Bundle Filter Set
open scoped Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {𝕜 B F : Type*} {V : B → Type*}
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace B] [ChartedSpace HB B] [FiberBundle F V]
  {z : 𝕜 → TotalSpace F V} {s : Set 𝕜} {t : 𝕜} {a : EB} {b : F}

/-- A curve into the total space which is continuous within `s` at `t` has a manifold derivative
there exactly when its base curve, read in the base chart at the current base point, and its fibre
coordinate, read in the trivialization at that same point, have the corresponding derivatives.
This is `TauCeti.Manifold.hasMFDerivWithinAt_totalSpace_curve_iff` with the continuity of the curve
supplied as a hypothesis rather than as a conjunct. -/
theorem hasMFDerivWithinAt_totalSpace_curve_iff_of_continuousWithinAt
    (hz : ContinuousWithinAt z s t) :
    HasMFDerivWithinAt 𝓘(𝕜, 𝕜) (IB.prod 𝓘(𝕜, F)) z s t ((1 : 𝕜 →L[𝕜] 𝕜).smulRight (a, b)) ↔
      HasDerivWithinAt (fun r ↦ extChartAt IB (z t).proj (z r).proj) a s t ∧
        HasDerivWithinAt (fun r ↦ (trivializationAt F V (z t).proj (z r)).2) b s t := by
  set x₀ := (z t).proj
  set e := trivializationAt F V x₀
  have hmem : ∀ᶠ r in 𝓝[s] t, (z r).proj ∈ e.baseSet :=
    hz.preimage_mem_nhdsWithin
      ((e.open_baseSet.preimage (FiberBundle.continuous_proj F V)).mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt F V x₀))
  have hfun : writtenInExtChartAt 𝓘(𝕜, 𝕜) (IB.prod 𝓘(𝕜, F)) t z =ᶠ[𝓝[s] t]
      fun r ↦ (extChartAt IB x₀ (z r).proj, (e (z r)).2) := by
    filter_upwards [hmem] with r hr
    rw [writtenInExtChartAt, FiberBundle.extChartAt, extChartAt_model_space_eq_id]
    simp only [PartialEquiv.refl_symm, PartialEquiv.refl_coe, Function.comp_apply, id_eq,
      PartialEquiv.trans_apply, PartialEquiv.prod_coe, OpenPartialHomeomorph.coe_toPartialEquiv,
      Trivialization.coe_coe]
    rw [Trivialization.coe_fst _ (e.mem_source.2 hr)]
  have hx : writtenInExtChartAt 𝓘(𝕜, 𝕜) (IB.prod 𝓘(𝕜, F)) t z t =
      (extChartAt IB x₀ (z t).proj, (e (z t)).2) := by
    rw [writtenInExtChartAt, FiberBundle.extChartAt, extChartAt_model_space_eq_id]
    simp only [PartialEquiv.refl_symm, PartialEquiv.refl_coe, Function.comp_apply, id_eq,
      PartialEquiv.trans_apply, PartialEquiv.prod_coe, OpenPartialHomeomorph.coe_toPartialEquiv,
      Trivialization.coe_coe]
    rw [Trivialization.coe_fst _
      (e.mem_source.2 (FiberBundle.mem_baseSet_trivializationAt F V x₀))]
  have key : HasMFDerivWithinAt 𝓘(𝕜, 𝕜) (IB.prod 𝓘(𝕜, F)) z s t
        ((1 : 𝕜 →L[𝕜] 𝕜).smulRight (a, b)) ↔
      HasDerivWithinAt (fun r ↦ (extChartAt IB x₀ (z r).proj, (e (z r)).2)) (a, b) s t := by
    -- There is no general characterization theorem for `HasMFDerivWithinAt` with a manifold
    -- target, so expose its defining continuity-and-chart-derivative pair before simplifying the
    -- model spaces and replacing the written chart map by `hfun`.
    change (ContinuousWithinAt z s t ∧ _) ↔ _
    rw [extChartAt_model_space_eq_id]
    simp only [PartialEquiv.refl_symm, PartialEquiv.refl_coe, preimage_id_eq, id_eq,
      ModelWithCorners.range_eq_univ, inter_univ, and_iff_right hz]
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← hfun.hasFDerivWithinAt_iff hx]
    rfl
  rw [key]
  refine ⟨fun h ↦ ?_, fun h ↦ h.1.prodMk h.2⟩
  have h' := hasDerivWithinAt_iff_hasFDerivWithinAt.1 h
  exact ⟨hasDerivWithinAt_iff_hasFDerivWithinAt.2
      (h'.fst.congr_fderiv (ContinuousLinearMap.ext fun _ ↦ rfl)),
    hasDerivWithinAt_iff_hasFDerivWithinAt.2
      (h'.snd.congr_fderiv (ContinuousLinearMap.ext fun _ ↦ rfl))⟩

/-- **The manifold derivative of a curve into a total space.**  A curve into the total space of a
fibre bundle has the manifold derivative determined by `(a, b)` within the parameter set `s` at
`t` exactly when it is continuous there, its base curve read in the base chart at the current base
point has derivative `a`, and its fibre coordinate read in the trivialization at that point has
derivative `b`. -/
theorem hasMFDerivWithinAt_totalSpace_curve_iff :
    HasMFDerivWithinAt 𝓘(𝕜, 𝕜) (IB.prod 𝓘(𝕜, F)) z s t ((1 : 𝕜 →L[𝕜] 𝕜).smulRight (a, b)) ↔
      ContinuousWithinAt z s t ∧
        HasDerivWithinAt (fun r ↦ extChartAt IB (z t).proj (z r).proj) a s t ∧
          HasDerivWithinAt (fun r ↦ (trivializationAt F V (z t).proj (z r)).2) b s t := by
  refine ⟨fun h ↦ ⟨h.1, (hasMFDerivWithinAt_totalSpace_curve_iff_of_continuousWithinAt h.1).1 h⟩,
    fun h ↦ (hasMFDerivWithinAt_totalSpace_curve_iff_of_continuousWithinAt h.1).2 h.2⟩

/-- The unrestricted case of `TauCeti.Manifold.hasMFDerivWithinAt_totalSpace_curve_iff`. -/
theorem hasMFDerivAt_totalSpace_curve_iff :
    HasMFDerivAt 𝓘(𝕜, 𝕜) (IB.prod 𝓘(𝕜, F)) z t ((1 : 𝕜 →L[𝕜] 𝕜).smulRight (a, b)) ↔
      ContinuousAt z t ∧
        HasDerivAt (fun r ↦ extChartAt IB (z t).proj (z r).proj) a t ∧
          HasDerivAt (fun r ↦ (trivializationAt F V (z t).proj (z r)).2) b t := by
  refine hasMFDerivWithinAt_univ.symm.trans ?_
  rw [hasMFDerivWithinAt_totalSpace_curve_iff, continuousWithinAt_univ, hasDerivWithinAt_univ,
    hasDerivWithinAt_univ]

end TauCeti.Manifold

end
