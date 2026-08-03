/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Calculus on spaces of continuous maps

This file develops the bounded pointwise operations needed to differentiate superposition maps on
spaces of continuous functions over a compact domain.

## Main results

* `ContinuousMap.applyContinuousLinearMap`: pointwise application of a continuous family of
  continuous linear maps, as a bounded bilinear operator.
* `ContinuousMap.hasStrictFDerivAt_comp_const`: strict differentiability of pointwise
  postcomposition at a constant map.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The exponential map".
-/

public section

open scoped ContinuousMap

noncomputable section

namespace ContinuousMap

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Pointwise application of a continuous family of continuous linear maps to a continuous map,
as a bounded bilinear operator. -/
noncomputable def applyContinuousLinearMap :
    C(K, E →L[𝕜] F) →L[𝕜] C(K, E) →L[𝕜] C(K, F) := by
  let app (A : C(K, E →L[𝕜] F)) : C(K, E) →L[𝕜] C(K, F) :=
    LinearMap.mkContinuous
      { toFun := fun f => ⟨fun x => A x (f x), by fun_prop⟩
        map_add' := fun _ _ => by ext x; simp
        map_smul' := fun _ _ => by ext x; simp }
      ‖A‖ fun f => by
      apply (ContinuousMap.norm_le _
        (mul_nonneg (norm_nonneg A) (norm_nonneg f))).2
      intro x
      exact (ContinuousLinearMap.le_opNorm (A x) (f x)).trans <|
        mul_le_mul (norm_coe_le_norm A x) (norm_coe_le_norm f x)
          (norm_nonneg _) (norm_nonneg _)
  let L : C(K, E →L[𝕜] F) →ₗ[𝕜] C(K, E) →L[𝕜] C(K, F) :=
    { toFun := app
      map_add' := fun _ _ => by ext f x; simp [app]
      map_smul' := fun _ _ => by ext f x; simp [app] }
  exact LinearMap.mkContinuous (𝕜₂ := 𝕜) L 1 fun
      (A : C(K, E →L[𝕜] F)) => by
    change ‖app A‖ ≤ 1 * ‖A‖
    rw [one_mul]
    apply ContinuousLinearMap.opNorm_le_bound (app A) (norm_nonneg A)
    intro f
    apply (ContinuousMap.norm_le _
      (mul_nonneg (norm_nonneg A) (norm_nonneg f))).2
    intro x
    exact (ContinuousLinearMap.le_opNorm (A x) (f x)).trans <|
      mul_le_mul (norm_coe_le_norm A x) (norm_coe_le_norm f x)
        (norm_nonneg _) (norm_nonneg _)

@[simp]
theorem applyContinuousLinearMap_apply (A : C(K, E →L[𝕜] F)) (f : C(K, E)) (x : K) :
    applyContinuousLinearMap A f x = A x (f x) :=
  by
    rw [applyContinuousLinearMap]
    rfl

/-- Strict differentiability of a map lifts to strict differentiability of pointwise
postcomposition at a constant continuous map. The derivative acts pointwise by the original
derivative. -/
theorem hasStrictFDerivAt_comp_const (f : C(E, F)) (f' : E →L[𝕜] F) (x : E)
    (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun g : C(K, E) ↦ f.comp g)
      (applyContinuousLinearMap (ContinuousMap.const K f')) (ContinuousMap.const K x) := by
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff] at hf ⊢
  intro c hc
  obtain ⟨r, hr, hbound⟩ := Metric.eventually_nhds_iff_ball.mp (hf hc)
  rw [Metric.eventually_nhds_iff_ball]
  refine ⟨r, hr, fun p hp ↦ ?_⟩
  apply (ContinuousMap.norm_le _ (mul_nonneg hc.le (norm_nonneg _))).2
  intro t
  have hpt : (p.1 t, p.2 t) ∈ Metric.ball (x, x) r := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hp
    exact ⟨(ContinuousMap.dist_apply_le_dist t).trans_lt hp.1,
      (ContinuousMap.dist_apply_le_dist t).trans_lt hp.2⟩
  calc
    ‖(f.comp p.1 - f.comp p.2 -
        applyContinuousLinearMap (ContinuousMap.const K f') (p.1 - p.2)) t‖ ≤
        c * ‖p.1 t - p.2 t‖ := by
      simpa only [ContinuousMap.comp_apply, ContinuousMap.const_apply,
        applyContinuousLinearMap_apply, ContinuousMap.sub_apply] using hbound _ hpt
    _ ≤ c * ‖p.1 - p.2‖ :=
      mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm (p.1 - p.2) t) hc.le

end ContinuousMap
