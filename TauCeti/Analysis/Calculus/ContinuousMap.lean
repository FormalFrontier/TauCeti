/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Calculus on spaces of continuous maps

This file develops the bounded pointwise operations needed to differentiate superposition maps on
spaces of continuous functions over a compact domain.

## Main results

* `ContinuousMap.applyContinuousLinearMap`: pointwise application of a continuous family of
  continuous linear maps, as a bounded bilinear operator.
* `ContinuousMap.hasStrictFDerivAt_postcomp_const`: strict differentiability of pointwise
  postcomposition at a constant map.
* `ContinuousMap.hasFDerivAt_postcomp`: the derivative of pointwise postcomposition by a `C¹` map.
* `ContinuousMap.contDiff_postcomp`: finite-order or smooth pointwise postcomposition.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The exponential map".
-/

public section

open scoped ContinuousMap ContDiff

noncomputable section

universe u v

namespace ContinuousMap

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Pointwise application of a continuous family of continuous linear maps to a continuous map,
as a bounded bilinear operator. -/
noncomputable def applyContinuousLinearMap :
    C(K, E →L[𝕜] F) →L[𝕜] C(K, E) →L[𝕜] C(K, F) := by
  let L : C(K, E →L[𝕜] F) →ₗ[𝕜] C(K, E) →ₗ[𝕜] C(K, F) :=
    { toFun := fun A =>
        { toFun := fun f => ⟨fun x => A x (f x), by fun_prop⟩
          map_add' := fun _ _ => by ext x; simp
          map_smul' := fun _ _ => by ext x; simp }
      map_add' := fun _ _ => by ext f x; simp
      map_smul' := fun _ _ => by ext f x; simp }
  exact LinearMap.mkContinuous₂ (𝕜 := 𝕜) (𝕜₂ := 𝕜) (𝕜₃ := 𝕜)
    (σ₁₃ := RingHom.id 𝕜) (σ₂₃ := RingHom.id 𝕜) L 1 fun
      (A : C(K, E →L[𝕜] F)) (f : C(K, E)) => by
      rw [one_mul]
      change ‖(⟨fun x => A x (f x), by fun_prop⟩ : C(K, F))‖ ≤ ‖A‖ * ‖f‖
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
theorem hasStrictFDerivAt_postcomp_const (f : C(E, F)) (f' : E →L[𝕜] F) (x : E)
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

namespace ContinuousMap

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The continuous family of derivatives of a `C¹` map along a continuous map. -/
noncomputable def fderivComp (f : E → F) (hf : ContDiff ℝ 1 f) (g : C(K, E)) :
    C(K, E →L[ℝ] F) :=
  ⟨fun t ↦ fderiv ℝ f (g t), (hf.continuous_fderiv one_ne_zero).comp g.continuous⟩

omit [CompactSpace K] in
@[simp]
theorem fderivComp_apply (f : E → F) (hf : ContDiff ℝ 1 f) (g : C(K, E)) (t : K) :
    fderivComp f hf g t = fderiv ℝ f (g t) :=
  by
    rw [fderivComp]
    rfl

/-- Pointwise postcomposition by a `C¹` map is Fréchet differentiable. Its derivative applies
the derivative of the original map pointwise along the input function. -/
theorem hasFDerivAt_postcomp (f : E → F) (hf : ContDiff ℝ 1 f) (g : C(K, E)) :
    HasFDerivAt (fun h : C(K, E) ↦ (⟨f, hf.continuous⟩ : C(E, F)).comp h)
      (applyContinuousLinearMap (fderivComp f hf g)) g := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hcompact : IsCompact (Set.range g) := isCompact_range g.continuous
  have hdf_cont : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have huniform := hcompact.uniformContinuousAt_of_continuousAt
    (fderiv ℝ f) (fun _ _ ↦ hdf_cont.continuousAt) (Metric.dist_mem_uniformity hc)
  obtain ⟨δ, hδ, hderiv⟩ := Metric.mem_uniformity_dist.mp huniform
  rw [Metric.eventually_nhds_iff_ball]
  refine ⟨δ, hδ, fun h hh ↦ ?_⟩
  apply (ContinuousMap.norm_le _ (mul_nonneg hc.le (norm_nonneg _))).2
  intro t
  have htg : g t ∈ Set.range g := ⟨t, rfl⟩
  have hpoint : dist (h t) (g t) < δ :=
    (ContinuousMap.dist_apply_le_dist t).trans_lt hh
  have hbound : ∀ z ∈ segment ℝ (g t) (h t),
      ‖fderiv ℝ f z - fderiv ℝ f (g t)‖ ≤ c := by
    intro z hz
    have hzg : dist (g t) z < δ := by
      rw [dist_comm]
      simpa only [dist_eq_norm] using
        (norm_sub_le_of_mem_segment hz).trans_lt (by simpa only [dist_eq_norm] using hpoint)
    have hd := hderiv hzg htg
    have hd' : dist (fderiv ℝ f (g t)) (fderiv ℝ f z) < c := hd
    simpa only [dist_eq_norm, norm_sub_rev] using hd'.le
  calc
    ‖((⟨f, hf.continuous⟩ : C(E, F)).comp h -
        (⟨f, hf.continuous⟩ : C(E, F)).comp g -
        applyContinuousLinearMap (fderivComp f hf g) (h - g)) t‖ ≤
        c * ‖h t - g t‖ := by
      rw [ContinuousMap.sub_apply, ContinuousMap.sub_apply,
        ContinuousMap.comp_apply, ContinuousMap.comp_apply,
        applyContinuousLinearMap_apply, fderivComp_apply]
      exact (convex_segment (g t) (h t)).norm_image_sub_le_of_norm_fderiv_le'
        (fun _ _ ↦ hf.differentiable one_ne_zero _) hbound
        (left_mem_segment ℝ (g t) (h t)) (right_mem_segment ℝ (g t) (h t))
    _ ≤ c * ‖h - g‖ :=
      mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm (h - g) t) hc.le

private theorem contDiff_postcomp_nat (n : ℕ) (f : C(E, F)) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun g : C(K, E) ↦ f.comp g) := by
  induction n generalizing F with
  | zero =>
      have hzero : ContDiff ℝ (0 : ℕ∞ω) (fun g : C(K, E) ↦ f.comp g) := by
        rw [contDiff_zero]
        exact f.continuous_postcomp
      simpa using hzero
  | succ n ih =>
      have hf' : ContDiff ℝ ((n : ℕ∞ω) + 1) f := by simpa using hf
      let hf₁ : ContDiff ℝ 1 f := hf'.one_of_succ
      let df : C(E, E →L[ℝ] F) := ⟨fderiv ℝ f, hf₁.continuous_fderiv one_ne_zero⟩
      have hdf : ContDiff ℝ n df := (contDiff_succ_iff_fderiv.mp hf').2.2
      have hcomp : ContDiff ℝ n (fun g : C(K, E) ↦ df.comp g) := ih df hdf
      have hsucc : ContDiff ℝ ((n : ℕ∞ω) + 1) (fun g : C(K, E) ↦ f.comp g) := by
        rw [contDiff_succ_iff_hasFDerivAt]
        refine ⟨fun g ↦ applyContinuousLinearMap (df.comp g),
          applyContinuousLinearMap.contDiff.fun_comp hcomp, fun g ↦ ?_⟩
        have hderiv := hasFDerivAt_postcomp (f : E → F) hf₁ g
        have hfamily : df.comp g = fderivComp f hf₁ g := by
          apply ContinuousMap.ext
          intro t
          have hdf_apply : df (g t) = fderiv ℝ f (g t) := by
            rfl
          rw [ContinuousMap.comp_apply, hdf_apply, fderivComp_apply]
        have hfc : (⟨(f : E → F), hf₁.continuous⟩ : C(E, F)) = f := by
          ext x
          rfl
        rw [hfc] at hderiv
        simpa only [hfamily] using hderiv
      simpa using hsucc

/-- Pointwise postcomposition by a `C^n` map is `C^n` on a compact-domain continuous-map space,
for every finite or infinite differentiability order `n`. -/
theorem contDiff_postcomp (n : ℕ∞) (f : E → F) (hf : ContDiff ℝ (n : ℕ∞ω) f) :
    ContDiff ℝ (n : ℕ∞ω)
      (fun g : C(K, E) ↦ (⟨f, hf.continuous⟩ : C(E, F)).comp g) := by
  induction n using ENat.recTopCoe with
  | top =>
      have hfInf : ContDiff ℝ ∞ f := by simpa using hf
      let fc : C(E, F) := ⟨f, hfInf.continuous⟩
      change ContDiff ℝ ∞ (fun g : C(K, E) => fc.comp g)
      exact contDiff_infty.2 fun m =>
        contDiff_postcomp_nat m fc ((contDiff_infty.mp hfInf) m)
  | coe n =>
      let fc : C(E, F) := ⟨f, hf.continuous⟩
      change ContDiff ℝ n (fun g : C(K, E) => fc.comp g)
      exact contDiff_postcomp_nat n fc hf

end ContinuousMap
