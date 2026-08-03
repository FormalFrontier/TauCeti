/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Calculus on spaces of continuous maps

This file develops the bounded pointwise operations needed to differentiate superposition maps on
spaces of continuous functions over a compact domain.

## Main results

* `ContinuousMap.applyContinuousLinearMap`: pointwise application of a continuous family of
  continuous linear maps, as a bounded bilinear operator.
* `ContinuousMap.hasFDerivAt_postcomp`: the derivative of pointwise postcomposition by a `C¹` map.
* `ContinuousMap.contDiff_postcomp`: finite-order or smooth pointwise postcomposition.
* `ContinuousMap.unitIntervalIntegral`: the Volterra integral operator on continuous paths over
  the unit interval.

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
      apply (ContinuousMap.norm_le _
        (mul_nonneg (norm_nonneg A) (norm_nonneg f))).2
      intro x
      exact (ContinuousLinearMap.le_opNorm (A x) (f x)).trans <|
        mul_le_mul (norm_coe_le_norm A x) (norm_coe_le_norm f x)
          (norm_nonneg _) (norm_nonneg _)

@[simp]
theorem applyContinuousLinearMap_apply (A : C(K, E →L[𝕜] F)) (f : C(K, E)) (x : K) :
    applyContinuousLinearMap A f x = A x (f x) :=
  by simp [applyContinuousLinearMap]

end ContinuousMap

namespace ContinuousMap

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Volterra integration as a continuous linear operator on continuous paths over the unit
interval. The input is extended constantly outside the interval before integration. -/
noncomputable def unitIntervalIntegral :
    C(Set.Icc (0 : ℝ) 1, E) →L[ℝ] C(Set.Icc (0 : ℝ) 1, E) := by
  let primitive (f : C(Set.Icc (0 : ℝ) 1, E)) : C(Set.Icc (0 : ℝ) 1, E) :=
    ⟨fun t ↦ ∫ s in (0 : ℝ)..t, f (Set.projIcc 0 1 zero_le_one s),
      (intervalIntegral.continuous_primitive
        (fun a b ↦ (f.continuous.comp continuous_projIcc).intervalIntegrable a b) 0).comp
          continuous_subtype_val⟩
  have primitive_apply (f : C(Set.Icc (0 : ℝ) 1, E)) (t : Set.Icc (0 : ℝ) 1) :
      primitive f t =
        ∫ s in (0 : ℝ)..t, f (Set.projIcc 0 1 zero_le_one s) :=
    rfl
  let L : C(Set.Icc (0 : ℝ) 1, E) →ₗ[ℝ] C(Set.Icc (0 : ℝ) 1, E) :=
    { toFun := primitive
      map_add' := fun f g ↦ by
        ext t
        exact intervalIntegral.integral_add
          ((f.continuous.comp continuous_projIcc).intervalIntegrable _ _)
          ((g.continuous.comp continuous_projIcc).intervalIntegrable _ _)
      map_smul' := fun c f ↦ by
        ext t
        rw [primitive_apply, ContinuousMap.smul_apply, primitive_apply]
        simpa only [ContinuousMap.smul_apply, RingHom.id_apply] using
          intervalIntegral.integral_smul c
            (fun s ↦ f (Set.projIcc 0 1 zero_le_one s)) }
  exact LinearMap.mkContinuous L 1 fun f ↦ by
    rw [one_mul]
    apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
    intro t
    calc
      ‖primitive f t‖ ≤ ‖f‖ * |(t : ℝ) - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun s _ ↦
          ContinuousMap.norm_coe_le_norm f (Set.projIcc 0 1 zero_le_one s)
      _ ≤ ‖f‖ := by
        rw [sub_zero, abs_of_nonneg t.2.1]
        exact mul_le_of_le_one_right (norm_nonneg f) t.2.2

omit [CompleteSpace E] in
/-- The Volterra integral operator on the unit interval has operator norm at most one. -/
theorem norm_unitIntervalIntegral_le :
    ‖unitIntervalIntegral (E := E)‖ ≤ 1 := by
  rw [unitIntervalIntegral]
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

omit [CompleteSpace E] in
/-- Evaluating the Volterra operator at `t` integrates the input's constant extension from zero
to `t`. -/
@[simp]
theorem unitIntervalIntegral_apply (f : C(Set.Icc (0 : ℝ) 1, E))
    (t : Set.Icc (0 : ℝ) 1) :
    unitIntervalIntegral f t =
      ∫ s in (0 : ℝ)..t, f (Set.projIcc 0 1 zero_le_one s) := by
  rw [unitIntervalIntegral]
  rfl

end ContinuousMap

namespace ContinuousMap

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  -- The induction replaces `F` by `E →L[𝕜] F`; cumulativity still lets callers instantiate this
  -- with a codomain from any universe, while `max u v` keeps every derivative family in one level.
  {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Pointwise postcomposition by a `C¹` map is Fréchet differentiable. Its derivative applies
the derivative of the original map pointwise along the input function. -/
theorem hasFDerivAt_postcomp (f : C(E, F)) (hf : ContDiff 𝕜 1 f) (g : C(K, E)) :
    HasFDerivAt (fun h : C(K, E) ↦ f.comp h)
      (applyContinuousLinearMap
        ((⟨fderiv 𝕜 f, hf.continuous_fderiv one_ne_zero⟩ : C(E, E →L[𝕜] F)).comp g)) g := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hcompact : IsCompact (Set.range g) := isCompact_range g.continuous
  have hdf_cont : Continuous (fderiv 𝕜 f) := hf.continuous_fderiv one_ne_zero
  have huniform := hcompact.uniformContinuousAt_of_continuousAt
    (fderiv 𝕜 f) (fun _ _ ↦ hdf_cont.continuousAt) (Metric.dist_mem_uniformity hc)
  obtain ⟨δ, hδ, hderiv⟩ := Metric.mem_uniformity_dist.mp huniform
  rw [Metric.eventually_nhds_iff_ball]
  refine ⟨δ, hδ, fun h hh ↦ ?_⟩
  apply (ContinuousMap.norm_le _ (mul_nonneg hc.le (norm_nonneg _))).2
  intro t
  have htg : g t ∈ Set.range g := ⟨t, rfl⟩
  have hpoint : dist (h t) (g t) < δ :=
    (ContinuousMap.dist_apply_le_dist t).trans_lt hh
  have hbound : ∀ z ∈ segment ℝ (g t) (h t),
      ‖fderiv 𝕜 f z - fderiv 𝕜 f (g t)‖ ≤ c := by
    intro z hz
    have hzg : dist (g t) z < δ := by
      rw [dist_comm]
      simpa only [dist_eq_norm] using
        (norm_sub_le_of_mem_segment hz).trans_lt (by simpa only [dist_eq_norm] using hpoint)
    have hd := hderiv hzg htg
    have hd' : dist (fderiv 𝕜 f (g t)) (fderiv 𝕜 f z) < c := hd
    simpa only [dist_eq_norm, norm_sub_rev] using hd'.le
  calc
    ‖(f.comp h - f.comp g -
        applyContinuousLinearMap
          ((⟨fderiv 𝕜 f, hf.continuous_fderiv one_ne_zero⟩ : C(E, E →L[𝕜] F)).comp g)
          (h - g)) t‖ ≤
        c * ‖h t - g t‖ := by
      rw [ContinuousMap.sub_apply, ContinuousMap.sub_apply,
        ContinuousMap.comp_apply, ContinuousMap.comp_apply,
        applyContinuousLinearMap_apply]
      exact (convex_segment (𝕜 := ℝ) (g t) (h t)).norm_image_sub_le_of_norm_fderiv_le'
        (fun _ _ ↦ hf.differentiable one_ne_zero _) hbound
        (left_mem_segment ℝ (g t) (h t)) (right_mem_segment ℝ (g t) (h t))
    _ ≤ c * ‖h - g‖ :=
      mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm (h - g) t) hc.le

private theorem contDiff_postcomp_nat (n : ℕ) (f : C(E, F)) (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n (fun g : C(K, E) ↦ f.comp g) := by
  induction n generalizing F with
  | zero =>
      have hzero : ContDiff 𝕜 (0 : ℕ∞ω) (fun g : C(K, E) ↦ f.comp g) := by
        rw [contDiff_zero]
        exact f.continuous_postcomp
      simpa using hzero
  | succ n ih =>
      have hf' : ContDiff 𝕜 ((n : ℕ∞ω) + 1) f := by simpa using hf
      let hf₁ : ContDiff 𝕜 1 f := hf'.one_of_succ
      let df : C(E, E →L[𝕜] F) := ⟨fderiv 𝕜 f, hf₁.continuous_fderiv one_ne_zero⟩
      have hdf : ContDiff 𝕜 n df := (contDiff_succ_iff_fderiv.mp hf').2.2
      have hcomp : ContDiff 𝕜 n (fun g : C(K, E) ↦ df.comp g) := ih df hdf
      have hsucc : ContDiff 𝕜 ((n : ℕ∞ω) + 1) (fun g : C(K, E) ↦ f.comp g) := by
        rw [contDiff_succ_iff_hasFDerivAt]
        refine ⟨fun g ↦ applyContinuousLinearMap (df.comp g),
          applyContinuousLinearMap.contDiff.fun_comp hcomp, fun g ↦ ?_⟩
        exact hasFDerivAt_postcomp f hf₁ g
      simpa using hsucc

/-- Pointwise postcomposition by a `C^n` map is `C^n` on a compact-domain continuous-map space,
for every finite or infinite differentiability order `n`. -/
theorem contDiff_postcomp (n : ℕ∞) (f : C(E, F)) (hf : ContDiff 𝕜 (n : ℕ∞ω) f) :
    ContDiff 𝕜 (n : ℕ∞ω) (fun g : C(K, E) ↦ f.comp g) := by
  induction n using ENat.recTopCoe with
  | top =>
      have hfInf : ContDiff 𝕜 ∞ f := by simpa using hf
      exact contDiff_infty.2 fun m =>
        contDiff_postcomp_nat m f ((contDiff_infty.mp hfInf) m)
  | coe n =>
      exact contDiff_postcomp_nat n f hf

end ContinuousMap
