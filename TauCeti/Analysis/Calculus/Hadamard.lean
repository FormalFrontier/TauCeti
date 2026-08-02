/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Smooth Hadamard factorization

This file develops the first-order factorization of a smooth map through displacement from a
basepoint. It is the analytic input for identifying point derivations on a finite-dimensional
smooth manifold with tangent vectors.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The Lie algebra and the tangent space at `1`".
-/

public section

noncomputable section

open MeasureTheory
open scoped ContDiff

universe u v

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The averaged derivative along the segment from `x` to `y`. -/
noncomputable def hadamardFactor (f : E → F) (x y : E) : E →L[ℝ] F :=
  ∫ t in (0 : ℝ)..1, fderiv ℝ f (x + t • (y - x))

/-- At the basepoint, the averaged derivative is the ordinary derivative. -/
@[simp]
theorem hadamardFactor_self (f : E → F) (x : E) : hadamardFactor f x x = fderiv ℝ f x := by
  simp [hadamardFactor]

omit [CompleteSpace F] in
private theorem hasFDerivAt_integral_Icc_of_contDiff [FiniteDimensional ℝ E]
    (h : E → ℝ → F) (hh : ContDiff ℝ 1 h.uncurry) (x₀ : E) :
    HasFDerivAt (fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, h x t)
      (∫ t in Set.Icc (0 : ℝ) 1,
        (fderiv ℝ h.uncurry (x₀, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x₀ := by
  let h' : E → ℝ → E →L[ℝ] F := fun x t ↦
    (fderiv ℝ h.uncurry (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hh' : Continuous h'.uncurry := by
    have hd : Continuous (fderiv ℝ h.uncurry) :=
      (hh.fderiv_right (m := 0) (by norm_num)).continuous
    fun_prop
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall x₀ 1).prod isCompact_Icc).bddAbove_image hh'.norm.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
    (F := h) (F' := h') (bound := fun _ ↦ C) (s := Metric.closedBall x₀ 1)
  · exact Metric.closedBall_mem_nhds x₀ zero_lt_one
  · exact Filter.Eventually.of_forall fun x ↦
      (hh.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hh.continuous.comp (continuous_const.prodMk continuous_id)).integrableOn_Icc
  · exact (hh'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    intro x hx
    have hxt : (x, t) ∈ Metric.closedBall x₀ 1 ×ˢ Set.Icc (0 : ℝ) 1 := ⟨hx, ht⟩
    have hbound := hC (Set.mem_image_of_mem (fun z : E × ℝ ↦ ‖h'.uncurry z‖) hxt)
    change ‖h' x t‖ ≤ C at hbound
    exact hbound
  · exact continuous_const.integrableOn_Icc
  · filter_upwards with t
    intro x _hx
    have hd := hh.differentiable_one.differentiableAt.hasFDerivAt.comp x
        (hasFDerivAt_id x |>.prodMk (hasFDerivAt_const t x))
    change HasFDerivAt (fun y ↦ h y t)
      ((fderiv ℝ h.uncurry (x, t)).comp ((ContinuousLinearMap.id ℝ E).prod 0)) x at hd
    simpa only [h', ContinuousLinearMap.inl] using hd

private theorem contDiff_integral_Icc_of_contDiff
    {V W : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [FiniteDimensional ℝ V] (n : ℕ)
    (h : V → ℝ → W) (hh : ContDiff ℝ n h.uncurry) :
    ContDiff ℝ n (fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, h x t) := by
  induction n generalizing W with
  | zero =>
      have hc : ContDiff ℝ (0 : ℕ∞ω) (fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, h x t) :=
        contDiff_zero.2 (continuous_parametric_integral_of_continuous hh.continuous isCompact_Icc)
      simpa using hc
  | succ n ih =>
      let h' : V → ℝ → V →L[ℝ] W := fun x t ↦
        (fderiv ℝ h.uncurry (x, t)).comp (ContinuousLinearMap.inl ℝ V ℝ)
      have hh' : ContDiff ℝ n h'.uncurry := by
        have hd : ContDiff ℝ n (fderiv ℝ h.uncurry) :=
          hh.fderiv_right (m := n) (by norm_num)
        fun_prop
      have hsmooth : ContDiff ℝ ((n : ℕ∞ω) + 1)
          (fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, h x t) := by
        rw [contDiff_succ_iff_hasFDerivAt]
        exact ⟨fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, h' x t, ih h' hh',
          hasFDerivAt_integral_Icc_of_contDiff h (hh.of_le (by norm_num))⟩
      simpa only [Nat.cast_add, Nat.cast_one] using hsmooth

/-- First-order Taylor expansion along a segment, with its coefficient bundled as a continuous
linear map. -/
theorem ContDiff.sub_eq_hadamardFactor_apply (f : E → F) (hf : ContDiff ℝ 1 f) (x y : E) :
    f y - f x = hadamardFactor f x y (y - x) := by
  have hTaylor := map_add_eq_sum_add_integral_iteratedFDeriv (n := 0) (x := x) (y := y - x)
    (fun _ _ ↦ hf.contDiffAt)
  have hIntegrable : IntervalIntegrable (fun t : ℝ ↦ fderiv ℝ f (x + t • (y - x)))
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact (hf.fderiv_right (m := 0) (by norm_num)).continuous.comp (by fun_prop)
  rw [hadamardFactor, ContinuousLinearMap.intervalIntegral_apply hIntegrable (y - x)]
  simpa [sub_eq_iff_eq_add, add_comm] using hTaylor

omit [CompleteSpace F] in
/-- The averaged derivative in Hadamard's factorization depends continuously on the endpoint. -/
theorem ContDiff.continuous_hadamardFactor [FiniteDimensional ℝ E] (f : E → F)
    (hf : ContDiff ℝ 1 f) (x : E) : Continuous (hadamardFactor f x) := by
  rw [show hadamardFactor f x = fun y ↦ ∫ t in Set.Icc (0 : ℝ) 1,
      fderiv ℝ f (x + t • (y - x)) by
    funext y
    rw [hadamardFactor, intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc]]
  apply continuous_parametric_integral_of_continuous
  · exact (hf.fderiv_right (m := 0) (by norm_num)).continuous.comp (by fun_prop)
  · exact isCompact_Icc

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] in
/-- For a smooth real-valued function, the averaged derivative in Hadamard's factorization depends
smoothly on the endpoint. -/
theorem ContDiff.contDiff_hadamardFactor [FiniteDimensional ℝ E] (f : E → ℝ)
    (hf : ContDiff ℝ ∞ f)
    (x : E) : ContDiff ℝ ∞ (hadamardFactor f x) := by
  rw [show hadamardFactor f x = fun y ↦ ∫ t in Set.Icc (0 : ℝ) 1,
      fderiv ℝ f (x + t • (y - x)) by
    funext y
    rw [hadamardFactor, intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc]]
  rw [contDiff_infty]
  intro n
  apply contDiff_integral_Icc_of_contDiff n
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) (by simp)
  have hc : ContDiff ℝ ∞ (fun _ : E × ℝ ↦ x) := contDiff_const
  have hfst : ContDiff ℝ ∞ (Prod.fst : E × ℝ → E) := contDiff_fst
  have hsnd : ContDiff ℝ ∞ (Prod.snd : E × ℝ → ℝ) := contDiff_snd
  have hi : ContDiff ℝ ∞ (fun p : E × ℝ ↦ x + p.2 • (p.1 - x)) :=
    ContDiff.add hc (ContDiff.smul hsnd (ContDiff.sub hfst hc))
  exact (hd.comp hi).of_le (WithTop.coe_le_coe.2 le_top)
