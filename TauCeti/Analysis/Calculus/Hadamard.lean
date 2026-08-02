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
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The averaged derivative along the segment from `x` to `y`. -/
noncomputable def hadamardFactor [CompleteSpace F] (f : E → F) (x y : E) : E →L[ℝ] F :=
  ∫ t in (0 : ℝ)..1, fderiv ℝ f (x + t • (y - x))

/-- The averaged derivative written as an integral over the compact unit interval. -/
theorem hadamardFactor_eq_integral_Icc [CompleteSpace F] (f : E → F) (x : E) :
    hadamardFactor f x = fun y ↦ ∫ t in Set.Icc (0 : ℝ) 1,
      fderiv ℝ f (x + t • (y - x)) := by
  funext y
  rw [hadamardFactor, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc]

/-- At the basepoint, the averaged derivative is the ordinary derivative. -/
@[simp]
theorem hadamardFactor_self [CompleteSpace F] (f : E → F) (x : E) :
    hadamardFactor f x x = fderiv ℝ f x := by
  simp [hadamardFactor]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
private theorem exists_eventually_norm_le_on_Icc
    (h : E → ℝ → F) (hh : Continuous h.uncurry) (x₀ : E) :
    ∃ C : ℝ, ∀ᶠ x in nhds x₀, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖h x t‖ ≤ C := by
  have hfiber : Continuous (fun t : ℝ ↦ ‖h x₀ t‖) :=
    hh.norm.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).bddAbove_image
    hfiber.continuousOn
  let n : Set (E × ℝ) := {z | ‖h.uncurry z‖ < C + 1}
  have hn : IsOpen n := isOpen_lt hh.norm continuous_const
  have hfiber_subset : {x₀} ×ˢ Set.Icc (0 : ℝ) 1 ⊆ n := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have hxx₀ : x = x₀ := by simpa only [Set.mem_singleton_iff] using hx
    subst x
    exact lt_of_le_of_lt (hC (Set.mem_image_of_mem (fun t : ℝ ↦ ‖h x₀ t‖) ht))
      (lt_add_of_pos_right C zero_lt_one)
  obtain ⟨u, v, hu, -, hxu, hIv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hn hfiber_subset
  have hx₀u : x₀ ∈ u := hxu (Set.mem_singleton x₀)
  refine ⟨C + 1, ?_⟩
  filter_upwards [hu.mem_nhds hx₀u] with x hx
  intro t ht
  have hxt := huv (show (x, t) ∈ u ×ˢ v from ⟨hx, hIv ht⟩)
  change ‖h x t‖ < C + 1 at hxt
  exact hxt.le

omit [NormedSpace ℝ E] in
/-- Integration over the compact unit interval preserves continuity in a normed parameter. -/
theorem continuous_integral_Icc_of_continuous [CompleteSpace F]
    (h : E → ℝ → F) (hh : Continuous h.uncurry) :
    Continuous (fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, h x t) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨C, hC⟩ := exists_eventually_norm_le_on_Icc h hh x₀
  apply continuousAt_of_dominated
  · filter_upwards with x using Continuous.aestronglyMeasurable (by fun_prop)
  · filter_upwards [hC] with x hx
    rw [ae_restrict_iff]
    · filter_upwards with t ht
      exact hx t ht
    · exact (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  · exact (show Continuous (fun _ : ℝ ↦ C) from continuous_const).integrableOn_Icc
  · filter_upwards using (by fun_prop)

/-- Differentiation under an integral over the compact unit interval for a continuously
differentiable parameterized function. -/
theorem hasFDerivAt_integral_Icc_of_contDiff
    [CompleteSpace F] (h : E → ℝ → F) (hh : ContDiff ℝ 1 h.uncurry) (x₀ : E) :
    HasFDerivAt (fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, h x t)
      (∫ t in Set.Icc (0 : ℝ) 1,
        (fderiv ℝ h.uncurry (x₀, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x₀ := by
  let h' : E → ℝ → E →L[ℝ] F := fun x t ↦
    (fderiv ℝ h.uncurry (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hh' : Continuous h'.uncurry := by
    have hd : Continuous (fderiv ℝ h.uncurry) :=
      (hh.fderiv_right (m := 0) (by norm_num)).continuous
    fun_prop
  obtain ⟨C, hC⟩ := exists_eventually_norm_le_on_Icc h' hh' x₀
  let s : Set E := {x | ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖h' x t‖ ≤ C}
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) (F := h) (F' := h')
    (bound := fun _ ↦ C) (s := s)
  · exact hC
  · exact Filter.Eventually.of_forall fun x ↦
      (hh.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hh.continuous.comp (continuous_const.prodMk continuous_id)).integrableOn_Icc
  · exact (hh'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    intro x hx
    exact hx t ht
  · exact continuous_const.integrableOn_Icc
  · filter_upwards with t
    intro x _hx
    have hd := hh.differentiable_one.differentiableAt.hasFDerivAt.comp x
        (hasFDerivAt_id x |>.prodMk (hasFDerivAt_const t x))
    -- Expose the derivative of the fixed-`t` slice; `inl` is definitionally `id.prod 0`.
    change HasFDerivAt (fun y ↦ h y t)
      ((fderiv ℝ h.uncurry (x, t)).comp ((ContinuousLinearMap.id ℝ E).prod 0)) x at hd
    simpa only [h', ContinuousLinearMap.inl] using hd

/-- Integration over the compact unit interval preserves any finite order of continuous
differentiability in a parameter. -/
theorem contDiff_integral_Icc_of_contDiff
    {V : Type u} {W : Type max u v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (n : ℕ) (h : V → ℝ → W) (hh : ContDiff ℝ n h.uncurry) :
    ContDiff ℝ n (fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, h x t) := by
  induction n generalizing W with
  | zero =>
      have hc : ContDiff ℝ (0 : ℕ∞ω) (fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, h x t) :=
        contDiff_zero.2 (continuous_integral_Icc_of_continuous h hh.continuous)
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

/-- If `f` is `n + 1` times continuously differentiable, its Hadamard factor is `n` times
continuously differentiable in the endpoint. -/
theorem ContDiff.contDiff_hadamardFactor_of_succ
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (n : ℕ) (f : E → F) (hf : ContDiff ℝ (n + 1) f) (x : E) :
    ContDiff ℝ n (hadamardFactor f x) := by
  rw [hadamardFactor_eq_integral_Icc]
  apply contDiff_integral_Icc_of_contDiff n
  have hd : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (m := n) (by norm_num)
  exact hd.comp <| by fun_prop

/-- First-order Taylor expansion along a segment, with its coefficient bundled as a continuous
linear map. -/
theorem ContDiff.sub_eq_hadamardFactor_apply [CompleteSpace F]
    (f : E → F) (hf : ContDiff ℝ 1 f) (x y : E) :
    f y - f x = hadamardFactor f x y (y - x) := by
  have hTaylor := map_add_eq_sum_add_integral_iteratedFDeriv (n := 0) (x := x) (y := y - x)
    (fun _ _ ↦ hf.contDiffAt)
  have hIntegrable : IntervalIntegrable (fun t : ℝ ↦ fderiv ℝ f (x + t • (y - x)))
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact (hf.fderiv_right (m := 0) (by norm_num)).continuous.comp (by fun_prop)
  rw [hadamardFactor, ContinuousLinearMap.intervalIntegral_apply hIntegrable (y - x)]
  simpa [sub_eq_iff_eq_add, add_comm] using hTaylor

/-- The averaged derivative in Hadamard's factorization depends continuously on the endpoint. -/
theorem ContDiff.continuous_hadamardFactor [CompleteSpace F] (f : E → F)
    (hf : ContDiff ℝ 1 f) (x : E) : Continuous (hadamardFactor f x) := by
  exact (ContDiff.contDiff_hadamardFactor_of_succ 0 f hf x).continuous

/-- For a smooth function, the averaged derivative in Hadamard's factorization depends smoothly on
the endpoint. -/
theorem ContDiff.contDiff_hadamardFactor [CompleteSpace F] (f : E → F)
    (hf : ContDiff ℝ ∞ f)
    (x : E) : ContDiff ℝ ∞ (hadamardFactor f x) := by
  rw [contDiff_infty]
  intro n
  exact ContDiff.contDiff_hadamardFactor_of_succ n f
    (hf.of_le (WithTop.coe_le_coe.2 le_top)) x
