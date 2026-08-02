/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Compact-parameter integration

This file proves that integration over the compact unit interval preserves joint continuity and
continuous differentiability in a parameter. Continuity holds for an arbitrary topological
parameter space, while differentiability is preserved at every finite or infinite order and with
independent domain and codomain universes.

These results supply the analytic regularity used by smooth Hadamard factorization, a prerequisite
for the point-derivation/tangent-space equivalence in the Lie groups roadmap.

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

omit [NormedSpace ℝ F] in
private theorem exists_eventually_norm_le_on_Icc
    {X : Type*} [TopologicalSpace X]
    (h : X → ℝ → F) (hh : Continuous h.uncurry) (x₀ : X) :
    ∃ C : ℝ, ∀ᶠ x in nhds x₀, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖h x t‖ ≤ C := by
  have hfiber : Continuous (fun t : ℝ ↦ ‖h x₀ t‖) :=
    hh.norm.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).bddAbove_image
    hfiber.continuousOn
  let n : Set (X × ℝ) := {z | ‖h.uncurry z‖ < C + 1}
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
  have hmem : (x, t) ∈ u ×ˢ v := ⟨hx, hIv ht⟩
  have hxt := huv hmem
  have hbound : ‖h x t‖ < C + 1 := by simpa [n] using hxt
  exact hbound.le

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

private theorem contDiff_integral_Icc_of_contDiff_nat
    {V : Type u} {W : Type max u v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (n : ℕ) (h : V → ℝ → W) (hh : ContDiff ℝ n h.uncurry) :
    ContDiff ℝ n (fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, h x t) := by
  induction n generalizing W with
  | zero =>
      have hc : Continuous (fun x ↦ ∫ t in (0 : ℝ)..1, h x t) :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          hh.continuous 0 1
      apply contDiff_zero.2
      simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
        using hc
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

/-- Integration over the compact unit interval preserves continuous differentiability of any
possibly infinite order in a parameter. -/
theorem contDiff_integral_Icc_of_contDiff
    {V : Type u} {W : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (n : ℕ∞) (h : V → ℝ → W) (hh : ContDiff ℝ n h.uncurry) :
    ContDiff ℝ n (fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, h x t) := by
  let eW : Type max u v := ULift.{u} W
  let isoW : eW ≃L[ℝ] W := ContinuousLinearEquiv.ulift
  let eh : V → ℝ → eW := fun x t ↦ isoW.symm (h x t)
  have heh : ContDiff ℝ n eh.uncurry := by
    apply isoW.symm.contDiff.comp hh
  have he : ContDiff ℝ n (fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, eh x t) := by
    rw [contDiff_iff_forall_nat_le]
    intro m hm
    exact contDiff_integral_Icc_of_contDiff_nat m eh (heh.of_le (by exact_mod_cast hm))
  convert isoW.contDiff.comp he using 1
  funext x
  simpa only [Function.comp_apply, eh, ContinuousLinearEquiv.apply_symm_apply] using
    (isoW.integral_comp_comm (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) (fun t ↦ eh x t))
