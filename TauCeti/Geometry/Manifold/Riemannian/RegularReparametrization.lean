/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Archon Horizon (claude+codex), Axel Delaval,
  Chunlei Liu, Jinxuan Chen, Wanxu Yang, Zekun Sheng, Yuxuan Liao, Jie Xu
-/
module

public import TauCeti.Analysis.Calculus.IntervalIntegralInverse
public import TauCeti.Geometry.Manifold.Riemannian.RiemannianSpeed

/-!
# Regular C¹ curves admit unit-speed reparametrizations

This file constructs arclength and constant-speed reparametrizations of regular
Riemannian curves. A curve that is `C¹` on a neighborhood of a nondegenerate
compact interval and has nonzero derivative throughout that interval has an
arclength inverse on its full length interval.
The inverse is strictly monotone, preserves both endpoints, gives unit speed, and
preserves Mathlib's canonical `Manifold.pathELength`.

The consumer-facing corollary rescales the arclength interval to `[0, 1]`,
where the resulting curve has constant speed equal to its total length.

## Main declarations

* `TauCeti.exists_contDiffOn_intervalIntegral_inverse_of_pos`: the inverse of
  the primitive of a continuous positive real function, with its interval and
  `C¹` properties.
* `TauCeti.Manifold.exists_unit_speed_reparametrization_of_regular`: the
  arclength-interval reparametrization.
* `TauCeti.Manifold.exists_constant_speed_reparametrization_of_regular`: the
  rescaled constant-speed reparametrization on `[0, 1]`.

## References

* Peter Petersen, *Riemannian Geometry* (3rd ed., 2016), Chapter 5, §5.3,
  Proposition `prop:pet-ch5-arclength-reparametrization`, formalized by
  `regularCurve_arclengthReparametrization` (with the supporting
  `contDiffAt_curveSpeedSq`) in
  `formalized-sources/Petersen/PetersenLib/Ch05/ArclengthReparametrization.lean`
  in `frenzymath/Poincare-Conjecture`, revision
  `e6bc8cb66a83e50afa2b4507db664c9370bd4ac4`.
* The do Carmo formalization in `frenzymath/Poincare-Conjecture`,
  `DoCarmoLib/Riemannian/Manifold/DoCarmoCh3SegmentReparam.lean`, declarations
  `reparam`, `reparam_mem_Ioo`, and `hasDerivAt_reparam`, revision
  `24f32e4d600878bfaac6bc2f2f9324175571c321`.
* Both cited formal source files are from the Apache-2.0-licensed
  `frenzymath/Poincare-Conjecture` repository; this module is an adaptation
  under that license.
-/

public section

open Bundle Filter Manifold Set
open scoped Bundle ContDiff Manifold Topology

namespace TauCeti

noncomputable section

namespace Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- A curve that is `C¹` on `[a, b]` and has nonzero derivative
throughout the interval admits a `C¹` unit-speed reparametrization on its
arclength interval `[0, L]`.

The length `L`, both endpoint identities, strict monotonicity of the inverse, the two
inverse identities, and the canonical `pathELength` characterizations are all
part of the public conclusion. -/
theorem exists_unit_speed_reparametrization_of_regular {gamma : ℝ → M}
    {a b : ℝ} (hab : a < b)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc a b))
    (hreg : ∀ t ∈ Icc a b, riemannianSpeed I gamma t ≠ 0) :
    ∃ L : ℝ, ∃ psi : ℝ → ℝ,
      L = ∫ t in a..b, riemannianSpeed I gamma t ∧
      0 < L ∧
      MapsTo psi (Icc 0 L) (Icc a b) ∧
      StrictMonoOn psi (Icc 0 L) ∧
      psi 0 = a ∧
      psi L = b ∧
      (∀ t ∈ Icc a b,
        psi (∫ s in a..t, riemannianSpeed I gamma s) = t) ∧
      (∀ s ∈ Icc 0 L,
        ∫ t in a..psi s, riemannianSpeed I gamma t = s) ∧
      ContDiffOn ℝ 1 psi (Icc 0 L) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 (gamma ∘ psi) (Icc 0 L) ∧
      (∀ s ∈ Icc 0 L, riemannianSpeed I (gamma ∘ psi) s = 1) ∧
      (gamma ∘ psi) 0 = gamma a ∧
      (gamma ∘ psi) L = gamma b ∧
      pathELength I gamma a b = ENNReal.ofReal L ∧
      (∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, s ≤ t →
        pathELength I (gamma ∘ psi) s t = ENNReal.ofReal (t - s)) ∧
      pathELength I (gamma ∘ psi) 0 L = pathELength I gamma a b := by
  have hmdiff : ∀ t ∈ Icc a b, MDiffAt gamma t := by
    intro t ht
    by_contra hnot
    exact hreg t ht (riemannianSpeed_eq_zero_of_not_mdifferentiableAt I gamma t hnot)
  have hspeed_cont : ContinuousOn (riemannianSpeed I gamma) (Icc a b) :=
    continuousOn_riemannianSpeed I hgamma hmdiff
      (uniqueDiffOn_Icc hab).uniqueMDiffOn
  have hspeed_pos : ∀ t ∈ Icc a b, 0 < riemannianSpeed I gamma t := by
    intro t ht
    have hnonneg : 0 ≤ riemannianSpeed I gamma t := by
      simpa only [riemannianSpeed_apply] using riemannianSpeed_nonneg I gamma t
    exact lt_of_le_of_ne hnonneg (hreg t ht).symm
  -- The generic positive-integral inverse lemma supplies all real-analysis
  -- facts about the arclength primitive and its inverse in one step.
  obtain ⟨L, psi, hL_def, hL_pos, hmaps, hpsi_strict,
    hpsi_zero, hpsi_L, hleft_Icc, hright_Icc, hpsi_C1_Icc, hpsi_hasDeriv⟩ :=
    exists_contDiffOn_intervalIntegral_inverse_of_pos hab hspeed_cont hspeed_pos
  -- Transfer the inverse's calculus facts through the curve, then identify
  -- the resulting interval integrals with Mathlib's canonical path length.
  have hcomp_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (gamma ∘ psi) (Icc 0 L) :=
    hgamma.comp hpsi_C1_Icc.contMDiffOn hmaps
  have hunitSpeed : ∀ s ∈ Icc 0 L,
      riemannianSpeed I (gamma ∘ psi) s = 1 := by
    intro s hs
    have hpsi_deriv := hpsi_hasDeriv s hs
    rw [riemannianSpeed_comp I gamma psi s (hmdiff _ (hmaps hs))
      hpsi_deriv.differentiableAt, hpsi_deriv.deriv]
    have hpos : 0 < riemannianSpeed I gamma (psi s) := by
      have hnonneg : 0 ≤ riemannianSpeed I gamma (psi s) := by
        simpa only [riemannianSpeed_apply] using riemannianSpeed_nonneg I gamma (psi s)
      exact lt_of_le_of_ne hnonneg (hreg _ (hmaps hs)).symm
    rw [abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
  have horiginalLength : pathELength I gamma a b = ENNReal.ofReal L := by
    rw [pathELength_eq_ofReal_integral_riemannianSpeed I hab.le
      hspeed_cont.integrableOn_Icc, ← hL_def]
  have hpsi_mono : MonotoneOn psi (Icc 0 L) := hpsi_strict.monotoneOn
  have hunitLength : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, s ≤ t →
      pathELength I (gamma ∘ psi) s t = ENNReal.ofReal (t - s) := by
    intro s hs t ht hst
    have hpsi_st : psi s ≤ psi t := hpsi_mono hs ht hst
    have htarget : Icc (psi s) (psi t) ⊆ Icc a b :=
      Icc_subset_Icc (hmaps hs).1 (hmaps ht).2
    have hcomp := pathELength_comp_of_monotoneOn (I := I) hst
      (hpsi_mono.mono (Icc_subset_Icc hs.1 ht.2))
      ((hpsi_C1_Icc.differentiableOn (by norm_num)).mono
        (Icc_subset_Icc hs.1 ht.2))
      ((hgamma.mdifferentiableOn (by norm_num)).mono htarget)
    have hint : MeasureTheory.IntegrableOn (riemannianSpeed I gamma)
        (Icc (psi s) (psi t)) :=
      (hspeed_cont.mono htarget).integrableOn_Icc
    rw [hcomp, pathELength_eq_ofReal_integral_riemannianSpeed I hpsi_st hint]
    congr 1
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume)
      ((hspeed_cont.mono (Icc_subset_Icc le_rfl (hmaps hs).2)).intervalIntegrable_of_Icc
        (hmaps hs).1)
      ((hspeed_cont.mono htarget).intervalIntegrable_of_Icc hpsi_st)
    rw [hright_Icc s hs, hright_Icc t ht] at hadd
    linarith
  have htotalLength :
      pathELength I (gamma ∘ psi) 0 L = pathELength I gamma a b := by
    have hlen := hunitLength 0 (left_mem_Icc.mpr hL_pos.le) L
      (right_mem_Icc.mpr hL_pos.le) hL_pos.le
    calc
      pathELength I (gamma ∘ psi) 0 L = ENNReal.ofReal L := by simpa using hlen
      _ = pathELength I gamma a b := horiginalLength.symm
  refine ⟨L, psi, hL_def, hL_pos, hmaps, hpsi_strict, hpsi_zero, hpsi_L,
    hleft_Icc, hright_Icc, hpsi_C1_Icc, hcomp_C1, hunitSpeed, ?_, ?_,
    horiginalLength, hunitLength, htotalLength⟩
  · simp only [Function.comp_apply, hpsi_zero]
  · simp only [Function.comp_apply, hpsi_L]

/-- A curve that is `C¹` on `[a, b]` and has nonzero derivative
throughout the interval admits a constant-speed reparametrization on `[0, 1]`;
its speed is its total length `L`, and every subinterval `[s, t]` has length
`L (t - s)`. -/
theorem exists_constant_speed_reparametrization_of_regular {gamma : ℝ → M}
    {a b : ℝ} (hab : a < b)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc a b))
    (hreg : ∀ t ∈ Icc a b, riemannianSpeed I gamma t ≠ 0) :
    ∃ L : ℝ, ∃ theta : ℝ → ℝ,
      L = ∫ t in a..b, riemannianSpeed I gamma t ∧
      0 < L ∧
      MapsTo theta (Icc 0 1) (Icc a b) ∧
      StrictMonoOn theta (Icc 0 1) ∧
      theta 0 = a ∧
      theta 1 = b ∧
      ContDiffOn ℝ 1 theta (Icc 0 1) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 (gamma ∘ theta) (Icc 0 1) ∧
      (∀ t ∈ Icc 0 1, riemannianSpeed I (gamma ∘ theta) t = L) ∧
      (∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1, s ≤ t →
        pathELength I (gamma ∘ theta) s t = ENNReal.ofReal (L * (t - s))) ∧
      pathELength I (gamma ∘ theta) 0 1 = ENNReal.ofReal L ∧
      pathELength I (gamma ∘ theta) 0 1 = pathELength I gamma a b := by
  obtain ⟨L, psi, hL, hL_pos, hpsi_maps, hpsi_strict, hpsi_zero, hpsi_L,
    _, _, hpsi_C1, hunit_C1, hunit, _, _, horiginalLength, hunitLength, _⟩ :=
    exists_unit_speed_reparametrization_of_regular hab hgamma hreg
  let scale : ℝ → ℝ := fun t ↦ L * t
  let theta : ℝ → ℝ := psi ∘ scale
  have hscale_maps : MapsTo scale (Icc 0 1) (Icc 0 L) := by
    intro t ht
    exact ⟨mul_nonneg hL_pos.le ht.1,
      (mul_le_mul_of_nonneg_left ht.2 hL_pos.le).trans_eq (mul_one L)⟩
  have htheta_maps : MapsTo theta (Icc 0 1) (Icc a b) :=
    hpsi_maps.comp hscale_maps
  have hscale_strict : StrictMonoOn scale (Icc 0 1) := by
    intro s _ t _ hst
    exact mul_lt_mul_of_pos_left hst hL_pos
  have hscale_mono : MonotoneOn scale (Icc 0 1) := hscale_strict.monotoneOn
  have htheta_strict : StrictMonoOn theta (Icc 0 1) := by
    intro s hs t ht hst
    exact hpsi_strict (hscale_maps hs) (hscale_maps ht)
      (hscale_strict hs ht hst)
  have hscale_C1 : ContDiff ℝ 1 scale := by
    fun_prop
  have htheta_C1 : ContDiffOn ℝ 1 theta (Icc 0 1) := by
    simpa only [theta] using hpsi_C1.comp hscale_C1.contDiffOn hscale_maps
  have hcomp_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1
      (gamma ∘ theta) (Icc 0 1) := by
    have hcomp := hunit_C1.comp hscale_C1.contDiffOn.contMDiffOn hscale_maps
    simpa only [theta, Function.comp_assoc] using hcomp
  have hscale_hasDeriv : ∀ t, HasDerivAt scale L t := by
    intro t
    simpa only [scale, id_eq, mul_one] using (hasDerivAt_id t).const_mul L
  have hunit_mdiff : ∀ t ∈ Icc 0 L, MDiffAt (gamma ∘ psi) t := by
    intro t ht
    by_contra hnot
    have hzero := riemannianSpeed_eq_zero_of_not_mdifferentiableAt
      I (gamma ∘ psi) t hnot
    rw [hunit t ht] at hzero
    norm_num at hzero
  have hconstant : ∀ t ∈ Icc 0 1,
      riemannianSpeed I (gamma ∘ theta) t = L := by
    intro t ht
    have hchain := riemannianSpeed_comp I (gamma ∘ psi) scale t
      (hunit_mdiff _ (hscale_maps ht)) (hscale_hasDeriv t).differentiableAt
    rw [(hscale_hasDeriv t).deriv, abs_of_pos hL_pos, hunit _ (hscale_maps ht)] at hchain
    simpa only [theta, Function.comp_assoc, mul_one] using hchain
  have hsubintervalLength : ∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1, s ≤ t →
      pathELength I (gamma ∘ theta) s t = ENNReal.ofReal (L * (t - s)) := by
    intro s hs t ht hst
    have hscale_st : scale s ≤ scale t := hscale_mono hs ht hst
    have hinterval : Icc (scale s) (scale t) ⊆ Icc 0 L :=
      Icc_subset_Icc (hscale_maps hs).1 (hscale_maps ht).2
    have hcomp := pathELength_comp_of_monotoneOn (I := I) hst
      (hscale_mono.mono (Icc_subset_Icc hs.1 ht.2))
      ((hscale_C1.contDiffOn.differentiableOn (by norm_num)).mono
        (Icc_subset_Icc hs.1 ht.2))
      ((hunit_C1.mdifferentiableOn (by norm_num)).mono hinterval)
    calc
      pathELength I (gamma ∘ theta) s t =
          pathELength I ((gamma ∘ psi) ∘ scale) s t := by
        simp only [theta, Function.comp_assoc]
      _ = pathELength I (gamma ∘ psi) (scale s) (scale t) := hcomp
      _ = ENNReal.ofReal (scale t - scale s) :=
        hunitLength _ (hscale_maps hs) _ (hscale_maps ht) hscale_st
      _ = ENNReal.ofReal (L * (t - s)) := by
        congr 1
        simp only [scale]
        ring
  have hconstantLength :
      pathELength I (gamma ∘ theta) 0 1 = ENNReal.ofReal L := by
    simpa using hsubintervalLength 0 (by norm_num) 1 (by norm_num) zero_le_one
  have htheta_zero : theta 0 = a := by simp only [theta, scale, Function.comp_apply, mul_zero,
    hpsi_zero]
  have htheta_one : theta 1 = b := by simp only [theta, scale, Function.comp_apply, mul_one,
    hpsi_L]
  refine ⟨L, theta, hL, hL_pos, htheta_maps, htheta_strict, htheta_zero,
    htheta_one, htheta_C1, hcomp_C1, hconstant, hsubintervalLength, hconstantLength, ?_⟩
  exact hconstantLength.trans horiginalLength.symm

end Manifold

end

end TauCeti
