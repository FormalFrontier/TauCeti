/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Archon Horizon (claude+codex), Axel Delaval,
  Chunlei Liu, Jinxuan Chen, Wanxu Yang, Zekun Sheng, Yuxuan Liao, Jie Xu
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.Topology.EMetricSpace.BoundedVariation

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Metric variation of a continuously differentiable curve

For a continuously differentiable curve in a complete real normed space, its
metric total variation equals the integral of the norm of its derivative.

The upper bound sums the fundamental theorem of calculus over finite
partitions. For the reverse bound, the curve is clamped to the compact
parameter interval. The resulting globally Lipschitz curve has bounded
variation, and its associated vector measure has density given by the
derivative on the interval.

## Main result

* `TauCeti.eVariationOn_eq_lintegral_enorm_derivWithin`: metric variation
  equals the integral of the derivative norm.

## Roadmap alignment

This module advances the `Regular reparametrization and limits` target under
`Layer 0: the reconciled Riemannian distance` in
`roadmap/HopfRinow/README.md`. It supplies the vector metric-variation
identity used as an analytic prerequisite by the lower-semicontinuity
comparison; this file does not claim the broader
Hopf--Rinow dependency path.

## Provenance

The partition-comparison architecture follows
`DoCarmoLib/Riemannian/Geodesic/HopfRinow/EVariationLePathELength.lean` in the
Apache-2.0 `frenzymath/Poincare-Conjecture` source at revision
`24f32e4d600878bfaac6bc2f2f9324175571c321`. That source proves the forward
comparison with Riemannian path length. The reverse derivative-integral
comparison here is a Tau Ceti proof using Mathlib's clamped-curve and
vector-measure APIs; it is not asserted to be present in that source.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 7, Section 2.
* The source-first Lean snapshot above, revision
  `24f32e4d600878bfaac6bc2f2f9324175571c321`, supplies the partition architecture
  via `eVariationOn_le_pathELength`; the reverse inequality is original to this
  module.
-/

public section

open Filter Set MeasureTheory
open scoped ENNReal NNReal Topology

namespace TauCeti

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For a `C¹` curve in a real normed space, metric total variation is bounded
by the integral of the norm of its derivative. -/
theorem eVariationOn_le_lintegral_enorm_derivWithin {f : ℝ → F} {a b : ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc a b)) :
    eVariationOn f (Icc a b) ≤ ∫⁻ t in Icc a b, ‖derivWithin f (Icc a b) t‖ₑ := by
  let L : ℝ → ℝ → ℝ≥0∞ := fun c d ↦
    ∫⁻ t in Icc c d, ‖derivWithin f (Icc a b) t‖ₑ
  have hL_add {c d e : ℝ} (hcd : c ≤ d) (hde : d ≤ e) : L c d + L d e = L c e := by
    have hset : Icc c e = Icc c d ∪ Ioc d e := (Icc_union_Ioc_eq_Icc hcd hde).symm
    simp only [L, hset]
    rw [lintegral_union measurableSet_Ioc]
    · simp only [restrict_Ioc_eq_restrict_Icc]
    · exact disjoint_iff_forall_ne.mpr (fun u hu v hv ↦ (hu.2.trans_lt hv.1).ne)
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  have hsegment : ∀ i, edist (f (u (i + 1))) (f (u i)) ≤ L (u i) (u (i + 1)) := by
    intro i
    have hlocal := enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc
      (hf.mono (Icc_subset_Icc (hus i).1 (hus (i + 1)).2)) (hu (Nat.le_succ i))
    calc
      edist (f (u (i + 1))) (f (u i)) = ‖f (u (i + 1)) - f (u i)‖ₑ := by
        rw [edist_eq_enorm_sub, enorm_sub_rev]
      _ ≤ ∫⁻ t in Icc (u i) (u (i + 1)),
          ‖derivWithin f (Icc (u i) (u (i + 1))) t‖ₑ := hlocal
      _ = L (u i) (u (i + 1)) := by
        simp only [L]
        rw [← restrict_Ioo_eq_restrict_Icc]
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro t ht
        have hderiv :
            derivWithin f (Icc (u i) (u (i + 1))) t = derivWithin f (Icc a b) t := by
          rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2),
            derivWithin_of_mem_nhds
              (Icc_mem_nhds ((hus i).1.trans_lt ht.1) (ht.2.trans_le (hus (i + 1)).2))]
        simp only [hderiv]
  have htelescoping : ∀ m, ∑ i ∈ Finset.range m, L (u i) (u (i + 1)) = L (u 0) (u m) := by
    intro m
    induction m with
    | zero => simp [L]
    | succ k ih => rw [Finset.sum_range_succ, ih, hL_add
        (hu (Nat.zero_le k)) (hu (Nat.le_succ k))]
  calc
    ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))
        ≤ ∑ i ∈ Finset.range n, L (u i) (u (i + 1)) :=
      Finset.sum_le_sum fun i _ ↦ hsegment i
    _ = L (u 0) (u n) := htelescoping n
    _ ≤ L a b := lintegral_mono_set (Icc_subset_Icc (hus 0).1 (hus n).2)
    _ = ∫⁻ t in Icc a b, ‖derivWithin f (Icc a b) t‖ₑ := rfl

variable [CompleteSpace F]

/-- For a `C¹` curve in a complete real normed space, the integral of the norm
of its derivative is bounded by its metric total variation. -/
theorem lintegral_enorm_derivWithin_le_eVariationOn {f : ℝ → F} {a b : ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc a b)) :
    ∫⁻ t in Icc a b, ‖derivWithin f (Icc a b) t‖ₑ ≤ eVariationOn f (Icc a b) := by
  by_cases hab : a ≤ b
  swap
  · rw [Icc_eq_empty hab]
    simp
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let p : ℝ → ℝ := fun t ↦ (Set.projIcc a b hab.le t).val
  let g : ℝ → F := f ∘ p
  let D : ℝ → F := (Icc a b).indicator (derivWithin f (Icc a b))
  have hp_mono : Monotone p := fun x y hxy ↦ by
    exact_mod_cast Set.monotone_projIcc hab.le hxy
  have hp_mem : MapsTo p univ (Icc a b) := fun t _ ↦ (Set.projIcc a b hab.le t).2
  have hD_cont : ContinuousOn (derivWithin f (Icc a b)) (Icc a b) :=
    hf.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)
  obtain ⟨C, hCpos, hC⟩ :=
    (isCompact_Icc.image_of_continuousOn hD_cont).isBounded.exists_pos_norm_le
  let K : ℝ≥0 := ⟨C, hCpos.le⟩
  have hK : LipschitzOnWith K f (Icc a b) := by
    apply (convex_Icc a b).lipschitzOnWith_of_nnnorm_derivWithin_le
      hf.differentiableOn_one
    intro t ht
    exact_mod_cast hC _ (mem_image_of_mem _ ht)
  have hg_lip : LipschitzWith K g := by
    have h := hK.comp (s := univ) (LipschitzWith.projIcc hab.le).lipschitzOnWith hp_mem
    rw [mul_one, lipschitzOnWith_univ] at h
    exact h
  have hp_bv : BoundedVariationOn p univ := by
    apply MonotoneOn.boundedVariationOn (hp_mono.monotoneOn univ) (C := max |a| |b|)
    intro t _
    exact (abs_le_max_abs_abs (Set.projIcc a b hab.le t).2.1
      (Set.projIcc a b hab.le t).2.2)
  have hg_bv : BoundedVariationOn g univ := hK.comp_boundedVariationOn hp_mem hp_bv
  have hg_cont : Continuous g := hg_lip.continuous
  have hright : Function.rightLim g = g := by
    funext t
    exact hg_cont.continuousWithinAt.rightLim_eq
  have hD_int : Integrable D :=
    hD_cont.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hprimitive : ∀ x : ℝ, ∫ t in a..x, D t = g x - g a := by
    intro x
    rcases le_total x a with hxa | hax
    · have hz : ∫ t in x..a, D t = 0 := by
        apply intervalIntegral.integral_zero_ae
        filter_upwards [volume.ae_ne a] with t hne hmem
        rw [uIoc_of_le hxa] at hmem
        have hlt : t < a := lt_of_le_of_ne hmem.2 hne
        have hnot : t ∉ Icc a b := fun hmem ↦ (not_le_of_gt hlt) hmem.1
        simp [D, hnot]
      rw [intervalIntegral.integral_symm, hz, neg_zero]
      have hpa : p a = a := by simp [p]
      have hpx : p x = a := by simp [p, Set.projIcc_of_le_left hab.le hxa]
      simp [g, hpa, hpx]
    · rcases le_total x b with hxb | hbx
      · have hcongr : ∫ t in a..x, D t = ∫ t in a..x, deriv f t := by
          apply intervalIntegral.integral_congr_Ioo_of_le hax
          intro t ht
          have htab : t ∈ Icc a b := ⟨ht.1.le, ht.2.le.trans hxb⟩
          simp only [D, Set.indicator_of_mem htab]
          exact derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 (ht.2.trans_le hxb))
        rw [hcongr, intervalIntegral.integral_deriv_of_contDiffOn_Icc
          (hf.mono (Icc_subset_Icc_right hxb)) hax]
        have hpa : p a = a := by simp [p]
        have hpx : p x = x := by simp [p, Set.projIcc_of_mem hab.le ⟨hax, hxb⟩]
        simp [g, hpa, hpx]
      · have hab_int : ∫ t in a..b, D t = f b - f a := by
          have hcongr : ∫ t in a..b, D t = ∫ t in a..b, deriv f t := by
            apply intervalIntegral.integral_congr_Ioo_of_le hab.le
            intro t ht
            simp only [D, Set.indicator_of_mem (Ioo_subset_Icc_self ht)]
            exact derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
          rw [hcongr, intervalIntegral.integral_deriv_of_contDiffOn_Icc hf hab.le]
        have hzero : ∫ t in b..x, D t = 0 := by
          apply intervalIntegral.integral_zero_ae
          filter_upwards with t ht
          rw [uIoc_of_le hbx] at ht
          have hnot : t ∉ Icc a b := fun hmem ↦ (not_le_of_gt ht.1) hmem.2
          simp [D, hnot]
        rw [← intervalIntegral.integral_add_adjacent_intervals
          hD_int.intervalIntegrable hD_int.intervalIntegrable, hab_int, hzero, add_zero]
        have hpa : p a = a := by simp [p]
        have hpx : p x = b := by simp [p, Set.projIcc_of_right_le hab.le hbx]
        simp [g, hpa, hpx]
  have hinterval : ∀ {c d : ℝ}, c ≤ d → ∫ t in c..d, D t = g d - g c := by
    intro c d hcd
    have hac := intervalIntegral.integral_add_adjacent_intervals
      hD_int.intervalIntegrable hD_int.intervalIntegrable (a := a) (b := c) (c := d)
    rw [hprimitive c, hprimitive d] at hac
    apply eq_sub_iff_add_eq.mpr
    calc
      (∫ t in c..d, D t) + g c = (g c - g a + ∫ t in c..d, D t) + g a := by abel
      _ = (g d - g a) + g a := by rw [hac]
      _ = g d := by abel
  have hmeasure : hg_bv.vectorMeasure = volume.withDensityᵥ D := by
    apply VectorMeasure.ext_of_generateFrom
      {s : Set ℝ | ∃ c d, c ≤ d ∧ s = Ioc c d}
    · rintro s ⟨c, d, hcd, rfl⟩
      rw [hg_bv.vectorMeasure_Ioc hcd, hright, withDensityᵥ_apply hD_int measurableSet_Ioc,
        ← intervalIntegral.integral_of_le hcd, hinterval hcd]
    · convert! BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioc_le ℝ) using 2;
        grind only
    · exact IsSetSemiring.Ioc.isPiSystem
    · rw [hg_bv.vectorMeasure_univ, withDensityᵥ_apply hD_int MeasurableSet.univ]
      simp only [Measure.restrict_univ, D]
      rw [MeasureTheory.integral_indicator measurableSet_Icc,
        MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hab.le,
        intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc hf hab.le]
      have htop : Tendsto g atTop (𝓝 (f b)) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [Ici_mem_atTop b] with t ht
        simp [g, p, Set.projIcc_of_right_le hab.le ht]
      have hbot : Tendsto g atBot (𝓝 (f a)) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [Iic_mem_atBot a] with t ht
        simp [g, p, Set.projIcc_of_le_left hab.le ht]
      rw [tendsto_nhds_unique hg_bv.tendsto_atTop_limUnder htop,
        tendsto_nhds_unique hg_bv.tendsto_atBot_limUnder hbot]
  have hvariation : eVariationOn g univ = eVariationOn f (Icc a b) := by
    apply le_antisymm
    · apply iSup_le
      rintro ⟨n, u, hu, -⟩
      simpa only [g, Function.comp_apply] using
        (eVariationOn.sum_le (f := f) (hp_mono.comp hu)
          (fun i ↦ hp_mem (mem_univ _)))
    · calc
        eVariationOn f (Icc a b) = eVariationOn g (Icc a b) := by
          apply eVariationOn.eq_of_eqOn
          intro t ht
          simp [g, p, Set.projIcc_of_mem hab.le ht]
        _ ≤ eVariationOn g univ := eVariationOn.mono g (subset_univ _)
  calc
    ∫⁻ t in Icc a b, ‖derivWithin f (Icc a b) t‖ₑ
        = (volume.withDensity fun t ↦ ‖D t‖ₑ) univ := by
          rw [withDensity_apply _ MeasurableSet.univ]
          simp only [Measure.restrict_univ]
          rw [← lintegral_indicator measurableSet_Icc]
          apply lintegral_congr
          intro t
          by_cases ht : t ∈ Icc a b <;> simp [D, ht]
    _ = (volume.withDensityᵥ D).variation univ := by
      rw [Measure.variation_withDensityᵥ hD_int]
    _ = hg_bv.vectorMeasure.variation univ := by rw [hmeasure]
    _ ≤ eVariationOn g univ := hg_bv.variation_vectorMeasure_univ_le
    _ = eVariationOn f (Icc a b) := hvariation

/-- The metric total variation of a `C¹` curve in a complete real normed space
equals the integral of the norm of its derivative. -/
theorem eVariationOn_eq_lintegral_enorm_derivWithin {f : ℝ → F} {a b : ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc a b)) :
    eVariationOn f (Icc a b) = ∫⁻ t in Icc a b, ‖derivWithin f (Icc a b) t‖ₑ :=
  le_antisymm (eVariationOn_le_lintegral_enorm_derivWithin hf)
    (lintegral_enorm_derivWithin_le_eVariationOn hf)

end

end TauCeti
