/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Harmonic.Poisson

/-!
# Harnack's inequality on a planar disk

This file proves the Harnack inequality for real-valued harmonic functions on a disk in the
complex plane.  Mathlib's Poisson integral formula writes the value at an interior point as a
circle average weighted by the Poisson kernel; its sharp upper and lower bounds give the
centered Harnack estimate directly.

The Poisson formula first gives the estimate from a sign hypothesis on a boundary circle and
propagates that sign throughout the disk.  Applying this result on concentric intermediate disks
and passing to the outer radius gives the usual formulation for a nonnegative harmonic function
on an open disk.  The pairwise form on a closed subdisk has the standard constant
`((R + r) / (R - r)) ^ 2`.

The argument is the classical Poisson-kernel proof; see Evans, *Partial Differential Equations*,
Chapter 2, Section 2.2.

## Main declarations

* `TauCeti.harnack_inequality_center`: the sharp two-sided comparison with the value at the
  center of a disk.
* `TauCeti.harnack_inequality`: any two values on a smaller closed disk differ by at most the
  standard Harnack factor.
* `TauCeti.eq_zero_on_ball_of_harmonicOnNhd_of_nonneg_of_eq_zero`: a nonnegative harmonic
  function that vanishes at an interior point vanishes throughout the disk.
-/

public section

noncomputable section

namespace TauCeti

open Complex Filter InnerProductSpace Metric Real Topology

private lemma continuousOn_re_herglotzRieszKernel {c w : ℂ} {R : ℝ} (hw : w ∈ ball c R) :
    ContinuousOn (re ∘ herglotzRieszKernel c w) (sphere c R) := by
  rw [herglotzRieszKernel_fun_def]
  have hne : ∀ z ∈ sphere c R, z - c - (w - c) ≠ 0 := by
    grind [mem_ball, mem_sphere]
  fun_prop

private lemma harnack_factor_mono {R s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < R) :
    (R + s) / (R - s) ≤ (R + t) / (R - t) := by
  rw [div_le_div_iff₀ (sub_pos.mpr (lt_of_le_of_lt hst ht)) (sub_pos.mpr ht)]
  nlinarith

private lemma le_harnack_factor_mul_of_mul_le {R d a b : ℝ} (hd : 0 ≤ d) (hdR : d < R)
    (h : (R - d) / (R + d) * a ≤ b) :
    a ≤ (R + d) / (R - d) * b := by
  have hR : 0 < R := hd.trans_lt hdR
  have hfactor : 0 ≤ (R + d) / (R - d) :=
    (div_pos (add_pos_of_pos_of_nonneg hR hd) (sub_pos.mpr hdR)).le
  calc
    a = (R + d) / (R - d) * ((R - d) / (R + d) * a) := by
      field_simp [ne_of_gt (add_pos_of_pos_of_nonneg hR hd),
        ne_of_gt (sub_pos.mpr hdR)]
    _ ≤ (R + d) / (R - d) * b := mul_le_mul_of_nonneg_left h hfactor

variable {f : ℂ → ℝ} {c w : ℂ} {R : ℝ}

/-- **A pointwise kernel bound on the boundary circle transfers to the circle averages.** If `f`
is nonnegative on `sphere c |R|` and `g₁ ≤ g₂` there, then multiplying by `f` preserves the
inequality under `circleAverage`.

The hypotheses are stated on `sphere c |R|`, the circle `circleAverage` integrates over, so no
sign condition on `R` is needed. -/
private theorem circleAverage_smul_le_circleAverage_smul_of_le_on_sphere {g₁ g₂ : ℂ → ℝ}
    (hnonneg : ∀ z ∈ sphere c |R|, 0 ≤ f z)
    (h₁ : CircleIntegrable (g₁ • f) c R) (h₂ : CircleIntegrable (g₂ • f) c R)
    (hle : ∀ z ∈ sphere c |R|, g₁ z ≤ g₂ z) :
    circleAverage (g₁ • f) c R ≤ circleAverage (g₂ • f) c R := by
  refine circleAverage_mono h₁ h₂ fun z hz => ?_
  simp only [smul_eq_mul]
  exact mul_le_mul_of_nonneg_right (hle z hz) (hnonneg z hz)

/-- **The centered Harnack inequality on a planar disk.**

If `f` is harmonic on a neighborhood of the closed disk of radius `R` about `c` and is
nonnegative on its boundary circle, then every `w` in the open disk satisfies

`(R - ‖w - c‖) / (R + ‖w - c‖) * f c ≤ f w
  ≤ (R + ‖w - c‖) / (R - ‖w - c‖) * f c`.

The boundary-only sign assumption is sufficient: both inequalities follow from the Poisson
integral formula and the pointwise bounds on the Poisson kernel. -/
theorem harnack_inequality_center_of_nonneg_on_sphere (hf : HarmonicOnNhd f (closedBall c R))
    (hnonneg : ∀ z ∈ sphere c R, 0 ≤ f z) (hw : w ∈ ball c R) :
    (R - ‖w - c‖) / (R + ‖w - c‖) * f c ≤ f w ∧
      f w ≤ (R + ‖w - c‖) / (R - ‖w - c‖) * f c := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hfcont : ContinuousOn f (sphere c R) :=
    hf.contDiffOn.continuousOn.mono sphere_subset_closedBall
  have hfint : CircleIntegrable f c R := hfcont.circleIntegrable hR.le
  have hkernelcont :
      ContinuousOn (re ∘ herglotzRieszKernel c w) (sphere c |R|) := by
    simpa [abs_of_pos hR] using continuousOn_re_herglotzRieszKernel hw
  have hkernelint : CircleIntegrable ((re ∘ herglotzRieszKernel c w) • f) c R :=
    hfint.smul_of_continuousOn hkernelcont
  have hnonneg' : ∀ z ∈ sphere c |R|, 0 ≤ f z := fun z hz =>
    hnonneg z (by simpa [abs_of_pos hR] using hz)
  have hmean : circleAverage f c R = f c := by
    apply HarmonicOnNhd.circleAverage_eq
    simpa [abs_of_pos hR] using hf
  constructor
  · calc
      (R - ‖w - c‖) / (R + ‖w - c‖) * f c =
          circleAverage
            (((R - ‖w - c‖) / (R + ‖w - c‖)) • f) c R := by
              rw [circleAverage_smul, hmean]
              simp [smul_eq_mul]
      _ ≤ circleAverage ((re ∘ herglotzRieszKernel c w) • f) c R := by
        refine circleAverage_smul_le_circleAverage_smul_of_le_on_sphere hnonneg'
          hfint.const_smul hkernelint fun z hz => ?_
        simpa [herglotzRieszKernel_def] using
          le_re_herglotzRieszKernel (by simpa [abs_of_pos hR] using hz) hw
      _ = f w := hf.circleAverage_re_herglotzRieszKernel_smul hw
  · calc
      f w = circleAverage ((re ∘ herglotzRieszKernel c w) • f) c R :=
        (hf.circleAverage_re_herglotzRieszKernel_smul hw).symm
      _ ≤ circleAverage
          (((R + ‖w - c‖) / (R - ‖w - c‖)) • f) c R := by
        refine circleAverage_smul_le_circleAverage_smul_of_le_on_sphere hnonneg'
          hkernelint hfint.const_smul fun z hz => ?_
        simpa [herglotzRieszKernel_def] using
          re_herglotzRieszKernel_le (by simpa [abs_of_pos hR] using hz) hw
      _ = (R + ‖w - c‖) / (R - ‖w - c‖) * f c := by
        rw [circleAverage_smul, hmean]
        simp [smul_eq_mul]

/-- A function harmonic near a closed planar disk and nonnegative on its boundary circle is
nonnegative throughout the open disk. -/
theorem nonneg_of_mem_ball_of_harmonicOnNhd_of_nonneg_on_sphere
    (hf : HarmonicOnNhd f (closedBall c R))
    (hnonneg : ∀ z ∈ sphere c R, 0 ≤ f z) (hw : w ∈ ball c R) :
    0 ≤ f w := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hmean : circleAverage f c R = f c := by
    apply HarmonicOnNhd.circleAverage_eq
    simpa [abs_of_pos hR] using hf
  have hfc : 0 ≤ f c := by
    rw [← hmean]
    apply circleAverage_nonneg_of_nonneg
    intro z hz
    exact hnonneg z (by simpa [abs_of_pos hR] using hz)
  have hwlower :=
    (harnack_inequality_center_of_nonneg_on_sphere hf hnonneg hw).1
  have hfactor :
      0 ≤ (R - ‖w - c‖) / (R + ‖w - c‖) := by
    apply div_nonneg
    · exact sub_nonneg.mpr (mem_ball_iff_norm.mp hw).le
    · positivity
  exact (mul_nonneg hfactor hfc).trans hwlower

/-- **Harnack's inequality on a smaller planar disk.**

Let `0 ≤ r < R`.  If `f` is harmonic on a neighborhood of `closedBall c R` and nonnegative on
its boundary, then for any `x, y ∈ closedBall c r`,

`f x ≤ ((R + r) / (R - r)) ^ 2 * f y`.

This pairwise form follows by comparing both values with `f c`. -/
theorem harnack_inequality_of_nonneg_on_sphere (hf : HarmonicOnNhd f (closedBall c R))
    (hnonneg : ∀ z ∈ sphere c R, 0 ≤ f z) {r : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {x y : ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    f x ≤ ((R + r) / (R - r)) ^ 2 * f y := by
  have hR : 0 < R := hr.trans_lt hrR
  have hdx : ‖x - c‖ ≤ r := by simpa [dist_eq_norm] using mem_closedBall.mp hx
  have hdy : ‖y - c‖ ≤ r := by simpa [dist_eq_norm] using mem_closedBall.mp hy
  have hxR : x ∈ ball c R := by
    rw [mem_ball, dist_eq_norm]
    exact hdx.trans_lt hrR
  have hyR : y ∈ ball c R := by
    rw [mem_ball, dist_eq_norm]
    exact hdy.trans_lt hrR
  have hxcenter :=
    (harnack_inequality_center_of_nonneg_on_sphere hf hnonneg hxR).2
  have hycenter :=
    (harnack_inequality_center_of_nonneg_on_sphere hf hnonneg hyR).1
  have hfc :=
    nonneg_of_mem_ball_of_harmonicOnNhd_of_nonneg_on_sphere hf hnonneg
      (mem_ball_self hR)
  have hfy :=
    nonneg_of_mem_ball_of_harmonicOnNhd_of_nonneg_on_sphere hf hnonneg hyR
  have hfactorx :
      (R + ‖x - c‖) / (R - ‖x - c‖) ≤ (R + r) / (R - r) :=
    harnack_factor_mono (norm_nonneg _) hdx hrR
  have hfactory :
      (R + ‖y - c‖) / (R - ‖y - c‖) ≤ (R + r) / (R - r) :=
    harnack_factor_mono (norm_nonneg _) hdy hrR
  have hx_le : f x ≤ (R + r) / (R - r) * f c :=
    hxcenter.trans (mul_le_mul_of_nonneg_right hfactorx hfc)
  have hfc_le : f c ≤ (R + r) / (R - r) * f y :=
    (le_harnack_factor_mul_of_mul_le (norm_nonneg _) (hdy.trans_lt hrR) hycenter).trans
      (mul_le_mul_of_nonneg_right hfactory hfy)
  have hfactor_nonneg : 0 ≤ (R + r) / (R - r) :=
    (div_pos (add_pos_of_pos_of_nonneg hR hr) (sub_pos.mpr hrR)).le
  calc
    f x ≤ (R + r) / (R - r) * f c := hx_le
    _ ≤ (R + r) / (R - r) * ((R + r) / (R - r) * f y) :=
      mul_le_mul_of_nonneg_left hfc_le hfactor_nonneg
    _ = ((R + r) / (R - r)) ^ 2 * f y := by ring

/-- If a function is harmonic near a closed planar disk, is nonnegative on the boundary, and
vanishes at an interior point, then it vanishes throughout the open disk.

This is the zero case of Harnack's inequality, and is the strong minimum principle for this
setting. -/
theorem eq_zero_on_ball_of_harmonicOnNhd_of_nonneg_on_sphere_of_eq_zero
    (hf : HarmonicOnNhd f (closedBall c R))
    (hnonneg : ∀ z ∈ sphere c R, 0 ≤ f z) (hw : w ∈ ball c R) (hfw : f w = 0) :
    Set.EqOn f 0 (ball c R) := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hnonneg_ball :
      ∀ z ∈ ball c R, 0 ≤ f z :=
    fun _ hz ↦
      nonneg_of_mem_ball_of_harmonicOnNhd_of_nonneg_on_sphere hf hnonneg hz
  have hfc : 0 ≤ f c := hnonneg_ball c (mem_ball_self hR)
  have hwlower :=
    (harnack_inequality_center_of_nonneg_on_sphere hf hnonneg hw).1
  have hwfactor :
      0 < (R - ‖w - c‖) / (R + ‖w - c‖) := by
    exact div_pos (sub_pos.mpr (by simpa [mem_ball, dist_eq_norm] using hw))
      (add_pos_of_pos_of_nonneg hR (norm_nonneg _))
  have hfc_zero : f c = 0 := by
    have hprod_nonpos :
        (R - ‖w - c‖) / (R + ‖w - c‖) * f c ≤ 0 := by
      simpa [hfw] using hwlower
    have hprod_zero :
        (R - ‖w - c‖) / (R + ‖w - c‖) * f c = 0 :=
      le_antisymm hprod_nonpos (mul_nonneg hwfactor.le hfc)
    exact (mul_eq_zero.mp hprod_zero).resolve_left hwfactor.ne'
  intro z hz
  have hz_bounds :=
    harnack_inequality_center_of_nonneg_on_sphere hf hnonneg hz
  apply le_antisymm
  · simpa [hfc_zero] using hz_bounds.2
  · simpa using hnonneg_ball z hz

/-- **The centered Harnack inequality on an open planar disk.**

If `f` is harmonic and nonnegative throughout the open disk of radius `R` about `c`, then
every `w` in the disk satisfies the sharp two-sided comparison with `f c`. -/
theorem harnack_inequality_center (hf : HarmonicOnNhd f (ball c R))
    (hnonneg : ∀ z ∈ ball c R, 0 ≤ f z) (hw : w ∈ ball c R) :
    (R - ‖w - c‖) / (R + ‖w - c‖) * f c ≤ f w ∧
      f w ≤ (R + ‖w - c‖) / (R - ‖w - c‖) * f c := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hdR : ‖w - c‖ < R := mem_ball_iff_norm.mp hw
  have hlowerTendsto :
      Tendsto (fun ρ : ℝ ↦ (ρ - ‖w - c‖) / (ρ + ‖w - c‖) * f c)
        (𝓝[<] R)
        (𝓝 ((R - ‖w - c‖) / (R + ‖w - c‖) * f c)) := by
    apply Tendsto.mono_left ?_ nhdsWithin_le_nhds
    exact
      ((tendsto_id.sub tendsto_const_nhds).div
        (tendsto_id.add tendsto_const_nhds)
        (ne_of_gt (add_pos_of_pos_of_nonneg hR (norm_nonneg _)))).mul
        tendsto_const_nhds
  have hupperTendsto :
      Tendsto (fun ρ : ℝ ↦ (ρ + ‖w - c‖) / (ρ - ‖w - c‖) * f c)
        (𝓝[<] R)
        (𝓝 ((R + ‖w - c‖) / (R - ‖w - c‖) * f c)) := by
    apply Tendsto.mono_left ?_ nhdsWithin_le_nhds
    exact
      ((tendsto_id.add tendsto_const_nhds).div
        (tendsto_id.sub tendsto_const_nhds) (sub_pos.mpr hdR).ne').mul
        tendsto_const_nhds
  constructor
  · apply le_of_tendsto hlowerTendsto
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hdR),
      self_mem_nhdsWithin] with ρ (hρd : ‖w - c‖ < ρ) (hρR : ρ < R)
    have hwρ : w ∈ ball c ρ := by
      simpa [mem_ball, dist_eq_norm] using hρd
    exact
      (harnack_inequality_center_of_nonneg_on_sphere
        (hf.mono (closedBall_subset_ball hρR))
        (fun z hz ↦ hnonneg z (sphere_subset_ball hρR hz)) hwρ).1
  · apply ge_of_tendsto hupperTendsto
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hdR),
      self_mem_nhdsWithin] with ρ (hρd : ‖w - c‖ < ρ) (hρR : ρ < R)
    have hwρ : w ∈ ball c ρ := by
      simpa [mem_ball, dist_eq_norm] using hρd
    exact
      (harnack_inequality_center_of_nonneg_on_sphere
        (hf.mono (closedBall_subset_ball hρR))
        (fun z hz ↦ hnonneg z (sphere_subset_ball hρR hz)) hwρ).2

/-- **Harnack's inequality on a smaller closed disk.**

Let `0 ≤ r < R`.  If `f` is harmonic and nonnegative throughout `ball c R`, then for any
`x, y ∈ closedBall c r`,

`f x ≤ ((R + r) / (R - r)) ^ 2 * f y`. -/
theorem harnack_inequality (hf : HarmonicOnNhd f (ball c R))
    (hnonneg : ∀ z ∈ ball c R, 0 ≤ f z) {r : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {x y : ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    f x ≤ ((R + r) / (R - r)) ^ 2 * f y := by
  have hfactorTendsto :
      Tendsto (fun ρ : ℝ ↦ ((ρ + r) / (ρ - r)) ^ 2 * f y) (𝓝[<] R)
        (𝓝 (((R + r) / (R - r)) ^ 2 * f y)) := by
    apply Tendsto.mono_left ?_ nhdsWithin_le_nhds
    exact
      (((tendsto_id.add tendsto_const_nhds).div
        (tendsto_id.sub tendsto_const_nhds) (sub_pos.mpr hrR).ne').pow 2).mul
        tendsto_const_nhds
  apply ge_of_tendsto hfactorTendsto
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hrR),
    self_mem_nhdsWithin] with ρ (hrρ : r < ρ) (hρR : ρ < R)
  exact harnack_inequality_of_nonneg_on_sphere
    (hf.mono (closedBall_subset_ball hρR))
    (fun z hz ↦ hnonneg z (sphere_subset_ball hρR hz)) hr hrρ hx hy

/-- A nonnegative harmonic function on an open planar disk that vanishes at one point vanishes
throughout the disk.  This is the zero case of Harnack's inequality. -/
theorem eq_zero_on_ball_of_harmonicOnNhd_of_nonneg_of_eq_zero (hf : HarmonicOnNhd f (ball c R))
    (hnonneg : ∀ z ∈ ball c R, 0 ≤ f z) (hw : w ∈ ball c R) (hfw : f w = 0) :
    Set.EqOn f 0 (ball c R) := by
  intro z hz
  have hdzR : ‖z - c‖ < R := mem_ball_iff_norm.mp hz
  have hdwR : ‖w - c‖ < R := mem_ball_iff_norm.mp hw
  obtain ⟨r, hdr, hrR⟩ := exists_between (max_lt hdzR hdwR)
  have hr : 0 ≤ r :=
    (norm_nonneg (z - c)).trans ((le_max_left _ _).trans hdr.le)
  have hzclosed : z ∈ closedBall c r := by
    rw [mem_closedBall, dist_eq_norm]
    exact (le_max_left _ _).trans hdr.le
  have hwclosed : w ∈ closedBall c r := by
    rw [mem_closedBall, dist_eq_norm]
    exact (le_max_right _ _).trans hdr.le
  have hzw := harnack_inequality hf hnonneg hr hrR hzclosed hwclosed
  apply le_antisymm
  · simpa [hfw] using hzw
  · simpa using hnonneg z hz

end TauCeti

end

end
