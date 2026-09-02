/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Beta.Cdf

/-!
# Fisher's F distribution

## Main results

* `fisherSnedecorMeasure`
* `fisherSnedecorMeasure_eq_map`
* `isProbabilityMeasure_fisherSnedecorMeasure_iff`
* `fisherSnedecorMap_image_Ioo`
* `ae_mem_Ioi_fisherSnedecorMeasure`
* `cdf_fisherSnedecorMeasure_eq`

This file begins the elementary API for Fisher's F law.  For positive degrees of freedom `m` and
`n`, it realizes the law as the image of `betaMeasure (m / 2) (n / 2)` under
`u ↦ (n / m) * u / (1 - u)`.  This gives a probability measure and its cumulative distribution
function without introducing a second probability-law abstraction.  The density and the
moment and transform formulas are subsequent parts of the roadmap development.

The change of variables is useful in its own right: the inverse map on the positive half-line is
`x ↦ m * x / (n + m * x)`.  The cdf theorem below records this inverse explicitly, in the same
regularized-incomplete-beta convention used by the beta API.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 3, the **Fisher's F** target.
* N. L. Johnson, S. Kotz, and N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), chapter 27.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {m n x : ℝ}

/-! ### The beta-to-F transformation -/

/-- The formula for the transformation from a beta variable to an F variable.

For positive `m` and `n`, this function is strictly monotone on `Iio 1` and maps `Ioo 0 1`
onto `Ioi 0`. -/
def fisherSnedecorMap (m n : ℝ) (u : ℝ) : ℝ := (n / m) * u / (1 - u)

/-- The defining formula for `fisherSnedecorMap`. -/
theorem fisherSnedecorMap_def (m n u : ℝ) :
    fisherSnedecorMap m n u = (n / m) * u / (1 - u) := (rfl)

/-- The formula for the inverse transformation on the positive half-line.

For positive `m` and `n`, this is the inverse of `fisherSnedecorMap m n` between `Ioi 0` and
`Ioo 0 1`. -/
def fisherSnedecorMapInv (m n : ℝ) (x : ℝ) : ℝ := m * x / (n + m * x)

/-- The defining formula for `fisherSnedecorMapInv`. -/
theorem fisherSnedecorMapInv_def (m n x : ℝ) :
    fisherSnedecorMapInv m n x = m * x / (n + m * x) := (rfl)

/-- The Fisher--Snedecor law with degrees of freedom `m` and `n`.  Invalid parameters are
the zero measure; for valid parameters this is the beta law pushed forward by the standard
beta-to-F transformation. -/
def fisherSnedecorMeasure (m n : ℝ) : Measure ℝ :=
  if 0 < m ∧ 0 < n then
    (betaMeasure (m / 2) (n / 2)).map (fisherSnedecorMap m n)
  else 0

/-- For invalid degrees of freedom, the Fisher--Snedecor measure is zero. -/
@[simp]
theorem fisherSnedecorMeasure_of_not_pos (h : ¬ (0 < m ∧ 0 < n)) :
    fisherSnedecorMeasure m n = 0 := by
  simp [fisherSnedecorMeasure, h]

/-- For positive degrees of freedom, the Fisher--Snedecor measure is the beta-to-F pushforward. -/
theorem fisherSnedecorMeasure_eq_map (hm : 0 < m) (hn : 0 < n) :
    fisherSnedecorMeasure m n =
      (betaMeasure (m / 2) (n / 2)).map (fisherSnedecorMap m n) := by
  simp [fisherSnedecorMeasure, hm, hn]

/-- The Fisher--Snedecor measure is a probability measure for positive degrees of freedom. -/
theorem isProbabilityMeasure_fisherSnedecorMeasure (hm : 0 < m) (hn : 0 < n) :
    IsProbabilityMeasure (fisherSnedecorMeasure m n) := by
  rw [fisherSnedecorMeasure_eq_map hm hn]
  let _ : IsProbabilityMeasure (betaMeasure (m / 2) (n / 2)) :=
    isProbabilityMeasureBeta (by linarith) (by linarith)
  infer_instance

/-- The Fisher--Snedecor measure is a probability measure exactly when both degrees of freedom
are positive. -/
@[simp]
theorem isProbabilityMeasure_fisherSnedecorMeasure_iff :
    IsProbabilityMeasure (fisherSnedecorMeasure m n) ↔ 0 < m ∧ 0 < n := by
  constructor
  · intro h
    by_contra hmn
    rw [fisherSnedecorMeasure_of_not_pos hmn] at h
    exact (@IsProbabilityMeasure.ne_zero ℝ _ 0 h) rfl
  · rintro ⟨hm, hn⟩
    exact isProbabilityMeasure_fisherSnedecorMeasure hm hn

/-- The beta-to-F transformation is measurable for all parameter values. -/
@[fun_prop]
theorem measurable_fisherSnedecorMap (m n : ℝ) :
    Measurable (fisherSnedecorMap m n) := by
  rw [show fisherSnedecorMap m n = (fun u : ℝ => (n / m) * u / (1 - u)) by
    funext u
    exact fisherSnedecorMap_def m n u]
  fun_prop

/-- The beta-to-F inverse transformation is measurable for all parameter values. -/
@[fun_prop]
theorem measurable_fisherSnedecorMapInv (m n : ℝ) :
    Measurable (fisherSnedecorMapInv m n) := by
  rw [show fisherSnedecorMapInv m n = (fun x : ℝ => m * x / (n + m * x)) by
    funext x
    exact fisherSnedecorMapInv_def m n x]
  fun_prop

/-! ### Support and the inverse -/

/-- For positive degrees of freedom, the beta-to-F map sends `Ioo 0 1` into `Ioi 0`. -/
theorem fisherSnedecorMap_mem_Ioi (hm : 0 < m) (hn : 0 < n) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    fisherSnedecorMap m n u ∈ Ioi 0 := by
  rcases hu with ⟨hu0, hu1⟩
  rw [fisherSnedecorMap_def]
  exact div_pos (mul_pos (div_pos hn hm) hu0) (sub_pos.mpr hu1)

/-- For positive degrees of freedom, the beta-to-F map is strictly monotone on `Iio 1`. -/
theorem fisherSnedecorMap_strictMonoOn (hm : 0 < m) (hn : 0 < n) :
    StrictMonoOn (fisherSnedecorMap m n) (Iio (1 : ℝ)) := by
  intro u hu v hv huv
  rw [fisherSnedecorMap_def, fisherSnedecorMap_def]
  have hnm : 0 < n / m := div_pos hn hm
  apply (div_lt_div_iff₀ (sub_pos.mpr hu) (sub_pos.mpr hv)).2
  nlinarith [mul_pos hnm (sub_pos.mpr huv)]

/-- If `m`, `n`, and `1 - u` are nonzero, the inverse transformation after the
beta-to-F map is the identity. -/
theorem fisherSnedecorMapInv_map (hm : m ≠ 0) (hn : n ≠ 0) {u : ℝ}
    (hu : u ≠ 1) :
    fisherSnedecorMapInv m n (fisherSnedecorMap m n u) = u := by
  rw [fisherSnedecorMapInv_def, fisherSnedecorMap_def]
  field_simp [hm, hn, sub_ne_zero.mpr (Ne.symm hu)]
  ring

/-- If `m`, `n`, and `n + m * x` are nonzero, the beta-to-F map after the inverse
transformation is the identity. -/
theorem fisherSnedecorMap_mapInv (hm : m ≠ 0) (hn : n ≠ 0) {x : ℝ}
    (hden : n + m * x ≠ 0) :
    fisherSnedecorMap m n (fisherSnedecorMapInv m n x) = x := by
  rw [fisherSnedecorMap_def, fisherSnedecorMapInv_def]
  field_simp [hm, hn, hden]
  ring

/-- For positive degrees of freedom, the inverse transformation maps `Ioi 0` into `Ioo 0 1`. -/
theorem fisherSnedecorMapInv_mem_Ioo (hm : 0 < m) (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    fisherSnedecorMapInv m n x ∈ Ioo (0 : ℝ) 1 := by
  rw [fisherSnedecorMapInv_def]
  constructor
  · exact div_pos (mul_pos hm hx) (by positivity)
  · rw [div_lt_one (by positivity)]
    nlinarith

/-- For positive degrees of freedom, the beta-to-F map sends `Ioo 0 1` onto `Ioi 0`. -/
theorem fisherSnedecorMap_image_Ioo (hm : 0 < m) (hn : 0 < n) :
    fisherSnedecorMap m n '' Ioo (0 : ℝ) 1 = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact fisherSnedecorMap_mem_Ioi hm hn hu
  · intro hx
    have hden : 0 < n + m * x := add_pos hn (mul_pos hm hx)
    exact ⟨fisherSnedecorMapInv m n x, fisherSnedecorMapInv_mem_Ioo hm hn hx,
      fisherSnedecorMap_mapInv (ne_of_gt hm) (ne_of_gt hn) (ne_of_gt hden)⟩

private theorem ae_mem_Ioo_betaMeasure (α β : ℝ) :
    ∀ᵐ u ∂betaMeasure α β, u ∈ Ioo (0 : ℝ) 1 := by
  let _ : NullSingletonClass (betaMeasure α β) := by
    rw [betaMeasure]
    infer_instance
  filter_upwards [(Ioo_ae_eq_Icc : Ioo (0 : ℝ) 1 =ᵐ[betaMeasure α β] Icc 0 1),
      ae_mem_Icc_betaMeasure α β] with u hu hIcc
  rw [hu]
  exact hIcc

/-- On the beta law, the preimage of `Iic x` under the beta-to-F map agrees a.e. with
`Iic (fisherSnedecorMapInv m n x)` for positive `x`. -/
private theorem fisherSnedecorMap_preimage_Iic_ae (hm : 0 < m) (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    fisherSnedecorMap m n ⁻¹' Iic x =ᵐ[betaMeasure (m / 2) (n / 2)]
      Iic (fisherSnedecorMapInv m n x) := by
  filter_upwards [ae_mem_Ioo_betaMeasure (m / 2) (n / 2)] with u hu
  simp only [mem_preimage, mem_Iic]
  apply propext
  have hden : 0 < n + m * x := add_pos hn (mul_pos hm hx)
  have h_inv := fisherSnedecorMap_mapInv (x := x) (ne_of_gt hm) (ne_of_gt hn)
    (ne_of_gt hden)
  nth_rewrite 1 [← h_inv]
  exact (fisherSnedecorMap_strictMonoOn hm hn).le_iff_le hu.2
    (fisherSnedecorMapInv_mem_Ioo hm hn hx).2

/-- For positive degrees of freedom, the Fisher--Snedecor law is almost surely positive. -/
theorem ae_mem_Ioi_fisherSnedecorMeasure (hm : 0 < m) (hn : 0 < n) :
    ∀ᵐ x ∂fisherSnedecorMeasure m n, x ∈ Ioi 0 := by
  rw [fisherSnedecorMeasure_eq_map hm hn, ae_map_iff
    (measurable_fisherSnedecorMap m n).aemeasurable (by measurability)]
  filter_upwards [ae_mem_Ioo_betaMeasure (m / 2) (n / 2)] with u hu
  exact fisherSnedecorMap_mem_Ioi hm hn hu

/-! ### The cdf -/

/-- For positive degrees of freedom, the cdf is `0` when `x ≤ 0` and is the regularized
incomplete beta function at the inverse beta-to-F coordinate when `0 < x`. -/
theorem cdf_fisherSnedecorMeasure_eq (hm : 0 < m) (hn : 0 < n) (x : ℝ) :
  cdf (fisherSnedecorMeasure m n) x =
      if x ≤ 0 then 0 else
      regularizedIncompleteBeta (m / 2) (n / 2) (fisherSnedecorMapInv m n x) := by
  let _ : IsProbabilityMeasure (fisherSnedecorMeasure m n) :=
    isProbabilityMeasure_fisherSnedecorMeasure hm hn
  let _ : IsProbabilityMeasure (betaMeasure (m / 2) (n / 2)) :=
    isProbabilityMeasureBeta (by linarith) (by linarith)
  by_cases hx : x ≤ 0
  · rw [ite_eq_left hx]
    rw [cdf_eq_real]
    have hpre : (Iic x : Set ℝ) =ᵐ[fisherSnedecorMeasure m n] ∅ := by
      filter_upwards [ae_mem_Ioi_fisherSnedecorMeasure hm hn] with y hy
      apply propext
      constructor
      · intro hyx
        exact (not_lt_of_ge (hyx.trans hx)) hy
      · intro hyempty
        simp at hyempty
    rw [measureReal_congr hpre, measureReal_empty]
  · have hx' : 0 < x := lt_of_not_ge hx
    rw [ite_eq_right hx]
    rw [cdf_eq_real, fisherSnedecorMeasure_eq_map hm hn,
      map_measureReal_apply (measurable_fisherSnedecorMap m n) measurableSet_Iic,
      measureReal_congr (fisherSnedecorMap_preimage_Iic_ae hm hn hx')]
    rw [← cdf_eq_real]
    exact cdf_betaMeasure_eq (by linarith) (by linarith) _

end Probability

end TauCeti
