/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Beta.Cdf

/-!
# Fisher's F distribution

This file begins the elementary API for Fisher's F law.  For positive degrees of freedom `m` and
`n`, it realizes the law as the image of a beta law under
`u ↦ (n / m) * u / (1 - u)`.  This gives a probability measure and its cumulative distribution
function without introducing a second probability-law abstraction.  The density and the
moment and transform formulas are subsequent parts of the roadmap development.

The change of variables is useful in its own right: the inverse map on the positive half-line is
`x ↦ m * x / (n + m * x)`.  The cdf theorem below records this inverse explicitly, in the same
regularized-incomplete-beta convention used by the beta and Student's t APIs.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 3, the **Fisher's F** target.
* N. L. Johnson, S. Kotz, and N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), chapter 25.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {m n x : ℝ}

/-! ### The beta-to-F transformation -/

/-- The monotone transformation from a beta variable to an F variable. -/
def fisherSnedecorMap (m n : ℝ) (u : ℝ) : ℝ := (n / m) * u / (1 - u)

/-- The inverse transformation on the positive half-line. -/
def fisherSnedecorInv (m n : ℝ) (x : ℝ) : ℝ := m * x / (n + m * x)

/-- The Fisher--Snedecor law with degrees of freedom `m` and `n`.  Invalid parameters are
the zero measure; for valid parameters this is the beta law pushed forward by the standard
beta-to-F transformation. -/
def fisherSnedecorMeasure (m n : ℝ) : Measure ℝ :=
  if 0 < m ∧ 0 < n then
    (betaMeasure (m / 2) (n / 2)).map (fisherSnedecorMap m n)
  else 0

@[simp]
theorem fisherSnedecorMeasure_of_not_pos (h : ¬ (0 < m ∧ 0 < n)) :
    fisherSnedecorMeasure m n = 0 := by
  simp [fisherSnedecorMeasure, h]

theorem fisherSnedecorMeasure_map (hm : 0 < m) (hn : 0 < n) :
    fisherSnedecorMeasure m n =
      (betaMeasure (m / 2) (n / 2)).map (fisherSnedecorMap m n) := by
  simp [fisherSnedecorMeasure, hm, hn]

theorem isProbabilityMeasure_fisherSnedecorMeasure (hm : 0 < m) (hn : 0 < n) :
    IsProbabilityMeasure (fisherSnedecorMeasure m n) := by
  rw [fisherSnedecorMeasure_map hm hn]
  let _ : IsProbabilityMeasure (betaMeasure (m / 2) (n / 2)) :=
    isProbabilityMeasureBeta (by linarith) (by linarith)
  infer_instance

@[simp]
theorem isProbabilityMeasure_fisherSnedecorMeasure_iff :
    IsProbabilityMeasure (fisherSnedecorMeasure m n) ↔ 0 < m ∧ 0 < n := by
  constructor
  · intro h
    by_contra hmn
    rw [fisherSnedecorMeasure_of_not_pos hmn] at h
    have h_univ : (0 : Measure ℝ) Set.univ = 1 :=
      @IsProbabilityMeasure.measure_univ ℝ _ 0 h
    have h_univ' : (0 : ℝ≥0∞) = 1 := by
      -- `measure_univ` is ENNReal-valued, while the zero-measure expression is polymorphic.
      change (0 : ℝ≥0∞) = 1 at h_univ
      exact h_univ
    exact (zero_ne_one h_univ').elim
  · rintro ⟨hm, hn⟩
    exact isProbabilityMeasure_fisherSnedecorMeasure hm hn

theorem measurable_fisherSnedecorMap (m n : ℝ) :
    Measurable (fisherSnedecorMap m n) := by
  unfold fisherSnedecorMap
  fun_prop

/-! ### Support and the inverse -/

theorem fisherSnedecorMap_mem_Ioi (hm : 0 < m) (hn : 0 < n) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    fisherSnedecorMap m n u ∈ Ioi 0 := by
  rcases hu with ⟨hu0, hu1⟩
  unfold fisherSnedecorMap
  exact div_pos (mul_pos (div_pos hn hm) hu0) (sub_pos.mpr hu1)

theorem fisherSnedecorMap_strictMonoOn (hm : 0 < m) (hn : 0 < n) :
    StrictMonoOn (fisherSnedecorMap m n) (Ioo (0 : ℝ) 1) := by
  intro u hu v hv huv
  rcases hu with ⟨hu0, hu1⟩
  rcases hv with ⟨hv0, hv1⟩
  unfold fisherSnedecorMap
  have hnm : 0 < n / m := div_pos hn hm
  apply (div_lt_div_iff₀ (sub_pos.mpr hu1) (sub_pos.mpr hv1)).2
  nlinarith [mul_pos hnm (sub_pos.mpr huv)]

theorem fisherSnedecorMap_inv (hm : 0 < m) (hn : 0 < n) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    fisherSnedecorInv m n (fisherSnedecorMap m n u) = u := by
  unfold fisherSnedecorInv fisherSnedecorMap
  field_simp [ne_of_gt hm, ne_of_gt hn, ne_of_gt (sub_pos.mpr hu.2)]
  ring

theorem fisherSnedecorInv_map (hm : 0 < m) (hn : 0 < n) {x : ℝ}
    (hx : 0 < x) :
    fisherSnedecorMap m n (fisherSnedecorInv m n x) = x := by
  unfold fisherSnedecorInv fisherSnedecorMap
  have hden : 0 < n + m * x := by positivity
  have hden' : 0 < 1 - m * x / (n + m * x) := by
    -- This identity exposes the positive denominator needed for the inverse map.
    rw [show 1 - m * x / (n + m * x) = n / (n + m * x) by field_simp; ring]
    exact div_pos hn hden
  field_simp [ne_of_gt hm, ne_of_gt hn, ne_of_gt hden, ne_of_gt hden']
  ring

theorem fisherSnedecorMap_inv_mem_Ioo (hm : 0 < m) (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    fisherSnedecorInv m n x ∈ Ioo (0 : ℝ) 1 := by
  unfold fisherSnedecorInv
  constructor
  · exact div_pos (mul_pos hm hx) (by positivity)
  · rw [div_lt_one (by positivity)]
    nlinarith

theorem fisherSnedecorMap_nonneg_on (hm : 0 < m) (hn : 0 < n) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ fisherSnedecorMap m n u := by
  rcases hu with ⟨hu0, hu1⟩
  rcases hu1.lt_or_eq with hu1' | rfl
  · exact div_nonneg (mul_nonneg (div_pos hn hm).le hu0) (sub_nonneg.mpr hu1'.le)
  · simp [fisherSnedecorMap]

theorem fisherSnedecorMap_image_Ioo (hm : 0 < m) (hn : 0 < n) :
    fisherSnedecorMap m n '' Ioo (0 : ℝ) 1 = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact fisherSnedecorMap_mem_Ioi hm hn hu
  · intro hx
    exact ⟨fisherSnedecorInv m n x, fisherSnedecorMap_inv_mem_Ioo hm hn hx,
      fisherSnedecorInv_map hm hn hx⟩

theorem fisherSnedecorMap_preimage_Iic_ae (hm : 0 < m) (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    fisherSnedecorMap m n ⁻¹' Iic x =ᵐ[betaMeasure (m / 2) (n / 2)]
      Iic (fisherSnedecorInv m n x) := by
  let _ : NullSingletonClass (betaMeasure (m / 2) (n / 2)) := by
    rw [betaMeasure]
    infer_instance
  filter_upwards [(Ioo_ae_eq_Icc : Ioo (0 : ℝ) 1 =ᵐ[betaMeasure (m / 2) (n / 2)] Icc 0 1),
      ae_mem_Icc_betaMeasure (m / 2) (n / 2)] with u hu hIcc
  have hu01 : u ∈ Ioo (0 : ℝ) 1 := by
    rw [hu]
    exact hIcc
  simp only [mem_preimage, mem_Iic]
  unfold fisherSnedecorMap fisherSnedecorInv
  have h₁ : 0 < 1 - u := sub_pos.mpr hu01.2
  have h₂ : 0 < n + m * x := by positivity
  apply propext
  constructor
  · intro h
    have h' : n / m * u ≤ x * (1 - u) := (div_le_iff₀ h₁).mp h
    apply (le_div_iff₀ h₂).2
    field_simp at h' ⊢
    nlinarith
  · intro h
    apply (div_le_iff₀ h₁).2
    have h' : u * (n + m * x) ≤ m * x := (le_div_iff₀ h₂).mp h
    field_simp at h' ⊢
    nlinarith

/-! ### The cdf -/

/-- The cdf of the beta-to-F realization is the regularized incomplete beta function at the
inverse beta-to-F coordinate. -/
theorem cdf_fisherSnedecorMeasure_eq (hm : 0 < m) (hn : 0 < n) (x : ℝ) :
  cdf (fisherSnedecorMeasure m n) x =
      if x ≤ 0 then 0 else
      regularizedIncompleteBeta (m / 2) (n / 2) (fisherSnedecorInv m n x) := by
  let _ : IsProbabilityMeasure (fisherSnedecorMeasure m n) :=
    isProbabilityMeasure_fisherSnedecorMeasure hm hn
  let _ : IsProbabilityMeasure (betaMeasure (m / 2) (n / 2)) :=
    isProbabilityMeasureBeta (by linarith) (by linarith)
  let _ : NullSingletonClass (betaMeasure (m / 2) (n / 2)) := by
    rw [betaMeasure]
    infer_instance
  by_cases hx : x ≤ 0
  · rw [ite_eq_left hx]
    rw [cdf_eq_real, fisherSnedecorMeasure_map hm hn,
    map_measureReal_apply (measurable_fisherSnedecorMap m n) measurableSet_Iic]
    have hpre : fisherSnedecorMap m n ⁻¹' Iic x =ᵐ[betaMeasure (m / 2) (n / 2)] ∅ := by
      filter_upwards [(Ioo_ae_eq_Icc : Ioo (0 : ℝ) 1 =ᵐ[betaMeasure (m / 2) (n / 2)] Icc 0 1),
          ae_mem_Icc_betaMeasure (m / 2) (n / 2)] with u huIoo huIcc
      have hu01 : u ∈ Ioo (0 : ℝ) 1 := by
        rw [huIoo]
        exact huIcc
      have hpos := fisherSnedecorMap_mem_Ioi hm hn hu01
      have hpos' : 0 < fisherSnedecorMap m n u := by
        simpa only [mem_Ioi] using hpos
      simp only [mem_preimage, mem_Iic]
      apply propext
      constructor
      · intro h
        linarith
      · intro h
        simp at h
    rw [measureReal_congr hpre]
    exact measureReal_empty
  · have hx' : 0 < x := lt_of_not_ge hx
    rw [ite_eq_right hx]
    rw [cdf_eq_real, fisherSnedecorMeasure_map hm hn,
      map_measureReal_apply (measurable_fisherSnedecorMap m n) measurableSet_Iic,
      measureReal_congr (fisherSnedecorMap_preimage_Iic_ae hm hn hx')]
    rw [← cdf_eq_real]
    exact cdf_betaMeasure_eq (by linarith) (by linarith) _

end Probability

end TauCeti
