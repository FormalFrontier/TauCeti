/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Density
public import TauCeti.Probability.Distributions.Beta.Cdf
import TauCeti.Analysis.Calculus.RealCharts

/-!
# Fisher's F distribution

## Main definitions

* `fisherSnedecorMeasure` — the Fisher--Snedecor probability measure.
* `fisherSnedecorPDFReal` and `fisherSnedecorPDF` — its real- and extended-nonnegative-valued
  densities.
* `fisherSnedecorMap` — the beta-to-F transformation.
* `fisherSnedecorMapInv` — its inverse on the positive half-line.

## Main results

* `fisherSnedecorMeasure_eq_map` — the beta pushforward characterization.
* `isProbabilityMeasure_fisherSnedecorMeasure_iff` — the exact parameter range for a probability
  measure.
* `fisherSnedecorMap_image_Ioo` — the image of the open unit interval.
* `fisherSnedecorMap_strictMonoOn` — strict monotonicity below one.
* `fisherSnedecorMapInv_map` and `fisherSnedecorMap_mapInv` — the inverse identities.
* `fisherSnedecorMap_div_add` — the beta-to-F image of a ratio-to-sum is the scaled quotient.
* `ae_mem_Ioi_fisherSnedecorMeasure` — positivity almost surely.
* `fisherSnedecorMeasure_eq_withDensity` — the density representation with respect to Lebesgue
  measure.
* `hasPDF_of_hasLaw_fisherSnedecorMeasure` and `rnDeriv_fisherSnedecorMeasure` — the
  random-variable and Radon--Nikodym density interfaces.
* `cdf_fisherSnedecorMeasure_eq` — the closed-form cumulative distribution function.

This file begins the elementary API for Fisher's F law.  For positive degrees of freedom `m` and
`n`, it realizes the law as the image of `betaMeasure (m / 2) (n / 2)` under
`u ↦ (n / m) * u / (1 - u)`.  This gives a probability measure and its cumulative distribution
function without introducing a second probability-law abstraction.  The density is derived from
this pushforward by the same beta-to-F change of variables, rather than being used as a second
definition of the law.

The change of variables is useful in its own right: the inverse map on the positive half-line is
`x ↦ m * x / (n + m * x)`.  The cdf theorem below records this inverse explicitly, in the same
regularized-incomplete-beta convention used by the beta API.

## References

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

/-- The Fisher--Snedecor law with numerator degrees of freedom `m` and denominator degrees of
freedom `n`.  It is the law of `(U / m) / (V / n)` for independent chi-squared variables with
degrees of freedom `m` and `n`; it is the zero measure unless `0 < m` and `0 < n`. -/
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
    let _ : IsProbabilityMeasure (0 : Measure ℝ) := h
    exact (IsProbabilityMeasure.ne_zero (0 : Measure ℝ)) rfl
  · rintro ⟨hm, hn⟩
    exact isProbabilityMeasure_fisherSnedecorMeasure hm hn

/-- The beta-to-F transformation is measurable for all parameter values. -/
@[fun_prop]
theorem measurable_fisherSnedecorMap (m n : ℝ) :
    Measurable (fisherSnedecorMap m n) := by
  unfold fisherSnedecorMap
  fun_prop

/-- The beta-to-F inverse transformation is measurable for all parameter values. -/
@[fun_prop]
theorem measurable_fisherSnedecorMapInv (m n : ℝ) :
    Measurable (fisherSnedecorMapInv m n) := by
  unfold fisherSnedecorMapInv
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

/-- The derivative of the beta-to-F transformation away from its pole at one. -/
theorem hasDerivAt_fisherSnedecorMap (m n : ℝ) {u : ℝ} (hu : u ≠ 1) :
    HasDerivAt (fisherSnedecorMap m n) ((n / m) * ((1 - u) ^ 2)⁻¹) u := by
  have hfun : fisherSnedecorMap m n = fun y ↦ (n / m) * (y / (1 - y)) := by
    funext y
    rw [fisherSnedecorMap_def]
    ring
  rw [hfun]
  exact (hasDerivAt_div_one_sub hu).const_mul (n / m)

/-- If `m ≠ 0`, `n ≠ 0`, and `u ≠ 1`, the inverse transformation after the
beta-to-F map is the identity. -/
@[simp]
theorem fisherSnedecorMapInv_map (hm : m ≠ 0) (hn : n ≠ 0) {u : ℝ}
    (hu : u ≠ 1) :
    fisherSnedecorMapInv m n (fisherSnedecorMap m n u) = u := by
  rw [fisherSnedecorMapInv_def, fisherSnedecorMap_def]
  field_simp [hm, hn, sub_ne_zero.mpr (Ne.symm hu)]
  ring

/-- If `m ≠ 0`, `n ≠ 0`, and `n + m * x ≠ 0`, the beta-to-F map after the
inverse transformation is the identity. -/
@[simp]
theorem fisherSnedecorMap_mapInv (hm : m ≠ 0) (hn : n ≠ 0) {x : ℝ}
    (hden : n + m * x ≠ 0) :
    fisherSnedecorMap m n (fisherSnedecorMapInv m n x) = x := by
  rw [fisherSnedecorMap_def, fisherSnedecorMapInv_def]
  field_simp [hm, hn, hden]
  ring

/-- If `u + v ≠ 0`, the beta-to-F transformation with `m` and `n` degrees of freedom sends the
ratio-to-sum `u / (u + v)` to the variance ratio `(u / m) / (v / n)`; equivalently, it inverts the
passage from a variance ratio to the fraction of the total that its numerator carries. -/
@[simp]
theorem fisherSnedecorMap_div_add {u v : ℝ} (huv : u + v ≠ 0) :
    fisherSnedecorMap m n (u / (u + v)) = u / m / (v / n) := by
  have hsub : 1 - u / (u + v) = v / (u + v) := by
    field_simp
    ring
  rw [fisherSnedecorMap_def, hsub, mul_div_assoc, div_div_div_cancel_right₀ huv]
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
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
  have key := (fisherSnedecorMap_strictMonoOn hm hn).le_iff_le hu.2
    (fisherSnedecorMapInv_mem_Ioo hm hn hx).2
  rw [h_inv] at key
  exact key

/-- The Fisher--Snedecor law is almost surely positive, including vacuously for invalid
parameters. -/
theorem ae_mem_Ioi_fisherSnedecorMeasure (m n : ℝ) :
    ∀ᵐ x ∂fisherSnedecorMeasure m n, x ∈ Ioi 0 := by
  by_cases h : 0 < m ∧ 0 < n
  · rw [fisherSnedecorMeasure_eq_map h.1 h.2, ae_map_iff
      (measurable_fisherSnedecorMap m n).aemeasurable (by measurability)]
    filter_upwards [ae_mem_Ioo_betaMeasure (m / 2) (n / 2)] with u hu
    exact fisherSnedecorMap_mem_Ioi h.1 h.2 hu
  · rw [fisherSnedecorMeasure_of_not_pos h]
    simp

/-! ### Density -/

/-- The real-valued Fisher--Snedecor density with numerator degrees of freedom `m` and
denominator degrees of freedom `n`.

It is zero unless both parameters and the sample point are positive. -/
def fisherSnedecorPDFReal (m n x : ℝ) : ℝ :=
  if 0 < m ∧ 0 < n ∧ 0 < x then
    Real.Gamma ((m + n) / 2) / (Real.Gamma (m / 2) * Real.Gamma (n / 2)) *
      (m / n) ^ (m / 2) * x ^ (m / 2 - 1) *
        (1 + m * x / n) ^ (-((m + n) / 2))
  else 0

/-- The Fisher--Snedecor density, valued in `ℝ≥0∞`. -/
def fisherSnedecorPDF (m n x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (fisherSnedecorPDFReal m n x)

/-- The `ℝ≥0∞`-valued Fisher--Snedecor density is the nonnegative coercion of its real-valued
version. -/
theorem fisherSnedecorPDF_eq_ofReal (m n x : ℝ) :
    fisherSnedecorPDF m n x = ENNReal.ofReal (fisherSnedecorPDFReal m n x) := (rfl)

/-- The real density has its usual formula at valid parameters and a positive point. -/
@[simp]
theorem fisherSnedecorPDFReal_of_pos (hm : 0 < m) (hn : 0 < n) (hx : 0 < x) :
    fisherSnedecorPDFReal m n x =
      Real.Gamma ((m + n) / 2) / (Real.Gamma (m / 2) * Real.Gamma (n / 2)) *
        (m / n) ^ (m / 2) * x ^ (m / 2 - 1) *
          (1 + m * x / n) ^ (-((m + n) / 2)) := by
  simp [fisherSnedecorPDFReal, hm, hn, hx]

/-- The real density vanishes on the nonpositive half-line. -/
@[simp]
theorem fisherSnedecorPDFReal_of_nonpos (hx : x ≤ 0) (m n : ℝ) :
    fisherSnedecorPDFReal m n x = 0 := by
  simp [fisherSnedecorPDFReal, not_lt.mpr hx]

/-- The real density vanishes unless both degrees of freedom are positive. -/
@[simp]
theorem fisherSnedecorPDFReal_of_not_pos (h : ¬ (0 < m ∧ 0 < n)) (x : ℝ) :
    fisherSnedecorPDFReal m n x = 0 := by
  rw [fisherSnedecorPDFReal, ite_eq_right]
  exact fun hx ↦ h ⟨hx.1, hx.2.1⟩

/-- The `ℝ≥0∞`-valued density has its usual formula at valid parameters and a positive
point. -/
@[simp]
theorem fisherSnedecorPDF_of_pos (hm : 0 < m) (hn : 0 < n) (hx : 0 < x) :
    fisherSnedecorPDF m n x = ENNReal.ofReal
      (Real.Gamma ((m + n) / 2) / (Real.Gamma (m / 2) * Real.Gamma (n / 2)) *
        (m / n) ^ (m / 2) * x ^ (m / 2 - 1) *
          (1 + m * x / n) ^ (-((m + n) / 2))) := by
  rw [fisherSnedecorPDF, fisherSnedecorPDFReal_of_pos hm hn hx]

/-- The `ℝ≥0∞`-valued density vanishes on the nonpositive half-line. -/
@[simp]
theorem fisherSnedecorPDF_of_nonpos (hx : x ≤ 0) (m n : ℝ) :
    fisherSnedecorPDF m n x = 0 := by
  rw [fisherSnedecorPDF, fisherSnedecorPDFReal_of_nonpos hx, ENNReal.ofReal_zero]

/-- The `ℝ≥0∞`-valued density vanishes unless both degrees of freedom are positive. -/
@[simp]
theorem fisherSnedecorPDF_of_not_pos (h : ¬ (0 < m ∧ 0 < n)) (x : ℝ) :
    fisherSnedecorPDF m n x = 0 := by
  rw [fisherSnedecorPDF, fisherSnedecorPDFReal_of_not_pos h, ENNReal.ofReal_zero]

/-- The real-valued Fisher--Snedecor density is nonnegative. -/
theorem fisherSnedecorPDFReal_nonneg (m n x : ℝ) : 0 ≤ fisherSnedecorPDFReal m n x := by
  rw [fisherSnedecorPDFReal]
  split_ifs with h
  · have hm2 : 0 < m / 2 := by linarith [h.1]
    have hn2 : 0 < n / 2 := by linarith [h.2.1]
    have hmn2 : 0 < (m + n) / 2 := by linarith [h.1, h.2.1]
    have hbase : 0 < 1 + m * x / n := by
      have : 0 < m * x / n := div_pos (mul_pos h.1 h.2.2) h.2.1
      linarith
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (div_nonneg (Real.Gamma_pos_of_pos hmn2).le
            (mul_nonneg (Real.Gamma_pos_of_pos hm2).le (Real.Gamma_pos_of_pos hn2).le))
          (Real.rpow_nonneg (div_nonneg h.1.le h.2.1.le) _))
        (Real.rpow_nonneg h.2.2.le _))
      (Real.rpow_nonneg hbase.le _)
  · exact le_rfl

/-- Converting the Fisher--Snedecor density back to `ℝ` recovers its real-valued version. -/
@[simp]
theorem toReal_fisherSnedecorPDF (m n x : ℝ) :
    (fisherSnedecorPDF m n x).toReal = fisherSnedecorPDFReal m n x :=
  ENNReal.toReal_ofReal (fisherSnedecorPDFReal_nonneg m n x)

/-- The real Fisher--Snedecor density is measurable in the sample point. -/
@[fun_prop]
theorem measurable_fisherSnedecorPDFReal (m n : ℝ) :
    Measurable (fisherSnedecorPDFReal m n) := by
  by_cases hvalid : 0 < m ∧ 0 < n
  · have heq : fisherSnedecorPDFReal m n = fun x ↦ if 0 < x then
        Real.Gamma ((m + n) / 2) / (Real.Gamma (m / 2) * Real.Gamma (n / 2)) *
          Real.exp (Real.log (m / n) * (m / 2)) *
            Real.exp (Real.log x * (m / 2 - 1)) *
              Real.exp (Real.log (1 + m * x / n) * (-((m + n) / 2))) else 0 := by
      funext x
      by_cases hx : 0 < x
      · have hbase : 0 < 1 + m * x / n := by
          have : 0 < m * x / n := div_pos (mul_pos hvalid.1 hx) hvalid.2
          linarith
        rw [fisherSnedecorPDFReal_of_pos hvalid.1 hvalid.2 hx, ite_eq_left hx,
          Real.rpow_def_of_pos (div_pos hvalid.1 hvalid.2), Real.rpow_def_of_pos hx,
          Real.rpow_def_of_pos hbase]
      · rw [fisherSnedecorPDFReal_of_nonpos (not_lt.mp hx), ite_eq_right hx]
    rw [heq]
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id) (by fun_prop)
      measurable_const
  · have heq : fisherSnedecorPDFReal m n = 0 := by
      funext x
      rw [fisherSnedecorPDFReal_of_not_pos hvalid]
      rfl
    rw [heq]
    fun_prop

/-- The `ℝ≥0∞`-valued Fisher--Snedecor density is measurable in the sample point. -/
@[fun_prop]
theorem measurable_fisherSnedecorPDF (m n : ℝ) : Measurable (fisherSnedecorPDF m n) :=
  (measurable_fisherSnedecorPDFReal m n).ennreal_ofReal

/-- The Fisher--Snedecor density is supported on the positive half-line. -/
theorem indicator_Ioi_fisherSnedecorPDF (m n : ℝ) :
    (Ioi (0 : ℝ)).indicator (fisherSnedecorPDF m n) = fisherSnedecorPDF m n := by
  ext x
  rcases le_or_gt x 0 with hx | hx
  · simp [hx]
  · simp [hx]

/-- The classical Fisher density in the scaled beta-prime form used by its change of variables. -/
theorem fisherSnedecorPDFReal_eq_scaled_beta (hm : 0 < m) (hn : 0 < n) (hx : 0 < x) :
    fisherSnedecorPDFReal m n x =
      (m / n) * (1 / beta (m / 2) (n / 2)) * (m * x / n) ^ (m / 2 - 1) *
        (1 + m * x / n) ^ (-((m + n) / 2)) := by
  rw [fisherSnedecorPDFReal_of_pos hm hn hx]
  have hmn : 0 < m / n := div_pos hm hn
  have hscale : m * x / n = (m / n) * x := by ring
  rw [hscale, Real.mul_rpow hmn.le hx.le]
  have hpow : (m / n) * (m / n) ^ (m / 2 - 1) = (m / n) ^ (m / 2) := by
    calc
      (m / n) * (m / n) ^ (m / 2 - 1) =
          (m / n) ^ (1 : ℝ) * (m / n) ^ (m / 2 - 1) := by rw [Real.rpow_one]
      _ = (m / n) ^ ((1 : ℝ) + (m / 2 - 1)) := by rw [Real.rpow_add hmn]
      _ = (m / n) ^ (m / 2) := by ring_nf
  rw [ProbabilityTheory.beta]
  have hsum : m / 2 + n / 2 = (m + n) / 2 := by ring
  rw [hsum, ← hpow]
  field_simp [(Real.Gamma_pos_of_pos (by linarith : 0 < m / 2)).ne',
    (Real.Gamma_pos_of_pos (by linarith : 0 < n / 2)).ne',
    (Real.Gamma_pos_of_pos (by linarith : 0 < (m + n) / 2)).ne']

/-- The density identity for the beta-to-F change of variables. -/
private theorem abs_deriv_mul_fisherSnedecorPDFReal (hm : 0 < m) (hn : 0 < n)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    |(n / m) * ((1 - u) ^ 2)⁻¹| *
        fisherSnedecorPDFReal m n (fisherSnedecorMap m n u) =
      betaPDFReal (m / 2) (n / 2) u := by
  have h1u : 0 < 1 - u := by linarith [hu.2]
  have hx : 0 < fisherSnedecorMap m n u := fisherSnedecorMap_mem_Ioi hm hn hu
  have hderiv : 0 < (n / m) * ((1 - u) ^ 2)⁻¹ :=
    mul_pos (div_pos hn hm) (inv_pos.mpr (sq_pos_of_pos h1u))
  rw [abs_of_pos hderiv, fisherSnedecorPDFReal_eq_scaled_beta hm hn hx,
    betaPDFReal, ite_eq_left ⟨hu.1, hu.2⟩]
  have hscale : m * fisherSnedecorMap m n u / n = u / (1 - u) := by
    rw [fisherSnedecorMap_def]
    field_simp [hm.ne', hn.ne', h1u.ne']
  rw [hscale]
  have hsum : m / 2 + n / 2 = (m + n) / 2 := by ring
  rw [← hsum]
  have hchart := abs_deriv_smul_one_add_rpow (m / 2) (n / 2) hu
  simp only [smul_eq_mul, abs_of_pos (inv_pos.mpr (sq_pos_of_pos h1u))] at hchart
  calc
    (n / m) * ((1 - u) ^ 2)⁻¹ *
          ((m / n) * (1 / beta (m / 2) (n / 2)) *
            (u / (1 - u)) ^ (m / 2 - 1) *
              (1 + u / (1 - u)) ^ (-(m / 2 + n / 2))) =
        (1 / beta (m / 2) (n / 2)) *
          (((1 - u) ^ 2)⁻¹ * ((u / (1 - u)) ^ (m / 2 - 1) *
              (1 + u / (1 - u)) ^ (-(m / 2 + n / 2)))) := by
      field_simp [hm.ne', hn.ne']
    _ = (1 / beta (m / 2) (n / 2)) *
        (u ^ (m / 2 - 1) * (1 - u) ^ (n / 2 - 1)) := by rw [hchart]
    _ = (1 / beta (m / 2) (n / 2)) * u ^ (m / 2 - 1) *
        (1 - u) ^ (n / 2 - 1) := by ring

/-- The extended-nonnegative density identity used in the beta-to-F Jacobian formula. -/
private theorem ofReal_abs_deriv_mul_fisherSnedecorPDF (hm : 0 < m) (hn : 0 < n)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    ENNReal.ofReal |(n / m) * ((1 - u) ^ 2)⁻¹| *
        fisherSnedecorPDF m n (fisherSnedecorMap m n u) =
      betaPDF (m / 2) (n / 2) u := by
  rw [fisherSnedecorPDF, betaPDF, ← ENNReal.ofReal_mul (abs_nonneg _),
    abs_deriv_mul_fisherSnedecorPDFReal hm hn hu]

/-- **The density of the Fisher--Snedecor law**, including the zero density at invalid
parameters. -/
theorem fisherSnedecorMeasure_eq_withDensity (m n : ℝ) :
    fisherSnedecorMeasure m n = volume.withDensity (fisherSnedecorPDF m n) := by
  by_cases h : 0 < m ∧ 0 < n
  · obtain ⟨hm, hn⟩ := h
    ext s hs
    let u : Set ℝ := Ioo 0 1 ∩ fisherSnedecorMap m n ⁻¹' s
    have hu : MeasurableSet u := measurableSet_Ioo.inter (measurable_fisherSnedecorMap m n hs)
    have himage : fisherSnedecorMap m n '' u = Ioi 0 ∩ s := by
      simp only [u, image_inter_preimage, fisherSnedecorMap_image_Ioo hm hn]
    have hindicator :
        (Ioo (0 : ℝ) 1).indicator (betaPDF (m / 2) (n / 2)) =
          betaPDF (m / 2) (n / 2) := by
      ext z
      by_cases hz : z ∈ Ioo (0 : ℝ) 1
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz]
        simp only [mem_Ioo, not_and_or] at hz
        rcases hz with hz | hz
        · exact (betaPDF_eq_zero_of_nonpos (not_lt.mp hz)).symm
        · exact (betaPDF_eq_zero_of_one_le (not_lt.mp hz)).symm
    calc
      fisherSnedecorMeasure m n s =
          ∫⁻ z in fisherSnedecorMap m n ⁻¹' s, betaPDF (m / 2) (n / 2) z := by
            rw [fisherSnedecorMeasure_eq_map hm hn,
              Measure.map_apply (measurable_fisherSnedecorMap m n) hs, betaMeasure,
              withDensity_apply _ (measurable_fisherSnedecorMap m n hs)]
      _ = ∫⁻ z in u, betaPDF (m / 2) (n / 2) z := by
            calc
              ∫⁻ z in fisherSnedecorMap m n ⁻¹' s, betaPDF (m / 2) (n / 2) z =
                  ∫⁻ z in fisherSnedecorMap m n ⁻¹' s,
                    (Ioo 0 1).indicator (betaPDF (m / 2) (n / 2)) z := by rw [hindicator]
              _ = ∫⁻ z in u, betaPDF (m / 2) (n / 2) z := by
                    rw [setLIntegral_indicator measurableSet_Ioo]
      _ = ∫⁻ z in u,
            ENNReal.ofReal |(n / m) * ((1 - z) ^ 2)⁻¹| *
              fisherSnedecorPDF m n (fisherSnedecorMap m n z) := by
            refine setLIntegral_congr_fun hu fun z hz ↦ ?_
            exact (ofReal_abs_deriv_mul_fisherSnedecorPDF hm hn hz.1).symm
      _ = ∫⁻ y in Ioi 0 ∩ s, fisherSnedecorPDF m n y := by
            rw [← himage]
            exact (lintegral_image_eq_lintegral_abs_deriv_mul hu
              (fun z hz ↦ (hasDerivAt_fisherSnedecorMap m n (ne_of_lt hz.1.2)).hasDerivWithinAt)
              ((fisherSnedecorMap_strictMonoOn hm hn).injOn.mono fun _ hz ↦ hz.1.2)
              (fisherSnedecorPDF m n)).symm
      _ = volume.withDensity (fisherSnedecorPDF m n) s := by
            rw [withDensity_apply _ hs, ← setLIntegral_indicator measurableSet_Ioi,
              indicator_Ioi_fisherSnedecorPDF]
  · rw [fisherSnedecorMeasure_of_not_pos h]
    ext s hs
    simp [withDensity_apply, hs, fisherSnedecorPDF_of_not_pos h]

section DensityCorollaries

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with a Fisher--Snedecor law has the corresponding density. -/
theorem hasPDF_of_hasLaw_fisherSnedecorMeasure
    (hX : HasLaw X (fisherSnedecorMeasure m n) P) : HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_fisherSnedecorPDF m n).aemeasurable
    (by rwa [fisherSnedecorMeasure_eq_withDensity m n] at hX)

/-- The density of a random variable with a Fisher--Snedecor law is `fisherSnedecorPDF`. -/
theorem pdf_eq_fisherSnedecorPDF_of_hasLaw_fisherSnedecorMeasure
    (hX : HasLaw X (fisherSnedecorMeasure m n) P) :
    pdf X P volume =ᵐ[volume] fisherSnedecorPDF m n :=
  pdf_eq_of_hasLaw_withDensity (measurable_fisherSnedecorPDF m n).aemeasurable
    (by rwa [fisherSnedecorMeasure_eq_withDensity m n] at hX)

end DensityCorollaries

/-- The Radon--Nikodym derivative of a Fisher--Snedecor law against Lebesgue measure. -/
theorem rnDeriv_fisherSnedecorMeasure (m n : ℝ) :
    (fisherSnedecorMeasure m n).rnDeriv volume =ᵐ[volume] fisherSnedecorPDF m n := by
  rw [fisherSnedecorMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity volume (measurable_fisherSnedecorPDF m n)

/-! ### The cdf -/

/-- For positive degrees of freedom, the cdf is `0` when `x ≤ 0` and is the regularized
incomplete beta function at `m * x / (n + m * x)` when `0 < x`. -/
theorem cdf_fisherSnedecorMeasure_eq (hm : 0 < m) (hn : 0 < n) (x : ℝ) :
  cdf (fisherSnedecorMeasure m n) x =
      if x ≤ 0 then 0 else
      regularizedIncompleteBeta (m / 2) (n / 2) (m * x / (n + m * x)) := by
  let _ : IsProbabilityMeasure (fisherSnedecorMeasure m n) :=
    isProbabilityMeasure_fisherSnedecorMeasure hm hn
  let _ : IsProbabilityMeasure (betaMeasure (m / 2) (n / 2)) :=
    isProbabilityMeasureBeta (by linarith) (by linarith)
  by_cases hx : x ≤ 0
  · rw [ite_eq_left hx]
    rw [cdf_eq_real]
    have hpre : (Iic x : Set ℝ) =ᵐ[fisherSnedecorMeasure m n] ∅ := by
      filter_upwards [ae_mem_Ioi_fisherSnedecorMeasure m n] with y hy
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
    simpa only [fisherSnedecorMapInv_def] using
      cdf_betaMeasure_eq (by linarith) (by linarith) _

end Probability

end TauCeti
