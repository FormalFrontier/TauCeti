/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Density
public import TauCeti.Probability.Distributions.Gamma.Cdf
public import TauCeti.Probability.Distributions.Measurability
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The inverse-gamma distribution

The inverse-gamma law with shape `a` and scale `r` is the law of `X⁻¹` for
`X ∼ gammaMeasure a r`, where `r` is the rate of the Gamma law.  This file defines that pushforward
for positive parameters and uses the zero measure otherwise.  It derives the density

`r ^ a / Gamma a * x ^ (-a - 1) * exp (-r / x)`

on the positive half-line, computes the cdf and the natural moments below the shape threshold,
and obtains the mean and variance together with the matching integrability thresholds.  It also
shows that nonpositive exponential moments exist while every positive exponential moment diverges.

The density is derived from the pushforward definition.  On `(0, ∞)`, inversion is an involution
with absolute derivative `x⁻²`; Mathlib's one-dimensional Jacobian formula transports the Gamma
density through this map.  The moment calculations reduce to Euler's Gamma integral after
composing a power with inversion.

## Main declarations

* `TauCeti.Probability.inverseGammaMeasure`, `inverseGammaPDFReal`, and `inverseGammaPDF` define
  the law and its density;
* `inverseGammaMeasure_eq_withDensity`, `hasPDF_of_hasLaw_inverseGammaMeasure`, and
  `rnDeriv_inverseGammaMeasure` identify the density;
* `cdf_inverseGammaMeasure_eq` computes the cdf as an upper regularized Gamma value;
* `integral_pow_inverseGammaMeasure`, `integral_id_inverseGammaMeasure`, and
  `variance_id_inverseGammaMeasure` compute the moments that exist;
* `integrableExpSet_id_inverseGammaMeasure` gives the exact exponential-integrability domain;
* `measurable_inverseGammaMeasure` makes the parameterized family available to kernels.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), chapter on inverse-gamma distributions.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal Topology

namespace TauCeti

namespace Probability

variable {a r x t : ℝ}

/-! ### Definition and boundary behavior -/

/-- The inverse-gamma law with shape `a` and scale `r`.

For positive parameters it is the pushforward of `gammaMeasure a r` by inversion, where `r` is the
rate of the Gamma law.  It is the zero measure if either parameter is nonpositive. -/
def inverseGammaMeasure (a r : ℝ) : Measure ℝ :=
  if 0 < a ∧ 0 < r then (gammaMeasure a r).map Inv.inv else 0

/-- At positive parameters the inverse-gamma law is the inversion pushforward of the Gamma law.

This is not a `simp` lemma: `inverseGammaMeasure a r` is the simp-normal form, and unfolding it
would shadow every `simp` lemma stated about the law at positive parameters. -/
theorem inverseGammaMeasure_of_pos (ha : 0 < a) (hr : 0 < r) :
    inverseGammaMeasure a r = (gammaMeasure a r).map Inv.inv := by
  rw [inverseGammaMeasure, ite_eq_left ⟨ha, hr⟩]

/-- If the shape or scale is nonpositive, the inverse-gamma law is the zero measure. -/
@[simp]
theorem inverseGammaMeasure_of_not_pos (h : ¬ (0 < a ∧ 0 < r)) :
    inverseGammaMeasure a r = 0 := by
  rw [inverseGammaMeasure, ite_eq_right h]

/-- A valid inverse-gamma law is a probability measure. -/
theorem isProbabilityMeasure_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) :
    IsProbabilityMeasure (inverseGammaMeasure a r) := by
  rw [inverseGammaMeasure_of_pos ha hr]
  let _ := isProbabilityMeasure_gammaMeasure ha hr
  infer_instance

/-- The inverse-gamma law assigns no mass to the nonpositive half-line. -/
@[simp]
theorem inverseGammaMeasure_Iic_zero (a r : ℝ) : inverseGammaMeasure a r (Iic 0) = 0 := by
  by_cases h : 0 < a ∧ 0 < r
  · rw [inverseGammaMeasure_of_pos h.1 h.2,
      Measure.map_apply measurable_inv measurableSet_Iic]
    have hpre : Inv.inv ⁻¹' Iic (0 : ℝ) = Iic 0 := by
      ext y
      simp only [mem_preimage, mem_Iic]
      exact inv_nonpos
    have hzero : gammaMeasure a r (Iic 0) = 0 := by
      let _ := isProbabilityMeasure_gammaMeasure h.1 h.2
      rw [← measureReal_eq_zero_iff, measureReal_Iic_gammaMeasure h.1 h.2,
        mul_zero, regularizedGamma_eq_zero_of_nonpos_right a le_rfl]
    rw [hpre, hzero]
  · simp [inverseGammaMeasure_of_not_pos h]

/-- An inverse-gamma law is concentrated on the positive half-line, including in the zero-measure
invalid-parameter cases. -/
theorem ae_pos_inverseGammaMeasure (a r : ℝ) : ∀ᵐ x ∂inverseGammaMeasure a r, 0 < x := by
  rw [ae_iff]
  simpa only [not_lt, ← Iic_def] using inverseGammaMeasure_Iic_zero a r

/-! ### Density -/

/-- The real-valued inverse-gamma density.  It vanishes unless both parameters and the sample
point are positive. -/
def inverseGammaPDFReal (a r x : ℝ) : ℝ :=
  if 0 < a ∧ 0 < r ∧ 0 < x then
    r ^ a / Real.Gamma a * x ^ (-a - 1) * Real.exp (-r / x)
  else 0

/-- The inverse-gamma density, valued in `ℝ≥0∞`. -/
def inverseGammaPDF (a r x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (inverseGammaPDFReal a r x)

/-- The `ℝ≥0∞`-valued inverse-gamma density is the coercion of the real-valued one. -/
theorem inverseGammaPDF_eq_ofReal (a r x : ℝ) :
    inverseGammaPDF a r x = ENNReal.ofReal (inverseGammaPDFReal a r x) := by
  rw [inverseGammaPDF]

/-- The real density has its usual formula at valid parameters and a positive point. -/
@[simp]
theorem inverseGammaPDFReal_of_pos (ha : 0 < a) (hr : 0 < r) (hx : 0 < x) :
    inverseGammaPDFReal a r x =
      r ^ a / Real.Gamma a * x ^ (-a - 1) * Real.exp (-r / x) := by
  simp [inverseGammaPDFReal, ha, hr, hx]

/-- The inverse-gamma density vanishes at a nonpositive point. -/
@[simp]
theorem inverseGammaPDFReal_of_nonpos (hx : x ≤ 0) (a r : ℝ) :
    inverseGammaPDFReal a r x = 0 := by
  simp [inverseGammaPDFReal, not_lt.mpr hx]

/-- The inverse-gamma density vanishes when its parameters are invalid. -/
@[simp]
theorem inverseGammaPDFReal_of_not_pos (h : ¬ (0 < a ∧ 0 < r)) (x : ℝ) :
    inverseGammaPDFReal a r x = 0 := by
  rw [inverseGammaPDFReal, ite_eq_right]
  exact fun hx ↦ h ⟨hx.1, hx.2.1⟩

/-- The inverse-gamma density has its usual formula at valid parameters and a positive point. -/
@[simp]
theorem inverseGammaPDF_of_pos (ha : 0 < a) (hr : 0 < r) (hx : 0 < x) :
    inverseGammaPDF a r x =
      ENNReal.ofReal (r ^ a / Real.Gamma a * x ^ (-a - 1) * Real.exp (-r / x)) := by
  rw [inverseGammaPDF, inverseGammaPDFReal_of_pos ha hr hx]

/-- The inverse-gamma density vanishes at a nonpositive point. -/
@[simp]
theorem inverseGammaPDF_of_nonpos (hx : x ≤ 0) (a r : ℝ) : inverseGammaPDF a r x = 0 := by
  rw [inverseGammaPDF, inverseGammaPDFReal_of_nonpos hx, ENNReal.ofReal_zero]

/-- The inverse-gamma density vanishes when its parameters are invalid. -/
@[simp]
theorem inverseGammaPDF_of_not_pos (h : ¬ (0 < a ∧ 0 < r)) (x : ℝ) :
    inverseGammaPDF a r x = 0 := by
  rw [inverseGammaPDF, inverseGammaPDFReal_of_not_pos h, ENNReal.ofReal_zero]

/-- The real-valued inverse-gamma density is nonnegative. -/
theorem inverseGammaPDFReal_nonneg (a r x : ℝ) : 0 ≤ inverseGammaPDFReal a r x := by
  rw [inverseGammaPDFReal]
  split_ifs with h
  · exact mul_nonneg
      (mul_nonneg (div_nonneg (Real.rpow_nonneg h.2.1.le _)
        (Real.Gamma_pos_of_pos h.1).le) (Real.rpow_nonneg h.2.2.le _))
      (Real.exp_pos _).le
  · exact le_rfl

/-- Converting the inverse-gamma density back to `ℝ` recovers its real-valued version. -/
@[simp]
theorem toReal_inverseGammaPDF (a r x : ℝ) :
    (inverseGammaPDF a r x).toReal = inverseGammaPDFReal a r x := by
  rw [inverseGammaPDF, ENNReal.toReal_ofReal (inverseGammaPDFReal_nonneg a r x)]

/-- The real inverse-gamma density is measurable in the sample point. -/
@[fun_prop]
theorem measurable_inverseGammaPDFReal (a r : ℝ) : Measurable (inverseGammaPDFReal a r) := by
  by_cases hvalid : 0 < a ∧ 0 < r
  · have heq : inverseGammaPDFReal a r = fun x ↦
        if 0 < x then r ^ a / Real.Gamma a * x ^ (-a - 1) * Real.exp (-r / x) else 0 := by
      funext x
      by_cases hx : 0 < x
      · simp [inverseGammaPDFReal, hvalid, hx]
      · simp [inverseGammaPDFReal, hvalid, hx]
    rw [heq]
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id) (by fun_prop)
      measurable_const
  · have heq : inverseGammaPDFReal a r = 0 := by
      funext x
      rw [inverseGammaPDFReal_of_not_pos hvalid]
      rfl
    rw [heq]
    fun_prop

/-- The `ℝ≥0∞`-valued inverse-gamma density is measurable in the sample point. -/
@[fun_prop]
theorem measurable_inverseGammaPDF (a r : ℝ) : Measurable (inverseGammaPDF a r) :=
  (measurable_inverseGammaPDFReal a r).ennreal_ofReal

/-- The inverse-gamma density is supported on the positive half-line. -/
theorem indicator_Ioi_inverseGammaPDF (a r : ℝ) :
    (Ioi (0 : ℝ)).indicator (inverseGammaPDF a r) = inverseGammaPDF a r := by
  ext y
  rcases le_or_gt y 0 with hy | hy
  · simp [hy, inverseGammaPDF]
  · simp [hy]

/-- The inverse-gamma density is the Gamma density at the inverse point multiplied by the
absolute Jacobian `x⁻²`. -/
theorem inverseGammaPDFReal_eq_inv_sq_mul_gammaPDFReal
    (ha : 0 < a) (hr : 0 < r) (hx : 0 < x) :
    inverseGammaPDFReal a r x = (x ^ 2)⁻¹ * gammaPDFReal a r x⁻¹ := by
  rw [inverseGammaPDFReal_of_pos ha hr hx, gammaPDFReal,
    ite_eq_left (inv_nonneg.mpr hx.le)]
  have hpow : x⁻¹ ^ (a - 1) = x ^ (1 - a) := by
    calc
      x⁻¹ ^ (a - 1) = (x ^ (a - 1))⁻¹ := Real.inv_rpow hx.le _
      _ = x ^ (-(a - 1)) := (Real.rpow_neg hx.le _).symm
      _ = x ^ (1 - a) := by congr 1; ring
  rw [hpow]
  have hcombine : (x ^ 2)⁻¹ * x ^ (1 - a) = x ^ (-a - 1) := by
    rw [← Real.rpow_natCast x 2, ← Real.rpow_neg hx.le, ← Real.rpow_add hx]
    congr 1
    ring
  rw [← hcombine]
  simp only [div_eq_mul_inv]
  ring_nf

/-- The Jacobian identity used to transport the Gamma density through inversion. -/
private lemma ofReal_abs_inv_deriv_mul_inverseGammaPDF
    (ha : 0 < a) (hr : 0 < r) (hx : 0 < x) :
    ENNReal.ofReal (abs (-((x ^ 2)⁻¹))) * inverseGammaPDF a r x⁻¹ = gammaPDF a r x := by
  calc
    ENNReal.ofReal (abs (-((x ^ 2)⁻¹))) * inverseGammaPDF a r x⁻¹ =
        ENNReal.ofReal ((x ^ 2)⁻¹ * inverseGammaPDFReal a r x⁻¹) := by
      rw [abs_neg, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hx)), inverseGammaPDF,
        ENNReal.ofReal_mul (inv_nonneg.mpr (sq_nonneg x))]
    _ = ENNReal.ofReal
        ((x ^ 2)⁻¹ * (((x⁻¹) ^ 2)⁻¹ * gammaPDFReal a r x)) := by
      rw [inverseGammaPDFReal_eq_inv_sq_mul_gammaPDFReal ha hr (inv_pos.mpr hx), inv_inv]
    _ = ENNReal.ofReal (gammaPDFReal a r x) := by
      simp only [inv_pow, inv_inv, ← mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero 2 hx.ne'), one_mul]
    _ = gammaPDF a r x := by rw [gammaPDF]

/-- **The density of an inverse-gamma law**, including the zero density at invalid parameters. -/
theorem inverseGammaMeasure_eq_withDensity (a r : ℝ) :
    inverseGammaMeasure a r = volume.withDensity (inverseGammaPDF a r) := by
  by_cases h : 0 < a ∧ 0 < r
  · obtain ⟨ha, hr⟩ := h
    ext s hs
    let u : Set ℝ := Ioi 0 ∩ Inv.inv ⁻¹' s
    have hu : MeasurableSet u := measurableSet_Ioi.inter (measurable_inv hs)
    have himage : Inv.inv '' u = Ioi 0 ∩ s := by
      apply Set.Subset.antisymm
      · rintro _ ⟨z, hz, rfl⟩
        have hzpos : 0 < z := hz.1
        refine ⟨by simpa using inv_pos.mpr hzpos, by simpa using hz.2⟩
      · intro y hy
        have hypos : 0 < y := hy.1
        refine ⟨y⁻¹, ?_, inv_inv y⟩
        exact ⟨by simpa using inv_pos.mpr hypos, by simpa using hy.2⟩
    calc
      inverseGammaMeasure a r s
          = ∫⁻ y in Inv.inv ⁻¹' s, gammaPDF a r y := by
              rw [inverseGammaMeasure_of_pos ha hr, Measure.map_apply measurable_inv hs,
                gammaMeasure, withDensity_apply _ (measurable_inv hs)]
      _ = ∫⁻ y in u, gammaPDF a r y := by
            have hpre : MeasurableSet (Inv.inv ⁻¹' s) := measurable_inv hs
            calc
              ∫⁻ y in Inv.inv ⁻¹' s, gammaPDF a r y =
                  ∫⁻ y in Inv.inv ⁻¹' s, (Ioi 0).indicator (gammaPDF a r) y := by
                apply setLIntegral_congr_fun_ae hpre
                filter_upwards [volume.ae_ne (0 : ℝ)] with y hy _
                rcases lt_or_gt_of_ne hy with hy | hy
                · have hymem : y ∉ Ioi (0 : ℝ) := by simpa using not_lt.mpr hy.le
                  rw [gammaPDF_of_neg hy, indicator_apply, ite_eq_right hymem]
                · have hymem : y ∈ Ioi (0 : ℝ) := hy
                  rw [indicator_apply, ite_eq_left hymem]
              _ = ∫⁻ y in u, gammaPDF a r y := by
                rw [setLIntegral_indicator measurableSet_Ioi]
      _ = ∫⁻ y in u,
            ENNReal.ofReal (abs (-((y ^ 2)⁻¹))) * inverseGammaPDF a r y⁻¹ := by
            refine setLIntegral_congr_fun hu fun y hy ↦ ?_
            exact (ofReal_abs_inv_deriv_mul_inverseGammaPDF ha hr hy.1).symm
      _ = ∫⁻ y in Ioi 0 ∩ s, inverseGammaPDF a r y := by
            rw [← himage]
            exact (lintegral_image_eq_lintegral_abs_deriv_mul
              (f := Inv.inv) (f' := fun y : ℝ ↦ -((y ^ 2)⁻¹)) hu
              (fun y hy ↦ (hasDerivAt_inv hy.1.ne').hasDerivWithinAt)
              (MeasurableEquiv.inv ℝ).injective.injOn (inverseGammaPDF a r)).symm
      _ = volume.withDensity (inverseGammaPDF a r) s := by
            rw [withDensity_apply _ hs, ← setLIntegral_indicator measurableSet_Ioi,
              indicator_Ioi_inverseGammaPDF]
  · rw [inverseGammaMeasure_of_not_pos h]
    ext s hs
    simp [withDensity_apply, hs, inverseGammaPDF_of_not_pos h]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with an inverse-gamma law has a density. -/
theorem hasPDF_of_hasLaw_inverseGammaMeasure
    (hX : HasLaw X (inverseGammaMeasure a r) P) : HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_inverseGammaPDF a r).aemeasurable
    (by rwa [inverseGammaMeasure_eq_withDensity a r] at hX)

/-- The density of a random variable with an inverse-gamma law is `inverseGammaPDF`. -/
theorem pdf_eq_inverseGammaPDF_of_hasLaw_inverseGammaMeasure
    (hX : HasLaw X (inverseGammaMeasure a r) P) :
    pdf X P volume =ᵐ[volume] inverseGammaPDF a r :=
  pdf_eq_of_hasLaw_withDensity (measurable_inverseGammaPDF a r).aemeasurable
    (by rwa [inverseGammaMeasure_eq_withDensity a r] at hX)

/-- The Radon–Nikodym derivative of an inverse-gamma law against Lebesgue measure. -/
theorem rnDeriv_inverseGammaMeasure (a r : ℝ) :
    (inverseGammaMeasure a r).rnDeriv volume =ᵐ[volume] inverseGammaPDF a r := by
  rw [inverseGammaMeasure_eq_withDensity a r]
  exact Measure.rnDeriv_withDensity volume (measurable_inverseGammaPDF a r)

/-! ### Moments -/

/-- A natural power is integrable under a valid inverse-gamma law exactly below the shape. -/
@[simp]
theorem integrable_pow_inverseGammaMeasure_iff (ha : 0 < a) (hr : 0 < r) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (inverseGammaMeasure a r) ↔ (n : ℝ) < a := by
  rw [inverseGammaMeasure_of_pos ha hr,
    integrable_map_measure (by fun_prop) measurable_inv.aemeasurable]
  simpa only [Function.comp_def, inv_pow] using
    TauCeti.integrable_inv_pow_gammaMeasure_iff ha hr n

/-- **Natural moments of a valid inverse-gamma law.**  The `n`th moment exists for `n < a` and
equals `r ^ n * Gamma (a - n) / Gamma a`. -/
@[simp]
theorem integral_pow_inverseGammaMeasure (hr : 0 < r) (n : ℕ)
    (hn : (n : ℝ) < a) :
    ∫ x, x ^ n ∂inverseGammaMeasure a r =
      r ^ n * Real.Gamma (a - n) / Real.Gamma a := by
  have ha : 0 < a := lt_of_le_of_lt (Nat.cast_nonneg n) hn
  rw [inverseGammaMeasure_of_pos ha hr,
    integral_map measurable_inv.aemeasurable (by fun_prop)]
  simpa only [inv_pow] using TauCeti.integral_inv_pow_gammaMeasure hr n hn

/-- The mean of an inverse-gamma law is `r / (a - 1)` when `1 < a`. -/
@[simp]
theorem integral_id_inverseGammaMeasure (hr : 0 < r) (ha : 1 < a) :
    ∫ x, x ∂inverseGammaMeasure a r = r / (a - 1) := by
  have h := integral_pow_inverseGammaMeasure hr 1 (by simpa using ha)
  have hgamma : Real.Gamma a = (a - 1) * Real.Gamma (a - 1) := by
    simpa using Real.Gamma_add_one (by linarith : a - 1 ≠ 0)
  simp only [pow_one, Nat.cast_one] at h
  rw [h, hgamma]
  field_simp [(Real.Gamma_pos_of_pos (by linarith : 0 < a - 1)).ne']

/-- The second raw moment of an inverse-gamma law is
`r² / ((a - 1) * (a - 2))` when `2 < a`. -/
@[simp high]
theorem integral_sq_inverseGammaMeasure (hr : 0 < r) (ha : 2 < a) :
    ∫ x, x ^ 2 ∂inverseGammaMeasure a r = r ^ 2 / ((a - 1) * (a - 2)) := by
  have h := integral_pow_inverseGammaMeasure hr 2 (by simpa using ha)
  have hgamma : Real.Gamma a = (a - 1) * Real.Gamma (a - 1) := by
    simpa using Real.Gamma_add_one (by linarith : a - 1 ≠ 0)
  have hshift : a - 2 + 1 = a - 1 := by ring
  have hgamma' : Real.Gamma (a - 1) = (a - 2) * Real.Gamma (a - 2) := by
    simpa [hshift] using Real.Gamma_add_one (by linarith : a - 2 ≠ 0)
  norm_num only [Nat.cast_ofNat] at h
  rw [h, hgamma, hgamma']
  field_simp [(Real.Gamma_pos_of_pos (by linarith : 0 < a - 2)).ne']

/-- The variance of an inverse-gamma law is
`r² / ((a - 1)² * (a - 2))` when `2 < a`. -/
@[simp]
theorem variance_id_inverseGammaMeasure (hr : 0 < r) (ha : 2 < a) :
    variance id (inverseGammaMeasure a r) = r ^ 2 / ((a - 1) ^ 2 * (a - 2)) := by
  let _ := isProbabilityMeasure_inverseGammaMeasure (by linarith : 0 < a) hr
  have hint2 : Integrable (fun x : ℝ ↦ x ^ 2) (inverseGammaMeasure a r) :=
    (integrable_pow_inverseGammaMeasure_iff (by linarith : 0 < a) hr 2).2 (by
      norm_num
      exact ha)
  have hLp : MemLp id 2 (inverseGammaMeasure a r) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      (by simpa using hint2)
  rw [variance_eq_sub hLp]
  simp only [Pi.pow_apply, id_eq]
  rw [integral_sq_inverseGammaMeasure hr ha, integral_id_inverseGammaMeasure hr (by linarith)]
  have ha1 : a - 1 ≠ 0 := by linarith
  have ha2 : a - 2 ≠ 0 := by linarith
  field_simp [ha1, ha2]
  ring

/-- The identity is integrable under a valid inverse-gamma law exactly above shape one. -/
@[simp]
theorem integrable_id_inverseGammaMeasure_iff (ha : 0 < a) (hr : 0 < r) :
    Integrable id (inverseGammaMeasure a r) ↔ 1 < a := by
  simpa only [Function.id_def, pow_one, Nat.cast_one] using
    integrable_pow_inverseGammaMeasure_iff ha hr 1

/-- At and below shape one, the identity is not integrable under a valid inverse-gamma law. -/
theorem not_integrable_id_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) (h : a ≤ 1) :
    ¬ Integrable id (inverseGammaMeasure a r) :=
  (integrable_id_inverseGammaMeasure_iff ha hr).not.mpr (not_lt.mpr h)

/-- At and below shape two, the square is not integrable under a valid inverse-gamma law. -/
theorem not_integrable_sq_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) (h : a ≤ 2) :
    ¬ Integrable (fun x : ℝ ↦ x ^ 2) (inverseGammaMeasure a r) :=
  (integrable_pow_inverseGammaMeasure_iff ha hr 2).not.mpr (by simpa using h)

/-! ### Exponential moments -/

/-- Every nonpositive exponential moment of a valid inverse-gamma law exists. -/
theorem integrable_exp_mul_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) (ht : t ≤ 0) :
    Integrable (fun x : ℝ ↦ Real.exp (t * x)) (inverseGammaMeasure a r) := by
  let _ := isProbabilityMeasure_inverseGammaMeasure ha hr
  refine Integrable.mono' (integrable_const 1) (by fun_prop) ?_
  filter_upwards [ae_pos_inverseGammaMeasure a r] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  nlinarith [hx.le]

/-- **Positive exponential moments of a valid inverse-gamma law do not exist.** -/
theorem not_integrable_exp_mul_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) (ht : 0 < t) :
    ¬ Integrable (fun x : ℝ ↦ Real.exp (t * x)) (inverseGammaMeasure a r) := by
  intro hint
  have hpow := integrable_pow_of_integrable_exp_mul ht.ne' hint
    (integrable_exp_mul_inverseGammaMeasure ha hr (by linarith : -t ≤ 0)) ⌈a⌉₊
  exact (not_lt_of_ge (Nat.le_ceil a))
    ((integrable_pow_inverseGammaMeasure_iff ha hr ⌈a⌉₊).1 hpow)

/-- **The exact exponential-integrability domain of a valid inverse-gamma law** is the
nonpositive half-line. -/
@[simp]
theorem integrableExpSet_id_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) :
    integrableExpSet id (inverseGammaMeasure a r) = Iic 0 := by
  ext u
  simp only [integrableExpSet, Set.mem_ofPred_eq, id_eq, mem_Iic]
  exact ⟨fun h ↦ not_lt.mp fun hu ↦ not_integrable_exp_mul_inverseGammaMeasure ha hr hu h,
    integrable_exp_mul_inverseGammaMeasure ha hr⟩

/-! ### Cumulative distribution function -/

/-- **The cdf of a valid inverse-gamma law** is the upper regularized Gamma value
`1 - P(a, r / x)` on the positive half-line and zero elsewhere. -/
@[simp]
theorem cdf_inverseGammaMeasure_eq (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    cdf (inverseGammaMeasure a r) x =
      if x ≤ 0 then 0 else 1 - regularizedGamma a (r / x) := by
  let _ := isProbabilityMeasure_inverseGammaMeasure ha hr
  split_ifs with hx
  · rw [cdf_eq_real, measureReal_def,
      measure_mono_null (Iic_subset_Iic.mpr hx) (inverseGammaMeasure_Iic_zero a r),
      ENNReal.toReal_zero]
  · have hxpos : 0 < x := not_le.mp hx
    rw [cdf_eq_real, inverseGammaMeasure_of_pos ha hr, measureReal_def,
      Measure.map_apply measurable_inv measurableSet_Iic]
    have hpre : Inv.inv ⁻¹' Iic x = Iic 0 ∪ Ici x⁻¹ := by
      ext y
      simp only [mem_preimage, mem_Iic, mem_union, mem_Ici]
      constructor
      · intro hy
        rcases le_or_gt y 0 with hy0 | hy0
        · exact Or.inl hy0
        · exact Or.inr ((inv_le_comm₀ hy0 hxpos).mp hy)
      · rintro (hy | hy)
        · exact (inv_nonpos.mpr hy).trans hxpos.le
        · have hypos : 0 < y := (inv_pos.mpr hxpos).trans_le hy
          exact (inv_le_comm₀ hypos hxpos).mpr hy
    have hsubset : Ici x⁻¹ ⊆ Ioi (0 : ℝ) := fun y hy ↦
      (inv_pos.mpr hxpos).trans_le hy
    have hdisj : Disjoint (Iic (0 : ℝ)) (Ici x⁻¹) := Set.disjoint_left.2 fun y hy0 hy ↦
      (not_lt_of_ge hy0) ((inv_pos.mpr hxpos).trans_le hy)
    have hzero : gammaMeasure a r (Iic 0) = 0 := by
      let _ := isProbabilityMeasure_gammaMeasure ha hr
      rw [← measureReal_eq_zero_iff, measureReal_Iic_gammaMeasure ha hr,
        mul_zero, regularizedGamma_eq_zero_of_nonpos_right a le_rfl]
    rw [hpre, measure_union hdisj measurableSet_Ici,
      hzero, zero_add]
    have hsets : Ici x⁻¹ =ᵐ[gammaMeasure a r] Ioi x⁻¹ :=
      (Ioi_ae_eq_Ici' (μ := gammaMeasure a r) (by
        rw [gammaMeasure]
        exact measure_singleton _)).symm
    rw [measure_congr hsets, ← measureReal_def, measureReal_Ioi_gammaMeasure ha hr x⁻¹,
      div_eq_mul_inv]

/-! ### Parameter measurability -/

/-- The inverse-gamma family is jointly measurable in its parameters. -/
@[fun_prop]
theorem measurable_inverseGammaMeasure :
    Measurable fun p : ℝ × ℝ ↦ inverseGammaMeasure p.1 p.2 := by
  unfold inverseGammaMeasure
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd)
  · exact (Measure.measurable_map _ measurable_inv).comp measurable_gammaMeasure

end Probability

end TauCeti
