/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Probability.Distributions.Cauchy
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.Probability.Moments.Variance
public import TauCeti.Analysis.Fourier.ExpNegAbs
public import TauCeti.Probability.Distributions.Dirac

/-!
# The cumulative distribution function and the characteristic function of the Cauchy law

This file develops the elementary transform theory of Mathlib's Cauchy law. For nonzero scale
`γ` the cumulative distribution function at `x` is

`1 / 2 + arctan ((x - x₀) / γ) / π`,

and for every scale, including the degenerate one, the characteristic function is

`t ↦ exp (t x₀ i - γ |t|)`.

At scale zero Mathlib defines `cauchyMeasure x₀ 0` to be the Dirac mass at `x₀`. The file records
the corresponding cumulative distribution function, mean, variance, exponential-integrability
domain, moment-generating function, and cumulant-generating function. Keeping the singular case
separate prevents the density calculation for positive scale from being applied where the law is
not absolutely continuous; the characteristic function, by contrast, is a single formula covering
both cases.

The characteristic function is obtained from the Fourier inversion theorem applied to
`TauCeti.fourier_exp_neg_mul_abs`: the Fourier transform of the two-sided exponential of rate
`2 π γ` is the centred Cauchy density of scale `γ`, so inverting it pairs that density against
`exp (i t x)` and returns the two-sided exponential again. The exponent in the resulting formula
is linear in `x₀` and `γ`, so products of characteristic functions add the locations and scales;
scaling the sum by the reciprocal of the sample size restores the original parameters. Thus the
sample mean of independent Cauchy variables with a common location and scale has exactly the
parent law.

## Main results

* `TauCeti.hasDerivAt_arctan_div_pi` — the derivative underlying the cdf formula;
* `TauCeti.integral_Iic_cauchyPDFReal` — the integral of the Cauchy density over a left
  half-line;
* `TauCeti.cdf_cauchyMeasure_of_scale_ne_zero` — the Cauchy cdf at nonzero scale;
* `TauCeti.cdf_cauchyMeasure_zero_scale` — the cdf of the zero-scale Dirac law;
* `TauCeti.integral_id_cauchyMeasure_zero_scale` and
  `TauCeti.variance_id_cauchyMeasure_zero_scale` — its mean and variance;
* `TauCeti.integrableExpSet_id_cauchyMeasure_zero_scale`,
  `TauCeti.mgf_id_cauchyMeasure_zero_scale`, and
  `TauCeti.cgf_id_cauchyMeasure_zero_scale` — its exponential moments;
* `TauCeti.fourier_exp_neg_mul_abs_eq_cauchyPDFReal_zero_loc` and
  `TauCeti.integral_exp_mul_I_mul_cauchyPDFReal_zero_loc` — the Fourier pair behind the transform;
* `TauCeti.cauchyMeasure_map_add_const` — translation changes the location parameter;
* `TauCeti.charFun_cauchyMeasure` — the characteristic function of `cauchyMeasure x₀ γ`;
* `TauCeti.hasLaw_average_of_iIndepFun_cauchyMeasure` — stability of the family under averaging.

## References

* Tau Ceti roadmap, `StandardDistributions`, Layer 1, "Cauchy".
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley, 1994.
-/

public section

namespace TauCeti

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

/-- The scaled arctangent has the Cauchy density as its derivative. -/
theorem hasDerivAt_arctan_div_pi (x₀ : ℝ) (γ : ℝ≥0) (y : ℝ) :
    HasDerivAt (fun z => Real.arctan ((z - x₀) / (γ : ℝ)) / Real.pi)
      (cauchyPDFReal x₀ γ y) y := by
  have hinner : HasDerivAt (fun z : ℝ => (z - x₀) / (γ : ℝ)) (γ : ℝ)⁻¹ y := by
    simpa only [one_div] using ((hasDerivAt_id' y).sub_const x₀).div_const (γ : ℝ)
  have h := ((Real.hasDerivAt_arctan ((y - x₀) / (γ : ℝ))).comp y hinner).div_const
    Real.pi
  have hvalue :
      ((1 / (1 + ((y - x₀) / (γ : ℝ)) ^ 2)) * (γ : ℝ)⁻¹) / Real.pi =
        cauchyPDFReal x₀ γ y := by
    rw [cauchyPDFReal_def', NNReal.coe_inv]
    ring
  simpa only [Function.comp_apply, hvalue] using h

/-- The Cauchy density has the expected antiderivative on a left half-line. This is the analytic
calculation behind `cdf_cauchyMeasure_of_scale_ne_zero`. -/
theorem integral_Iic_cauchyPDFReal (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) (x : ℝ) :
    ∫ y in Iic x, cauchyPDFReal x₀ γ y =
      1 / 2 + Real.arctan ((x - x₀) / (γ : ℝ)) / Real.pi := by
  let F : ℝ → ℝ := fun y => Real.arctan ((y - x₀) / (γ : ℝ)) / Real.pi
  have hint : IntegrableOn (cauchyPDFReal x₀ γ) (Iic x) :=
    (integrable_cauchyPDFReal (γ := γ) x₀).integrableOn
  have hsub_bot : Tendsto (fun y : ℝ => y - x₀) atBot atBot := by
    simpa [sub_eq_add_neg] using tendsto_atBot_add_const_right atBot (-x₀) tendsto_id
  have hinner_bot : Tendsto (fun y : ℝ => (y - x₀) / (γ : ℝ)) atBot atBot :=
    hsub_bot.atBot_div_const (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ))
  have hF_bot : Tendsto F atBot (nhds ((-(Real.pi / 2)) / Real.pi)) := by
    have harctan : Tendsto (fun y : ℝ => Real.arctan ((y - x₀) / (γ : ℝ))) atBot
        (nhds (-(Real.pi / 2))) :=
      (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp hinner_bot
    simpa only [F] using harctan.div_const Real.pi
  rw [integral_Iic_of_hasDerivAt_of_tendsto'
    (fun y _ => hasDerivAt_arctan_div_pi x₀ γ y) hint hF_bot]
  field_simp [Real.pi_ne_zero]
  ring

/-- **The cumulative distribution function of a nondegenerate Cauchy law.** -/
@[simp]
theorem cdf_cauchyMeasure_of_scale_ne_zero (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) (x : ℝ) :
    cdf (cauchyMeasure x₀ γ) x =
      1 / 2 + Real.arctan ((x - x₀) / (γ : ℝ)) / Real.pi := by
  rw [cdf_eq_real, cauchyMeasure_of_scale_ne_zero x₀ hγ, measureReal_def,
    withDensity_apply _ measurableSet_Iic]
  have hnonneg : 0 ≤ᵐ[volume.restrict (Iic x)] cauchyPDFReal x₀ γ :=
    ae_of_all _ fun y => (cauchyPDF_pos x₀ hγ y).le
  simp_rw [cauchyPDF_def]
  rw [← integral_eq_lintegral_of_nonneg_ae hnonneg
    (measurable_cauchyPDFReal x₀ γ).aestronglyMeasurable]
  exact integral_Iic_cauchyPDFReal x₀ hγ x

/-- **The cumulative distribution function at zero scale.** Mathlib totalizes the Cauchy family
by setting `cauchyMeasure x₀ 0 = Measure.dirac x₀`. -/
theorem cdf_cauchyMeasure_zero_scale (x₀ x : ℝ) :
    cdf (cauchyMeasure x₀ 0) x = if x₀ ≤ x then 1 else 0 := by
  rw [cauchyMeasure_zero_scale, cdf_dirac]

/-- The mean of the zero-scale Cauchy law is its location. -/
theorem integral_id_cauchyMeasure_zero_scale (x₀ : ℝ) :
    ∫ x, x ∂cauchyMeasure x₀ 0 = x₀ := by
  rw [cauchyMeasure_zero_scale, integral_dirac]

/-- The zero-scale Cauchy law has zero variance. -/
theorem variance_id_cauchyMeasure_zero_scale (x₀ : ℝ) :
    variance id (cauchyMeasure x₀ 0) = 0 := by
  rw [cauchyMeasure_zero_scale, variance_dirac]

/-- Every exponential moment of the zero-scale Cauchy law exists. -/
theorem integrableExpSet_id_cauchyMeasure_zero_scale (x₀ : ℝ) :
    integrableExpSet id (cauchyMeasure x₀ 0) = Set.univ := by
  rw [cauchyMeasure_zero_scale, integrableExpSet_dirac]

/-- The moment-generating function of the zero-scale Cauchy law. -/
theorem mgf_id_cauchyMeasure_zero_scale (x₀ t : ℝ) :
    mgf id (cauchyMeasure x₀ 0) t = Real.exp (t * x₀) := by
  rw [cauchyMeasure_zero_scale, mgf_dirac', id_eq]

/-- The cumulant-generating function of the zero-scale Cauchy law. -/
theorem cgf_id_cauchyMeasure_zero_scale (x₀ t : ℝ) :
    cgf id (cauchyMeasure x₀ 0) t = t * x₀ := by
  rw [cauchyMeasure_zero_scale, cgf_dirac', id_eq]

section CharFun

open scoped FourierTransform

variable {γ : ℝ≥0}

private theorem cauchyMeasure_apply_eq_integral (x₀ : ℝ) (hγ : γ ≠ 0)
    {s : Set ℝ} (hs : MeasurableSet s) :
    cauchyMeasure x₀ γ s = ENNReal.ofReal (∫ x in s, cauchyPDFReal x₀ γ x) := by
  rw [cauchyMeasure_of_scale_ne_zero x₀ hγ]
  -- `cauchyPDF` is the `ofReal` lift of `cauchyPDFReal`; exposing it lets the
  -- with-density integral API apply.
  change (volume.withDensity (fun x ↦ ENNReal.ofReal (cauchyPDFReal x₀ γ x))) s = _
  rw [withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_cauchyPDFReal x₀).integrableOn
      (.of_forall fun x ↦ (cauchyPDF_pos x₀ hγ x).le)]

/-- Translating a Cauchy distribution changes its location parameter by the same amount. -/
@[simp]
theorem cauchyMeasure_map_add_const (x₀ y : ℝ) (γ : ℝ≥0) :
    (cauchyMeasure x₀ γ).map (· + y) = cauchyMeasure (x₀ + y) γ := by
  by_cases hγ : γ = 0
  · subst γ
    simp [cauchyMeasure_zero_scale]
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.addRight y).symm.toMeasurableEquiv
  have he' : ∀ x, HasDerivAt e ((fun _ ↦ 1) x) x := fun x ↦ (hasDerivAt_id x).sub_const y
  -- By construction, `e.symm` is the translation `fun x ↦ x + y`.
  change (cauchyMeasure x₀ γ).map e.symm = cauchyMeasure (x₀ + y) γ
  ext s hs
  rw [cauchyMeasure_of_scale_ne_zero x₀ hγ]
  -- As above, unfold the density wrapper to use the Jacobian formula stated for `ofReal`.
  change (volume.withDensity (fun x ↦ ENNReal.ofReal (cauchyPDFReal x₀ γ x))).map e.symm s = _
  rw [
    e.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul' hs he'
      (.of_forall fun x ↦ (cauchyPDF_pos x₀ hγ x).le) (integrable_cauchyPDFReal x₀),
    cauchyMeasure_apply_eq_integral (x₀ + y) hγ hs]
  simp only [abs_one, one_mul]
  congr 2 with x
  dsimp [e, Homeomorph.addRight]
  rw [cauchyPDFReal_def, cauchyPDFReal_def]
  congr 3
  ring

/-- The Fourier transform of the two-sided exponential of rate `2 π γ` is the Cauchy density of
scale `γ` centred at the origin. This is `TauCeti.fourier_exp_neg_mul_abs` at the rate that makes
the Lorentzian a probability density. -/
theorem fourier_exp_neg_mul_abs_eq_cauchyPDFReal_zero_loc (hγ : γ ≠ 0) (ξ : ℝ) :
    𝓕 (fun x : ℝ ↦ (Real.exp (-(2 * Real.pi * γ * |x|)) : ℂ)) ξ = (cauchyPDFReal 0 γ ξ : ℂ) := by
  have hγ' : (0 : ℝ) < (γ : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ)
  have ha : (0 : ℝ) < 2 * Real.pi * γ := mul_pos (by positivity) hγ'
  have h₁ : (0 : ℝ) < (2 * Real.pi * (γ : ℝ)) ^ 2 + (2 * Real.pi * ξ) ^ 2 :=
    add_pos_of_pos_of_nonneg (pow_pos ha 2) (sq_nonneg _)
  have h₂ : (0 : ℝ) < (ξ - 0) ^ 2 + (γ : ℝ) ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hγ' 2)
  rw [fourier_exp_neg_mul_abs ha, Complex.ofReal_inj, cauchyPDFReal_def]
  field_simp
  ring

/-- **The oscillatory integral of the centred Cauchy density.** Fourier inversion turns
`TauCeti.fourier_exp_neg_mul_abs_eq_cauchyPDFReal_zero_loc` around: pairing the Cauchy density of
scale `γ` against `exp (i t x)` returns the two-sided exponential `exp (-(γ * |t|))`. -/
theorem integral_exp_mul_I_mul_cauchyPDFReal_zero_loc (hγ : γ ≠ 0) (t : ℝ) :
    (∫ x : ℝ, Complex.exp ((t : ℂ) * x * Complex.I) * (cauchyPDFReal 0 γ x : ℂ))
      = (Real.exp (-((γ : ℝ) * |t|)) : ℂ) := by
  have hγ' : (0 : ℝ) < (γ : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ)
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have ha : (0 : ℝ) < 2 * Real.pi * γ := mul_pos hπ hγ'
  have hcont : Continuous (fun x : ℝ ↦ (Real.exp (-(2 * Real.pi * γ * |x|)) : ℂ)) := by fun_prop
  have hint : Integrable (fun x : ℝ ↦ (Real.exp (-(2 * Real.pi * γ * |x|)) : ℂ)) :=
    (integrable_exp_neg_mul_abs ha).ofReal
  have hFf : 𝓕 (fun x : ℝ ↦ (Real.exp (-(2 * Real.pi * γ * |x|)) : ℂ))
      = fun ξ : ℝ ↦ (cauchyPDFReal 0 γ ξ : ℂ) :=
    funext (fourier_exp_neg_mul_abs_eq_cauchyPDFReal_zero_loc hγ)
  have hintF : Integrable (𝓕 (fun x : ℝ ↦ (Real.exp (-(2 * Real.pi * γ * |x|)) : ℂ))) := by
    rw [hFf]
    exact (integrable_cauchyPDFReal 0).ofReal
  have hinv := congrFun (hcont.fourierInv_fourier_eq hint hintF) (t / (2 * Real.pi))
  rw [hFf, Real.fourierInv_eq'] at hinv
  have habs : 2 * Real.pi * (γ : ℝ) * |t / (2 * Real.pi)| = (γ : ℝ) * |t| := by
    rw [abs_div, abs_of_pos hπ]
    field_simp
  rw [← habs, ← hinv]
  refine integral_congr_ae (.of_forall fun v ↦ ?_)
  dsimp only
  rw [smul_eq_mul]
  congr 2
  push_cast [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  field_simp

private theorem charFun_cauchyMeasure_zero_loc (hγ : γ ≠ 0) (t : ℝ) :
    charFun (cauchyMeasure 0 γ) t = (Real.exp (-((γ : ℝ) * |t|)) : ℂ) := by
  have hltop : ∀ᵐ x : ℝ ∂volume, cauchyPDF 0 γ x < ⊤ :=
    .of_forall fun x ↦ by rw [cauchyPDF_def]; exact ENNReal.ofReal_lt_top
  rw [charFun_apply_real, cauchyMeasure_of_scale_ne_zero 0 hγ,
    integral_withDensity_eq_integral_toReal_smul (measurable_cauchyPDF 0 γ) hltop]
  have htoReal : ∀ x : ℝ, (cauchyPDF 0 γ x).toReal = cauchyPDFReal 0 γ x := fun x ↦ by
    rw [cauchyPDF_def, ENNReal.toReal_ofReal (cauchyPDF_pos 0 hγ x).le]
  simp_rw [htoReal]
  simpa only [Complex.real_smul, mul_comm] using
    integral_exp_mul_I_mul_cauchyPDFReal_zero_loc hγ t

/-- **The characteristic function of the Cauchy distribution.** For location `x₀` and scale `γ`
it is `t ↦ exp (t x₀ i - γ |t|)`. The formula is uniform in the scale: at `γ = 0` Mathlib's
`cauchyMeasure x₀ 0` is the Dirac mass at `x₀`, whose characteristic function is
`t ↦ exp (t x₀ i)`. -/
@[simp]
theorem charFun_cauchyMeasure (x₀ : ℝ) (γ : ℝ≥0) (t : ℝ) :
    charFun (cauchyMeasure x₀ γ) t
      = Complex.exp ((t : ℂ) * x₀ * Complex.I - ((γ : ℝ) : ℂ) * |t|) := by
  rcases eq_or_ne γ 0 with rfl | hγ
  · rw [cauchyMeasure_zero_scale, charFun_dirac]
    simp [RCLike.inner_apply, mul_comm]
  · have hmap := cauchyMeasure_map_add_const 0 x₀ γ
    simp only [zero_add] at hmap
    rw [← hmap, charFun_map_add_const, charFun_cauchyMeasure_zero_loc hγ,
      Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    ring

/-- **The Cauchy family is stable under averaging.** The sample mean of `n` independent Cauchy
variables with common location `x₀` and scale `γ` has exactly the same law. -/
theorem hasLaw_average_of_iIndepFun_cauchyMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) {x₀ : ℝ} {γ : ℝ≥0}
    {X : Fin n → Ω → ℝ} (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (cauchyMeasure x₀ γ) P) :
    HasLaw (fun ω ↦ (n : ℝ)⁻¹ * ∑ i, X i ω) (cauchyMeasure x₀ γ) P where
  aemeasurable :=
    (Finset.aemeasurable_fun_sum _ fun i _ ↦ (hlaw i).aemeasurable).const_mul _
  map_eq := by
    have hmeas : AEMeasurable (fun ω ↦ ∑ i, X i ω) P :=
      Finset.aemeasurable_fun_sum _ fun i _ ↦ (hlaw i).aemeasurable
    refine Measure.ext_of_charFun (funext fun t ↦ ?_)
    rw [charFun_map_mul_comp hmeas,
      hindep.charFun_map_fun_sum_eq_prod (fun i ↦ (hlaw i).aemeasurable)]
    have hone : ∀ i : Fin n, charFun (P.map (X i)) ((n : ℝ)⁻¹ * t)
        = Complex.exp ((((n : ℝ)⁻¹ * t : ℝ) : ℂ) * x₀ * Complex.I
          - ((γ : ℝ) : ℂ) * |(n : ℝ)⁻¹ * t|) := fun i ↦ by
      rw [(hlaw i).map_eq, charFun_cauchyMeasure]
    rw [Finset.prod_apply, Finset.prod_congr rfl fun i _ ↦ hone i, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← Complex.exp_nat_mul, charFun_cauchyMeasure]
    congr 1
    have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have habs : |(n : ℝ)⁻¹ * t| = (n : ℝ)⁻¹ * |t| := by
      rw [abs_mul, abs_of_pos (by positivity)]
    have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    rw [habs]
    push_cast
    field_simp

end CharFun

end TauCeti
