/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Density
public import TauCeti.Probability.Distributions.Gamma.Cdf
public import TauCeti.Probability.Distributions.Measurability
public import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.JacobianOneDim
import TauCeti.Probability.Distributions.PDFInstances

/-!
# The inverse-gamma distribution

The inverse-gamma law with shape `a` and rate `r` is the law of `X⁻¹` for
`X ∼ gammaMeasure a r`.  This file defines that pushforward for positive parameters and uses
the zero measure otherwise.  It derives the density

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

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 3, **Inverse-gamma**.
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

/-- The inverse-gamma law with shape `a` and rate `r`.

For positive parameters it is the pushforward of `gammaMeasure a r` by inversion.  It is the zero
measure if either parameter is nonpositive. -/
def inverseGammaMeasure (a r : ℝ) : Measure ℝ :=
  if 0 < a ∧ 0 < r then (gammaMeasure a r).map Inv.inv else 0

/-- At positive parameters the inverse-gamma law is the inversion pushforward of the Gamma law. -/
theorem inverseGammaMeasure_of_pos (ha : 0 < a) (hr : 0 < r) :
    inverseGammaMeasure a r = (gammaMeasure a r).map Inv.inv := by
  rw [inverseGammaMeasure, ite_eq_left ⟨ha, hr⟩]

/-- If the shape or rate is nonpositive, the inverse-gamma law is the zero measure. -/
@[simp]
theorem inverseGammaMeasure_of_not_pos (h : ¬ (0 < a ∧ 0 < r)) :
    inverseGammaMeasure a r = 0 := by
  rw [inverseGammaMeasure, ite_eq_right h]

/-- A valid inverse-gamma law is a probability measure. -/
theorem isProbabilityMeasure_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) :
    IsProbabilityMeasure (inverseGammaMeasure a r) := by
  rw [inverseGammaMeasure_of_pos ha hr]
  let _ := isProbabilityMeasure_gammaMeasure ha hr
  exact Measure.isProbabilityMeasure_map measurable_inv.aemeasurable

/-- A valid Gamma law gives no mass to the nonpositive half-line. -/
private theorem gammaMeasure_Iic_zero (ha : 0 < a) (hr : 0 < r) :
    gammaMeasure a r (Iic 0) = 0 := by
  let _ := isProbabilityMeasure_gammaMeasure ha hr
  have hreal : (gammaMeasure a r).real (Iic 0) = 0 := by
    rw [measureReal_Iic_gammaMeasure ha hr 0,
      regularizedGamma_eq_zero_of_nonpos_right a (by simp)]
  rw [measureReal_def] at hreal
  exact ((ENNReal.toReal_eq_zero_iff _).mp hreal).resolve_right (measure_lt_top _ _).ne

/-- A Gamma law has no atoms. -/
private theorem gammaMeasure_singleton (a r y : ℝ) : gammaMeasure a r {y} = 0 := by
  rw [gammaMeasure, withDensity_apply _ (measurableSet_singleton y)]
  exact setLIntegral_measure_zero _ _ (measure_singleton y)

/-- The inverse-gamma law assigns no mass to the nonpositive half-line. -/
@[simp]
theorem inverseGammaMeasure_Iic_zero (ha : 0 < a) (hr : 0 < r) :
    inverseGammaMeasure a r (Iic 0) = 0 := by
  rw [inverseGammaMeasure_of_pos ha hr, Measure.map_apply measurable_inv measurableSet_Iic]
  have hpre : Inv.inv ⁻¹' Iic (0 : ℝ) = Iic 0 := by
    ext y
    simp only [mem_preimage, mem_Iic]
    exact inv_nonpos
  rw [hpre, gammaMeasure_Iic_zero ha hr]

/-- A variable with a valid inverse-gamma law is almost surely positive. -/
theorem ae_pos_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) :
    ∀ᵐ x ∂inverseGammaMeasure a r, 0 < x := by
  rw [ae_iff]
  simpa only [not_lt, ← Iic_def] using inverseGammaMeasure_Iic_zero ha hr

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

/-- The real-valued inverse-gamma density is nonnegative. -/
theorem inverseGammaPDFReal_nonneg (a r x : ℝ) : 0 ≤ inverseGammaPDFReal a r x := by
  rw [inverseGammaPDFReal]
  split_ifs with h
  · exact mul_nonneg
      (mul_nonneg (div_nonneg (Real.rpow_nonneg h.2.1.le _)
        (Real.Gamma_pos_of_pos h.1).le) (Real.rpow_nonneg h.2.2.le _))
      (Real.exp_pos _).le
  · exact le_rfl

/-- The `ℝ≥0∞` density is the nonnegative coercion of the real density. -/
theorem inverseGammaPDF_eq_ofReal (a r x : ℝ) :
    inverseGammaPDF a r x = ENNReal.ofReal (inverseGammaPDFReal a r x) := by
  rw [inverseGammaPDF]

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
  rw [abs_neg, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hx)), inverseGammaPDF, gammaPDF,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (sq_nonneg x)),
    inverseGammaPDFReal_eq_inv_sq_mul_gammaPDFReal ha hr (inv_pos.mpr hx), inv_inv,
    inv_pow, inv_inv, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hx.ne'), one_mul]

/-- **The density of a valid inverse-gamma law.** -/
theorem inverseGammaMeasure_eq_withDensity (ha : 0 < a) (hr : 0 < r) :
    inverseGammaMeasure a r = volume.withDensity (inverseGammaPDF a r) := by
  ext s hs
  let u : Set ℝ := Ioi 0 ∩ Inv.inv ⁻¹' s
  have hu : MeasurableSet u := measurableSet_Ioi.inter (measurable_inv hs)
  have himage : Inv.inv '' u = Ioi 0 ∩ s := by
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨?_, by simpa using hz.2⟩
      change 0 < z⁻¹
      exact inv_pos.mpr hz.1
    · intro y hy
      refine ⟨y⁻¹, ?_, inv_inv y⟩
      refine ⟨?_, by simpa using hy.2⟩
      change 0 < y⁻¹
      exact inv_pos.mpr hy.1
  calc
    inverseGammaMeasure a r s
        = ∫⁻ y in Inv.inv ⁻¹' s, gammaPDF a r y := by
            rw [inverseGammaMeasure_of_pos ha hr, Measure.map_apply measurable_inv hs,
              gammaMeasure, withDensity_apply _ (measurable_inv hs)]
    _ = ∫⁻ y in u, gammaPDF a r y := by
          have hpre : MeasurableSet (Inv.inv ⁻¹' s) := measurable_inv hs
          have hzero : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := by
            rw [ae_iff]
            simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using
              (measure_singleton (μ := (volume : Measure ℝ)) (0 : ℝ))
          calc
            ∫⁻ y in Inv.inv ⁻¹' s, gammaPDF a r y =
                ∫⁻ y in Inv.inv ⁻¹' s, (Ioi 0).indicator (gammaPDF a r) y := by
              apply setLIntegral_congr_fun_ae hpre
              filter_upwards [hzero] with y hy _
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

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with a valid inverse-gamma law has a density. -/
theorem hasPDF_of_hasLaw_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r)
    (hX : HasLaw X (inverseGammaMeasure a r) P) : HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_inverseGammaPDF a r).aemeasurable
    (by rwa [inverseGammaMeasure_eq_withDensity ha hr] at hX)

/-- The density of a random variable with a valid inverse-gamma law is `inverseGammaPDF`. -/
theorem pdf_eq_inverseGammaPDF_of_hasLaw_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r)
    (hX : HasLaw X (inverseGammaMeasure a r) P) :
    pdf X P volume =ᵐ[volume] inverseGammaPDF a r :=
  pdf_eq_of_hasLaw_withDensity (measurable_inverseGammaPDF a r).aemeasurable
    (by rwa [inverseGammaMeasure_eq_withDensity ha hr] at hX)

/-- The Radon–Nikodym derivative of a valid inverse-gamma law against Lebesgue measure. -/
theorem rnDeriv_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) :
    (inverseGammaMeasure a r).rnDeriv volume =ᵐ[volume] inverseGammaPDF a r := by
  rw [inverseGammaMeasure_eq_withDensity ha hr]
  exact Measure.rnDeriv_withDensity volume (measurable_inverseGammaPDF a r)

/-! ### Moments -/

/-- An integral against a valid Gamma law, restricted to the positive half-line. -/
private lemma integral_gammaMeasure_eq (ha : 0 < a) (hr : 0 < r) (f : ℝ → ℝ) :
    ∫ x, f x ∂gammaMeasure a r =
      ∫ x in Ioi 0, r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x)) * f x := by
  have hcompl : ∀ x ∉ Ici (0 : ℝ), gammaPDFReal a r x * f x = 0 := by
    intro x hx
    rw [gammaPDFReal, ite_eq_right (by simpa using hx), zero_mul]
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul
    (Probability.measurable_gammaPDF a r)
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) f]
  simp_rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _), smul_eq_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hcompl, integral_Ici_eq_integral_Ioi]
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ by
    rw [gammaPDFReal, ite_eq_left hx.le]

/-- Integrability against a valid Gamma law, restricted to the positive half-line. -/
private lemma integrable_gammaMeasure_iff (ha : 0 < a) (hr : 0 < r) (f : ℝ → ℝ) :
    Integrable f (gammaMeasure a r) ↔
      IntegrableOn
        (fun x ↦ r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x)) * f x)
        (Ioi 0) := by
  have hpos : ∀ x ∈ Ioi (0 : ℝ), f x * gammaPDFReal a r x =
      r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x)) * f x := fun x hx ↦ by
    rw [gammaPDFReal, ite_eq_left hx.le]
    ring
  have hneg : IntegrableOn (fun x ↦ f x * gammaPDFReal a r x) (Iio 0) := by
    refine integrableOn_zero.congr_fun (fun x hx ↦ ?_) measurableSet_Iio
    rw [gammaPDFReal, ite_eq_right (not_le.mpr hx), mul_zero]
  rw [gammaMeasure, integrable_withDensity_iff
    (Probability.measurable_gammaPDF a r)
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _)]
  rw [← integrableOn_univ, ← Iio_union_Ici (a := (0 : ℝ)), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨fun h ↦ h.2.congr_fun hpos measurableSet_Ioi,
    fun h ↦ ⟨hneg, h.congr_fun (fun x hx ↦ (hpos x hx).symm) measurableSet_Ioi⟩⟩

/-- Multiplying a Gamma density by the `n`th power of inversion lowers its shape by `n`. -/
private lemma gammaWeight_mul_inv_pow (n : ℕ)
    {x : ℝ} (hx : 0 < x) :
    r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x)) * (x⁻¹) ^ n =
      r ^ a / Real.Gamma a * (x ^ (a - n - 1) * Real.exp (-(r * x))) := by
  have hinv : (x⁻¹) ^ n = x ^ (-(n : ℝ)) := by
    rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hx.le]
  have hpow : x ^ (a - 1) * x ^ (-(n : ℝ)) = x ^ (a - n - 1) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  rw [hinv]
  calc
    r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x)) * x ^ (-(n : ℝ)) =
        r ^ a / Real.Gamma a * (x ^ (a - 1) * x ^ (-(n : ℝ)) *
          Real.exp (-(r * x))) := by ring
    _ = r ^ a / Real.Gamma a * (x ^ (a - n - 1) * Real.exp (-(r * x))) := by
      rw [hpow]

/-- Below the shape threshold, inverse powers are integrable under a Gamma law. -/
private theorem integrable_inv_pow_gammaMeasure (ha : 0 < a) (hr : 0 < r) (n : ℕ)
    (hn : (n : ℝ) < a) : Integrable (fun x : ℝ ↦ (x⁻¹) ^ n) (gammaMeasure a r) := by
  rw [integrable_gammaMeasure_iff ha hr]
  refine IntegrableOn.congr_fun ?_ (fun x hx ↦ (gammaWeight_mul_inv_pow n hx).symm)
    measurableSet_Ioi
  have hkernel : IntegrableOn
      (fun x : ℝ ↦ x ^ (a - n - 1) * Real.exp (-r * x ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := a - n - 1) (b := r)
      (by linarith) one_pos hr
  have hkernel' : IntegrableOn
      (fun x : ℝ ↦ x ^ (a - n - 1) * Real.exp (-(r * x))) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using hkernel
  exact hkernel'.const_mul _

/-- At or above the shape threshold, inverse powers are not integrable under a Gamma law. -/
private theorem not_integrable_inv_pow_gammaMeasure (ha : 0 < a) (hr : 0 < r) (n : ℕ)
    (hn : a ≤ n) : ¬ Integrable (fun x : ℝ ↦ (x⁻¹) ^ n) (gammaMeasure a r) := by
  rw [integrable_gammaMeasure_iff ha hr]
  intro hint
  have hC : 0 < r ^ a / Real.Gamma a := by positivity
  have hsmall := hint.mono_set (Ioo_subset_Ioi_self : Ioo (0 : ℝ) 1 ⊆ Ioi 0)
  have hscaled : IntegrableOn
      (fun x : ℝ ↦ (r ^ a / Real.Gamma a * Real.exp (-r)) * x ^ (a - n - 1))
      (Ioo 0 1) := by
    refine Integrable.mono' hsmall (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hexp : Real.exp (-r) ≤ Real.exp (-(r * x)) :=
      Real.exp_le_exp.mpr (by nlinarith [hx.2, hr])
    have hxpow : 0 ≤ x ^ (a - n - 1) := Real.rpow_nonneg hx.1.le _
    rw [gammaWeight_mul_inv_pow n hx.1]
    have hleft : 0 ≤ (r ^ a / Real.Gamma a * Real.exp (-r)) * x ^ (a - n - 1) :=
      mul_nonneg (mul_nonneg hC.le (Real.exp_pos _).le) hxpow
    calc
      ‖(r ^ a / Real.Gamma a * Real.exp (-r)) * x ^ (a - n - 1)‖ =
          (r ^ a / Real.Gamma a * Real.exp (-r)) * x ^ (a - n - 1) :=
        Real.norm_of_nonneg hleft
      _ =
          (r ^ a / Real.Gamma a * x ^ (a - n - 1)) * Real.exp (-r) := by ring
      _ ≤ (r ^ a / Real.Gamma a * x ^ (a - n - 1)) * Real.exp (-(r * x)) :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg hC.le hxpow)
      _ = r ^ a / Real.Gamma a * (x ^ (a - n - 1) * Real.exp (-(r * x))) := by ring
  have hpow := hscaled.const_mul (r ^ a / Real.Gamma a * Real.exp (-r))⁻¹
  have hpow' : IntegrableOn (fun x : ℝ ↦ x ^ (a - n - 1)) (Ioo 0 1) := by
    refine IntegrableOn.congr_fun hpow (fun x _ ↦ ?_) measurableSet_Ioo
    rw [inv_mul_cancel_left₀]
    positivity
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff one_pos] at hpow'
  linarith

/-- A natural power is integrable under a valid inverse-gamma law exactly below the shape. -/
theorem integrable_pow_inverseGammaMeasure_iff (ha : 0 < a) (hr : 0 < r) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (inverseGammaMeasure a r) ↔ (n : ℝ) < a := by
  rw [inverseGammaMeasure_of_pos ha hr,
    integrable_map_measure (by fun_prop) measurable_inv.aemeasurable]
  exact ⟨fun h ↦ lt_of_not_ge fun hn ↦ not_integrable_inv_pow_gammaMeasure ha hr n hn h,
    integrable_inv_pow_gammaMeasure ha hr n⟩

/-- **Natural moments of a valid inverse-gamma law.**  The `n`th moment exists for `n < a` and
equals `r ^ n * Gamma (a - n) / Gamma a`. -/
theorem integral_pow_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) (n : ℕ)
    (hn : (n : ℝ) < a) :
    ∫ x, x ^ n ∂inverseGammaMeasure a r =
      r ^ n * Real.Gamma (a - n) / Real.Gamma a := by
  rw [inverseGammaMeasure_of_pos ha hr,
    integral_map measurable_inv.aemeasurable (by fun_prop)]
  rw [integral_gammaMeasure_eq ha hr,
    setIntegral_congr_fun measurableSet_Ioi (fun x hx ↦ gammaWeight_mul_inv_pow n hx)]
  have han : 0 < a - (n : ℝ) := sub_pos.mpr hn
  rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi han hr]
  have hGa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  rw [one_div, Real.inv_rpow hr.le, div_eq_mul_inv, Real.rpow_sub hr,
    Real.rpow_natCast]
  field_simp

/-- The mean of an inverse-gamma law is `r / (a - 1)` when `1 < a`. -/
theorem integral_id_inverseGammaMeasure (hr : 0 < r) (ha : 1 < a) :
    ∫ x, x ∂inverseGammaMeasure a r = r / (a - 1) := by
  have h := integral_pow_inverseGammaMeasure (by linarith : 0 < a) hr 1 (by simpa using ha)
  simp only [pow_one, Nat.cast_one] at h
  rw [h]
  have hrec : Real.Gamma a = (a - 1) * Real.Gamma (a - 1) := by
    calc
      Real.Gamma a = Real.Gamma ((a - 1) + 1) := by congr 1; ring
      _ = (a - 1) * Real.Gamma (a - 1) :=
        Real.Gamma_add_one (by linarith : a - 1 ≠ 0)
  rw [hrec]
  field_simp [(Real.Gamma_pos_of_pos (by linarith : 0 < a - 1)).ne']

/-- The second raw moment of an inverse-gamma law is
`r² / ((a - 1) * (a - 2))` when `2 < a`. -/
theorem integral_sq_inverseGammaMeasure (hr : 0 < r) (ha : 2 < a) :
    ∫ x, x ^ 2 ∂inverseGammaMeasure a r = r ^ 2 / ((a - 1) * (a - 2)) := by
  have h := integral_pow_inverseGammaMeasure (by linarith : 0 < a) hr 2 (by simpa using ha)
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  have hrec1 : Real.Gamma a = (a - 1) * Real.Gamma (a - 1) := by
    calc
      Real.Gamma a = Real.Gamma ((a - 1) + 1) := by congr 1; ring
      _ = (a - 1) * Real.Gamma (a - 1) :=
        Real.Gamma_add_one (by linarith : a - 1 ≠ 0)
  have hrec2 : Real.Gamma (a - 1) = (a - 2) * Real.Gamma (a - 2) := by
    calc
      Real.Gamma (a - 1) = Real.Gamma ((a - 2) + 1) := by congr 1; ring
      _ = (a - 2) * Real.Gamma (a - 2) :=
        Real.Gamma_add_one (by linarith : a - 2 ≠ 0)
  have hstep : Real.Gamma a = (a - 1) * ((a - 2) * Real.Gamma (a - 2)) := by
    rw [hrec1, hrec2]
  rw [hstep]
  field_simp [(Real.Gamma_pos_of_pos (by linarith : 0 < a - 2)).ne']

/-- The variance of an inverse-gamma law is
`r² / ((a - 1)² * (a - 2))` when `2 < a`. -/
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

/-- At and below shape one, the identity is not integrable under a valid inverse-gamma law. -/
theorem not_integrable_id_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) (h : a ≤ 1) :
    ¬ Integrable id (inverseGammaMeasure a r) := by
  change ¬ Integrable (fun x : ℝ ↦ x) (inverseGammaMeasure a r)
  intro hint
  have hint' : Integrable (fun x : ℝ ↦ x ^ 1) (inverseGammaMeasure a r) := by
    simpa only [pow_one] using hint
  have hlt := (integrable_pow_inverseGammaMeasure_iff ha hr 1).1 hint'
  norm_num at hlt
  exact (not_lt_of_ge h) hlt

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
  filter_upwards [ae_pos_inverseGammaMeasure ha hr] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  nlinarith [hx.le]

/-- **Positive exponential moments of a valid inverse-gamma law do not exist.** -/
theorem not_integrable_exp_mul_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) (ht : 0 < t) :
    ¬ Integrable (fun x : ℝ ↦ Real.exp (t * x)) (inverseGammaMeasure a r) := by
  rw [inverseGammaMeasure_eq_withDensity ha hr,
    integrable_withDensity_iff (measurable_inverseGammaPDF a r)
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  intro hint
  simp only [inverseGammaPDF,
    ENNReal.toReal_ofReal (inverseGammaPDFReal_nonneg a r _)] at hint
  have hC : 0 < r ^ a / Real.Gamma a := by positivity
  have hD : 0 < r ^ a / Real.Gamma a * Real.exp (-r) := mul_pos hC (Real.exp_pos _)
  have hgrowth : Tendsto
      (fun x : ℝ ↦ (r ^ a / Real.Gamma a * Real.exp (-r)) *
        (Real.exp (t * x) / x ^ (a + 1))) atTop atTop :=
    (tendsto_exp_mul_div_rpow_atTop (a + 1) t ht).const_mul_atTop hD
  have hev : ∀ᶠ x in atTop,
      (1 : ℝ) ≤ Real.exp (t * x) * inverseGammaPDFReal a r x := by
    filter_upwards [hgrowth.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℝ)]
      with x hxgrowth hx
    have hxpos : 0 < x := zero_lt_one.trans_le hx
    have hexp : Real.exp (-r) ≤ Real.exp (-r / x) := by
      refine Real.exp_le_exp.mpr ?_
      have hdiv : r / x ≤ r := (div_le_iff₀ hxpos).2 (by nlinarith [hr])
      rw [neg_div]
      exact neg_le_neg hdiv
    have hpow : x ^ (-a - 1) = 1 / x ^ (a + 1) := by
      rw [one_div, ← Real.rpow_neg hxpos.le]
      congr 1
      ring
    rw [inverseGammaPDFReal_of_pos ha hr hxpos, hpow]
    calc
      (1 : ℝ) ≤ (r ^ a / Real.Gamma a * Real.exp (-r)) *
          (Real.exp (t * x) / x ^ (a + 1)) := hxgrowth
      _ = (r ^ a / Real.Gamma a * Real.exp (t * x) / x ^ (a + 1)) *
          Real.exp (-r) := by ring
      _ ≤ (r ^ a / Real.Gamma a * Real.exp (t * x) / x ^ (a + 1)) *
          Real.exp (-r / x) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = Real.exp (t * x) *
          (r ^ a / Real.Gamma a * (1 / x ^ (a + 1)) * Real.exp (-r / x)) := by ring
  obtain ⟨b, hb⟩ := eventually_atTop.mp hev
  have hone : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Ioi b) volume := by
    refine Integrable.mono' hint.integrableOn (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_one]
    exact hb x hx.le
  rw [integrableOn_const_iff] at hone
  simp [Real.volume_Ioi] at hone

/-- **The exact exponential-integrability domain of a valid inverse-gamma law** is the
nonpositive half-line. -/
theorem integrableExpSet_id_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) :
    integrableExpSet id (inverseGammaMeasure a r) = Iic 0 := by
  ext u
  simp only [integrableExpSet, Set.mem_ofPred_eq, id_eq, mem_Iic]
  exact ⟨fun h ↦ not_lt.mp fun hu ↦ not_integrable_exp_mul_inverseGammaMeasure ha hr hu h,
    integrable_exp_mul_inverseGammaMeasure ha hr⟩

/-! ### Cumulative distribution function -/

/-- **The cdf of a valid inverse-gamma law** is the upper regularized Gamma value
`1 - P(a, r / x)` on the positive half-line and zero elsewhere. -/
theorem cdf_inverseGammaMeasure_eq (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    cdf (inverseGammaMeasure a r) x =
      if x ≤ 0 then 0 else 1 - regularizedGamma a (r / x) := by
  let _ := isProbabilityMeasure_inverseGammaMeasure ha hr
  split_ifs with hx
  · rw [cdf_eq_real, measureReal_def,
      measure_mono_null (Iic_subset_Iic.mpr hx) (inverseGammaMeasure_Iic_zero ha hr),
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
    rw [hpre, measure_union hdisj measurableSet_Ici,
      gammaMeasure_Iic_zero ha hr, zero_add]
    have hsets : Ici x⁻¹ =ᵐ[gammaMeasure a r] Ioi x⁻¹ := by
      rw [ae_eq_set]
      constructor
      · have hdiff : Ici x⁻¹ \ Ioi x⁻¹ = {x⁻¹} := by ext y; simp [le_antisymm_iff]
        rw [hdiff]
        exact gammaMeasure_singleton a r _
      · simp
    rw [measure_congr hsets, ← measureReal_def, measureReal_Ioi_gammaMeasure ha hr x⁻¹]
    congr 2

/-! ### Parameter measurability -/

/-- The inverse-gamma family is jointly measurable in its parameters. -/
theorem measurable_inverseGammaMeasure :
    Measurable fun p : ℝ × ℝ ↦ inverseGammaMeasure p.1 p.2 := by
  unfold inverseGammaMeasure
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd)
  · exact (Measure.measurable_map _ measurable_inv).comp measurable_gammaMeasure

end Probability

end TauCeti
