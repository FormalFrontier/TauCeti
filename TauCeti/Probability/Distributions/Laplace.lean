/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Density
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# The Laplace distribution

The Laplace law with location `μ` and scale `b` is the two-sided exponential law: its density is
`(2 * b)⁻¹ * exp (-|x - μ| / b)`. This file defines it, proves it is a probability measure for
`0 < b`, identifies it as a `MeasureTheory.HasPDF` law with that density, and computes the cdf,
every absolute central moment, the mean, and the variance. The variance is derived from the second
absolute central moment.

**Boundary.** The scale must be positive for the two-sided exponential formula to normalize to a
probability density, so both
`laplacePDFReal` and `laplaceMeasure` are *defined* to vanish for `b ≤ 0`
(`laplaceMeasure_of_nonpos`); formulas that describe the probability law carry `0 < b` as a
hypothesis.

## Main definitions

* `TauCeti.Probability.laplacePDFReal` — the real-valued density;
* `TauCeti.Probability.laplacePDF` — its `ℝ≥0∞`-valued companion;
* `TauCeti.Probability.laplaceMeasure` — the law, as `volume.withDensity laplacePDF`.

## Main results

* `isProbabilityMeasure_laplaceMeasure` — it is a probability measure when `0 < b`;
* `hasPDF_of_hasLaw_laplaceMeasure`, `pdf_eq_laplacePDF_of_hasLaw_laplaceMeasure` and
  `rnDeriv_laplaceMeasure` — the `HasPDF` bridge, the density, and the Radon–Nikodym derivative;
* `cdf_laplaceMeasure_eq` — the cdf is `exp ((x - μ) / b) / 2` below the location and
  `1 - exp (-(x - μ) / b) / 2` above it;
* `integral_pow_abs_sub_laplaceMeasure` — the absolute central moments are `n ! * b ^ n`;
* `integral_id_laplaceMeasure` — the mean is `μ`;
* `variance_id_laplaceMeasure` — the variance is `2 * b ^ 2`;
* `measurable_laplaceMeasure` — the family is measurable in its two parameters, so it can be used
  as a kernel.

## Implementation

Resolving the absolute value on either side of the location turns the density into a constant
multiple of `x ↦ exp (r * x)` with `r = b⁻¹` of one sign or the other, so Mathlib's
`integral_exp_mul_Iic` and `integral_exp_mul_Ioi` give the two tail masses directly; the total
mass `1` is the sum of the two halves at `x = μ`.

The moments take a different route. Translating by the location with
`MeasureTheory.integral_sub_right_eq_self` makes the integrand a function of `|x|`, and Mathlib's
`integral_comp_abs` folds that onto the positive half-line, where the moment is Euler's integral
`MeasureTheory.integral_rpow_mul_exp_neg_mul_rpow`. The mean is *not* computed from a first
moment: the translated integrand is odd, so the whole integral vanishes by the reflection
invariance of Lebesgue measure, and the variance is the second absolute central moment.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 3, the **Laplace** target —
  the measure and its density for `0 < b`, its vanishing for `b ≤ 0`, the mean `μ`, the variance
  `2 * b ^ 2` and the cdf — together with the Laplace case of the items 1–4 required of every
  family in "What every distribution must provide". The exponential-integrability domain, the mgf,
  the cgf and the characteristic function of that same target are not proved here.
* Formal declaration scaffold: `TauCetiRoadmap/StandardDistributions/Suggested.lean`, Layer 3.
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2, 2nd ed.,
  Wiley (1995), ch. 24.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal Nat

namespace TauCeti

namespace Probability

variable {μ b x : ℝ}

/-! ### The density -/

/-- The density of the Laplace law with location `μ` and scale `b`, as a real-valued function.

For `b ≤ 0` there is no such law and the density is `0`. -/
def laplacePDFReal (μ b x : ℝ) : ℝ :=
  if 0 < b then (2 * b)⁻¹ * Real.exp (-|x - μ| / b) else 0

/-- The density of the Laplace law, as a function valued in `ℝ≥0∞`. -/
def laplacePDF (μ b x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (laplacePDFReal μ b x)

/-- The `ℝ≥0∞`-valued Laplace density is the coercion of the real-valued one. -/
theorem laplacePDF_eq_ofReal (μ b x : ℝ) :
    laplacePDF μ b x = ENNReal.ofReal (laplacePDFReal μ b x) := by
  rw [laplacePDF]

/-- Outside the valid parameter range the density vanishes. -/
@[simp]
theorem laplacePDFReal_of_nonpos (hb : b ≤ 0) (μ x : ℝ) : laplacePDFReal μ b x = 0 := by
  rw [laplacePDFReal, ite_eq_right (not_lt.mpr hb)]

/-- For a positive scale the density is the two-sided exponential formula. -/
@[simp]
theorem laplacePDFReal_of_pos (hb : 0 < b) (μ x : ℝ) :
    laplacePDFReal μ b x = (2 * b)⁻¹ * Real.exp (-|x - μ| / b) := by
  rw [laplacePDFReal, ite_eq_left hb]

/-- Outside the valid parameter range the `ℝ≥0∞`-valued density vanishes. -/
@[simp]
theorem laplacePDF_of_nonpos (hb : b ≤ 0) (μ x : ℝ) : laplacePDF μ b x = 0 := by
  rw [laplacePDF_eq_ofReal, laplacePDFReal_of_nonpos hb, ENNReal.ofReal_zero]

/-- For a positive scale the `ℝ≥0∞`-valued density is the two-sided exponential formula. -/
@[simp]
theorem laplacePDF_of_pos (hb : 0 < b) (μ x : ℝ) :
    laplacePDF μ b x = ENNReal.ofReal ((2 * b)⁻¹ * Real.exp (-|x - μ| / b)) := by
  rw [laplacePDF_eq_ofReal, laplacePDFReal_of_pos hb]

/-- The Laplace density is nonnegative at every parameter, valid or not. -/
theorem laplacePDFReal_nonneg (μ b x : ℝ) : 0 ≤ laplacePDFReal μ b x := by
  rw [laplacePDFReal]
  split_ifs with hb
  · exact mul_nonneg (inv_nonneg.mpr (by linarith)) (Real.exp_pos _).le
  · exact le_rfl

/-- For a positive scale the Laplace density is strictly positive everywhere: unlike the gamma or
Pareto densities it has no vanishing tail. -/
theorem laplacePDFReal_pos (hb : 0 < b) (μ x : ℝ) : 0 < laplacePDFReal μ b x := by
  rw [laplacePDFReal_of_pos hb]
  exact mul_pos (inv_pos.mpr (by linarith)) (Real.exp_pos _)

/-- The two Laplace densities agree under `ENNReal.toReal`; the density is never infinite. -/
@[simp]
theorem toReal_laplacePDF (μ b x : ℝ) : (laplacePDF μ b x).toReal = laplacePDFReal μ b x :=
  ENNReal.toReal_ofReal (laplacePDFReal_nonneg μ b x)

/-- The real-valued Laplace density is measurable. -/
@[fun_prop]
theorem measurable_laplacePDFReal (μ b : ℝ) : Measurable (laplacePDFReal μ b) := by
  by_cases hb : 0 < b
  · have h : laplacePDFReal μ b = fun y => (2 * b)⁻¹ * Real.exp (-|y - μ| / b) :=
      funext fun y => laplacePDFReal_of_pos hb μ y
    rw [h]
    fun_prop
  · have h : laplacePDFReal μ b = fun _ => (0 : ℝ) :=
      funext fun y => laplacePDFReal_of_nonpos (not_lt.mp hb) μ y
    rw [h]
    exact measurable_const

/-- The `ℝ≥0∞`-valued Laplace density is measurable. -/
@[fun_prop]
theorem measurable_laplacePDF (μ b : ℝ) : Measurable (laplacePDF μ b) :=
  (measurable_laplacePDFReal μ b).ennreal_ofReal

/-- Below the location the absolute value resolves and the density is an exponential factor. -/
private lemma laplacePDFReal_eq_left (hb : 0 < b) {y : ℝ} (hy : y ≤ μ) :
    laplacePDFReal μ b y = (2 * b)⁻¹ * Real.exp (-(μ / b)) * Real.exp (b⁻¹ * y) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hexp : -|y - μ| / b = -(μ / b) + b⁻¹ * y := by
    rw [abs_of_nonpos (sub_nonpos.mpr hy)]
    field_simp
    ring
  rw [laplacePDFReal_of_pos hb, hexp, Real.exp_add, mul_assoc]

/-- Above the location the absolute value resolves and the density is a decaying exponential. -/
private lemma laplacePDFReal_eq_right (hb : 0 < b) {y : ℝ} (hy : μ ≤ y) :
    laplacePDFReal μ b y = (2 * b)⁻¹ * Real.exp (μ / b) * Real.exp (-b⁻¹ * y) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hexp : -|y - μ| / b = μ / b + -b⁻¹ * y := by
    rw [abs_of_nonneg (sub_nonneg.mpr hy)]
    field_simp
    ring
  rw [laplacePDFReal_of_pos hb, hexp, Real.exp_add, mul_assoc]

/-! ### The measure and its total mass -/

/-- The Laplace probability measure with location `μ` and scale `b`.

For `b ≤ 0` this is the zero measure, not a probability measure; see
`laplaceMeasure_of_nonpos`. -/
def laplaceMeasure (μ b : ℝ) : Measure ℝ :=
  volume.withDensity (laplacePDF μ b)

/-- The defining presentation of the Laplace law as a `MeasureTheory.Measure.withDensity`. -/
theorem laplaceMeasure_eq_withDensity (μ b : ℝ) :
    laplaceMeasure μ b = volume.withDensity (laplacePDF μ b) := by
  rw [laplaceMeasure]

/-- Outside the valid parameter range the Laplace law is the zero measure. -/
@[simp]
theorem laplaceMeasure_of_nonpos (hb : b ≤ 0) (μ : ℝ) : laplaceMeasure μ b = 0 := by
  have h : laplacePDF μ b = 0 := by
    funext y
    rw [laplacePDF_eq_ofReal, laplacePDFReal_of_nonpos hb, ENNReal.ofReal_zero]
    rfl
  rw [laplaceMeasure_eq_withDensity, h, withDensity_zero]

/-- The Laplace density is integrable on the whole line for every scale. -/
theorem integrable_laplacePDFReal (μ : ℝ) : Integrable (laplacePDFReal μ b) := by
  by_cases hb : 0 < b
  · rw [← integrableOn_univ, ← Iic_union_Ioi (a := μ)]
    have hIic : IntegrableOn (laplacePDFReal μ b) (Iic μ) := by
      have h : IntegrableOn
          (fun y : ℝ => (2 * b)⁻¹ * Real.exp (-(μ / b)) * Real.exp (b⁻¹ * y)) (Iic μ) :=
        (integrableOn_exp_mul_Iic (inv_pos.mpr hb) μ).const_mul _
      exact h.congr_fun (fun y hy => (laplacePDFReal_eq_left hb hy).symm) measurableSet_Iic
    have hIoi : IntegrableOn (laplacePDFReal μ b) (Ioi μ) := by
      have h : IntegrableOn
          (fun y : ℝ => (2 * b)⁻¹ * Real.exp (μ / b) * Real.exp (-b⁻¹ * y)) (Ioi μ) :=
        (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (inv_pos.mpr hb)) μ).const_mul _
      exact h.congr_fun (fun y (hy : μ < y) => (laplacePDFReal_eq_right hb hy.le).symm)
        measurableSet_Ioi
    exact hIic.union hIoi
  · have hzero : laplacePDFReal μ b = 0 :=
      funext fun y => laplacePDFReal_of_nonpos (not_lt.mp hb) μ y
    rw [hzero]
    exact integrable_zero ℝ ℝ volume

/-- The Laplace density is integrable on every lower half-line. -/
theorem integrableOn_laplacePDFReal_Iic : IntegrableOn (laplacePDFReal μ b) (Iic x) :=
  (integrable_laplacePDFReal (b := b) μ).integrableOn

/-- The Laplace density is integrable on every upper half-line. -/
theorem integrableOn_laplacePDFReal_Ioi : IntegrableOn (laplacePDFReal μ b) (Ioi x) :=
  (integrable_laplacePDFReal (b := b) μ).integrableOn

/-- The mass of a Laplace density below a point at or under its location. -/
theorem integral_laplacePDFReal_Iic (hb : 0 < b) (hx : x ≤ μ) :
    ∫ y in Iic x, laplacePDFReal μ b y = Real.exp ((x - μ) / b) / 2 := by
  have hb0 : b ≠ 0 := hb.ne'
  have hexp : (x - μ) / b = -(μ / b) + b⁻¹ * x := by
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Iic
      (fun y hy => laplacePDFReal_eq_left hb (le_trans hy hx)),
    integral_const_mul, integral_exp_mul_Iic (inv_pos.mpr hb), hexp, Real.exp_add]
  field_simp

/-- The mass of a Laplace density above a point at or over its location. -/
theorem integral_laplacePDFReal_Ioi (hb : 0 < b) (hx : μ ≤ x) :
    ∫ y in Ioi x, laplacePDFReal μ b y = Real.exp (-(x - μ) / b) / 2 := by
  have hb0 : b ≠ 0 := hb.ne'
  have hexp : -(x - μ) / b = μ / b + -b⁻¹ * x := by
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi
      (fun y hy => laplacePDFReal_eq_right hb (le_trans hx hy.le)),
    integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr (inv_pos.mpr hb)), hexp,
    Real.exp_add]
  field_simp

/-- The Laplace density integrates to `1`: the two halves each carry mass `1 / 2`. -/
theorem integral_laplacePDFReal (hb : 0 < b) (μ : ℝ) : ∫ y, laplacePDFReal μ b y = 1 := by
  rw [← integral_add_compl (s := Iic μ) measurableSet_Iic
      (integrable_laplacePDFReal (b := b) μ),
    compl_Iic, integral_laplacePDFReal_Iic hb le_rfl, integral_laplacePDFReal_Ioi hb le_rfl]
  norm_num

/-- The `ℝ≥0∞`-valued Laplace density has total mass `1`. -/
theorem lintegral_laplacePDF_eq_one (hb : 0 < b) (μ : ℝ) : ∫⁻ y, laplacePDF μ b y = 1 := by
  simp_rw [laplacePDF_eq_ofReal]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_laplacePDFReal (b := b) μ)
      (ae_of_all _ fun y => laplacePDFReal_nonneg μ b y),
    integral_laplacePDFReal hb μ, ENNReal.ofReal_one]

/-- **For a positive scale the Laplace law is a probability measure.** -/
theorem isProbabilityMeasure_laplaceMeasure (hb : 0 < b) (μ : ℝ) :
    IsProbabilityMeasure (laplaceMeasure μ b) := by
  constructor
  rw [laplaceMeasure_eq_withDensity, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, lintegral_laplacePDF_eq_one hb μ]

/-! ### Absolute continuity -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with a Laplace law has a density. -/
theorem hasPDF_of_hasLaw_laplaceMeasure (hX : HasLaw X (laplaceMeasure μ b) P) :
    HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_laplacePDF μ b).aemeasurable hX

/-- The density of a Laplace law is `laplacePDF`. -/
theorem pdf_eq_laplacePDF_of_hasLaw_laplaceMeasure (hX : HasLaw X (laplaceMeasure μ b) P) :
    pdf X P volume =ᵐ[volume] laplacePDF μ b :=
  pdf_eq_of_hasLaw_withDensity (measurable_laplacePDF μ b).aemeasurable hX

/-- The Radon–Nikodym derivative of a Laplace law against Lebesgue measure is `laplacePDF`. -/
theorem rnDeriv_laplaceMeasure (μ b : ℝ) :
    (laplaceMeasure μ b).rnDeriv volume =ᵐ[volume] laplacePDF μ b :=
  Measure.rnDeriv_withDensity volume (measurable_laplacePDF μ b)

/-! ### The cumulative distribution function -/

/-- The mass a Laplace law assigns to a measurable set on which its density is integrable. -/
private lemma measureReal_laplaceMeasure {s : Set ℝ} (hs : MeasurableSet s)
    (hint : IntegrableOn (laplacePDFReal μ b) s) :
    (laplaceMeasure μ b).real s = ∫ y in s, laplacePDFReal μ b y := by
  rw [measureReal_def, laplaceMeasure_eq_withDensity, withDensity_apply _ hs]
  simp_rw [laplacePDF_eq_ofReal]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun y => laplacePDFReal_nonneg μ b y),
    ENNReal.toReal_ofReal (integral_nonneg fun y => laplacePDFReal_nonneg μ b y)]

/-- The upper tail of a Laplace law above its location. -/
theorem measureReal_Ioi_laplaceMeasure (hb : 0 < b) (hx : μ ≤ x) :
    (laplaceMeasure μ b).real (Ioi x) = Real.exp (-(x - μ) / b) / 2 := by
  rw [measureReal_laplaceMeasure measurableSet_Ioi integrableOn_laplacePDFReal_Ioi,
    integral_laplacePDFReal_Ioi hb hx]

/-- The lower tail of a Laplace law below its location. -/
theorem measureReal_Iic_laplaceMeasure_of_le (hb : 0 < b) (hx : x ≤ μ) :
    (laplaceMeasure μ b).real (Iic x) = Real.exp ((x - μ) / b) / 2 := by
  rw [measureReal_laplaceMeasure measurableSet_Iic integrableOn_laplacePDFReal_Iic,
    integral_laplacePDFReal_Iic hb hx]

/-- **The cumulative distribution function of the Laplace law.** -/
theorem cdf_laplaceMeasure_eq (hb : 0 < b) (μ x : ℝ) :
    cdf (laplaceMeasure μ b) x =
      if x < μ then Real.exp ((x - μ) / b) / 2 else 1 - Real.exp (-(x - μ) / b) / 2 := by
  have hp : IsProbabilityMeasure (laplaceMeasure μ b) := isProbabilityMeasure_laplaceMeasure hb μ
  rw [cdf_eq_real]
  split_ifs with hx
  · exact measureReal_Iic_laplaceMeasure_of_le hb hx.le
  · rw [← compl_Ioi, measureReal_compl measurableSet_Ioi,
      measureReal_Ioi_laplaceMeasure hb (not_lt.mp hx)]
    simp

/-! ### Moments -/

/-- Euler's integral in the form used below: the `n`-th moment of a decaying exponential on the
positive half-line. -/
private lemma integral_pow_mul_exp_neg_inv_mul_Ioi (hb : 0 < b) (n : ℕ) :
    ∫ y in Ioi (0 : ℝ), y ^ n * Real.exp (-b⁻¹ * y) = n ! * b ^ (n + 1) := by
  have hb' : (0 : ℝ) < b⁻¹ := inv_pos.mpr hb
  have hq : (-1 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := (n : ℝ)) (b := b⁻¹) one_pos hq hb'
  simp only [Real.rpow_one, Real.rpow_natCast, div_one, mul_one] at h
  rw [h, Real.Gamma_nat_eq_factorial, Real.rpow_neg hb'.le, Real.inv_rpow hb.le, inv_inv,
    ← Nat.cast_one, ← Nat.cast_add, Real.rpow_natCast]
  ring

/-- The integrand of `integral_pow_mul_exp_neg_inv_mul_Ioi` is integrable. -/
private lemma integrableOn_pow_mul_exp_neg_inv_mul_Ioi (hb : 0 < b) (n : ℕ) :
    IntegrableOn (fun y : ℝ => y ^ n * Real.exp (-b⁻¹ * y)) (Ioi 0) := by
  have hb' : (0 : ℝ) < b⁻¹ := inv_pos.mpr hb
  have hq : (-1 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n : ℝ)) (b := b⁻¹) hq one_pos hb'
  simpa only [Real.rpow_one, Real.rpow_natCast] using h

/-- An even function integrable on the positive half-line is integrable on the whole line. -/
private lemma integrable_comp_abs {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) :
    Integrable fun y : ℝ => f |y| := by
  have hIoi : IntegrableOn (fun y : ℝ => f |y|) (Ioi 0) :=
    hf.congr_fun (fun y hy => by rw [abs_of_pos hy]) measurableSet_Ioi
  have hIic : IntegrableOn (fun y : ℝ => f |y|) (Iic 0) := by
    have hemb : MeasurableEmbedding fun y : ℝ => -y := (Homeomorph.neg ℝ).measurableEmbedding
    have h := ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      hemb (f := fun u : ℝ => f |u|) (s := Ici (0 : ℝ))).2
      (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hIoi)
    simpa [Function.comp_def, abs_neg] using h
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hIic.union hIoi

/-- Algebraic normalization shared by the absolute-moment value and integrability proofs. -/
private lemma neg_div_eq_neg_inv_mul (t b : ℝ) : -t / b = -b⁻¹ * t := by
  ring

/-- **The absolute central moments of a Laplace law** are `n ! * b ^ n`. -/
theorem integral_pow_abs_sub_laplaceMeasure (hb : 0 < b) (μ : ℝ) (n : ℕ) :
    ∫ y, |y - μ| ^ n ∂laplaceMeasure μ b = n ! * b ^ n := by
  have hb0 : b ≠ 0 := hb.ne'
  rw [laplaceMeasure_eq_withDensity, integral_withDensity_eq_integral_toReal_smul
    (measurable_laplacePDF μ b) (ae_of_all _ fun y => ENNReal.ofReal_lt_top)]
  simp_rw [toReal_laplacePDF, smul_eq_mul]
  calc ∫ y, laplacePDFReal μ b y * |y - μ| ^ n
      = ∫ y, (2 * b)⁻¹ * Real.exp (-|y - μ| / b) * |y - μ| ^ n := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        simp only [laplacePDFReal_of_pos hb]
    _ = ∫ y, (2 * b)⁻¹ * Real.exp (-|y| / b) * |y| ^ n :=
        integral_sub_right_eq_self
          (fun u : ℝ => (2 * b)⁻¹ * Real.exp (-|u| / b) * |u| ^ n) μ
    _ = 2 * ∫ t in Ioi (0 : ℝ), (2 * b)⁻¹ * Real.exp (-t / b) * t ^ n :=
        integral_comp_abs (f := fun t : ℝ => (2 * b)⁻¹ * Real.exp (-t / b) * t ^ n)
    _ = 2 * ∫ t in Ioi (0 : ℝ), (2 * b)⁻¹ * (t ^ n * Real.exp (-b⁻¹ * t)) := by
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        rw [neg_div_eq_neg_inv_mul]
        ring
    _ = 2 * ((2 * b)⁻¹ * ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-b⁻¹ * t)) := by
        rw [integral_const_mul]
    _ = n ! * b ^ n := by
        rw [integral_pow_mul_exp_neg_inv_mul_Ioi hb n]
        field_simp
        ring

/-- The absolute central moments of a Laplace law are finite for every scale. -/
theorem integrable_pow_abs_sub_laplaceMeasure (μ : ℝ) (n : ℕ) :
    Integrable (fun y => |y - μ| ^ n) (laplaceMeasure μ b) := by
  by_cases hb : 0 < b
  · have hb0 : b ≠ 0 := hb.ne'
    rw [laplaceMeasure_eq_withDensity, integrable_withDensity_iff (measurable_laplacePDF μ b)
      (ae_of_all _ fun y => ENNReal.ofReal_lt_top)]
    simp_rw [toReal_laplacePDF]
    have hIoi : IntegrableOn
        (fun t : ℝ => (2 * b)⁻¹ * Real.exp (-t / b) * t ^ n) (Ioi 0) := by
      refine IntegrableOn.congr_fun
        ((integrableOn_pow_mul_exp_neg_inv_mul_Ioi hb n).const_mul ((2 * b)⁻¹))
        (fun t _ => ?_) measurableSet_Ioi
      rw [neg_div_eq_neg_inv_mul]
      ring
    have habs := integrable_comp_abs hIoi
    refine (habs.comp_sub_right μ).congr (ae_of_all _ fun y => ?_)
    simp only [laplacePDFReal_of_pos hb]
    ring
  · simp [laplaceMeasure_of_nonpos (not_lt.mp hb)]

/-- Deviations from the location are integrable against a Laplace law for every scale. -/
theorem integrable_sub_const_laplaceMeasure (μ : ℝ) :
    Integrable (fun y : ℝ => y - μ) (laplaceMeasure μ b) := by
  have h := integrable_pow_abs_sub_laplaceMeasure (b := b) μ 1
  simp only [pow_one] at h
  refine (integrable_norm_iff (by fun_prop)).mp ?_
  simpa [Real.norm_eq_abs] using h

/-- The identity is integrable against a Laplace law for every scale. -/
theorem integrable_id_laplaceMeasure (μ : ℝ) : Integrable id (laplaceMeasure μ b) := by
  by_cases hb : 0 < b
  · have hp : IsProbabilityMeasure (laplaceMeasure μ b) :=
      isProbabilityMeasure_laplaceMeasure hb μ
    have h := (integrable_sub_const_laplaceMeasure (b := b) μ).add (integrable_const μ)
    refine h.congr (ae_of_all _ fun y => ?_)
    simp
  · simp [laplaceMeasure_of_nonpos (not_lt.mp hb)]

/-- **The mean of a Laplace law is its location.** -/
theorem integral_id_laplaceMeasure (hb : 0 < b) (μ : ℝ) :
    ∫ y, y ∂laplaceMeasure μ b = μ := by
  -- After translating by `μ`, the integrand is odd, so reflection invariance makes its integral
  -- zero.
  have hp : IsProbabilityMeasure (laplaceMeasure μ b) := isProbabilityMeasure_laplaceMeasure hb μ
  have hsub : Integrable (fun y : ℝ => y - μ) (laplaceMeasure μ b) :=
    integrable_sub_const_laplaceMeasure (b := b) μ
  have hodd : ∫ y, (y - μ) ∂laplaceMeasure μ b = 0 := by
    rw [laplaceMeasure_eq_withDensity, integral_withDensity_eq_integral_toReal_smul
      (measurable_laplacePDF μ b) (ae_of_all _ fun y => ENNReal.ofReal_lt_top)]
    simp_rw [toReal_laplacePDF, smul_eq_mul]
    have hshift : ∫ y, laplacePDFReal μ b y * (y - μ)
        = ∫ y, (2 * b)⁻¹ * Real.exp (-|y| / b) * y :=
      calc ∫ y, laplacePDFReal μ b y * (y - μ)
          = ∫ y, (2 * b)⁻¹ * Real.exp (-|y - μ| / b) * (y - μ) := by
            refine integral_congr_ae (ae_of_all _ fun y => ?_)
            simp only [laplacePDFReal_of_pos hb]
        _ = ∫ y, (2 * b)⁻¹ * Real.exp (-|y| / b) * y :=
            integral_sub_right_eq_self
              (fun u : ℝ => (2 * b)⁻¹ * Real.exp (-|u| / b) * u) μ
    rw [hshift]
    have hrefl : ∫ y : ℝ, (2 * b)⁻¹ * Real.exp (-|(-y)| / b) * (-y)
        = ∫ y : ℝ, (2 * b)⁻¹ * Real.exp (-|y| / b) * y :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
        (Homeomorph.neg ℝ).measurableEmbedding
        (fun u : ℝ => (2 * b)⁻¹ * Real.exp (-|u| / b) * u)
    simp only [abs_neg, mul_neg] at hrefl
    rw [integral_neg] at hrefl
    linarith
  have : ∫ y, y ∂laplaceMeasure μ b = ∫ y, ((y - μ) + μ) ∂laplaceMeasure μ b := by simp
  rw [this, integral_add hsub (integrable_const μ), hodd, integral_const]
  simp

/-- **The variance of a Laplace law with scale `b` is `2 * b ^ 2`.** -/
theorem variance_id_laplaceMeasure (hb : 0 < b) (μ : ℝ) :
    variance id (laplaceMeasure μ b) = 2 * b ^ 2 := by
  have hp : IsProbabilityMeasure (laplaceMeasure μ b) := isProbabilityMeasure_laplaceMeasure hb μ
  rw [variance_eq_integral (by fun_prop)]
  simp only [id_eq]
  rw [integral_id_laplaceMeasure hb μ]
  have h := integral_pow_abs_sub_laplaceMeasure hb μ 2
  simp only [sq_abs] at h
  rw [h]
  norm_num

/-! ### Measurability in the parameters -/

/-- The Laplace density is measurable jointly in its location, its scale and the point. -/
@[fun_prop]
theorem measurable_uncurry_laplacePDF :
    Measurable fun q : (ℝ × ℝ) × ℝ => laplacePDF q.1.1 q.1.2 q.2 := by
  simp only [laplacePDF, laplacePDFReal]
  refine (Measurable.ite (measurableSet_lt measurable_const measurable_fst.snd) ?_
    measurable_const).ennreal_ofReal
  fun_prop

/-- **The Laplace family is measurable in its parameters**, so it can be packaged as a kernel. -/
@[fun_prop]
theorem measurable_laplaceMeasure : Measurable fun p : ℝ × ℝ => laplaceMeasure p.1 p.2 :=
  measurable_withDensity (μ := volume) measurable_uncurry_laplacePDF

end Probability

end TauCeti
