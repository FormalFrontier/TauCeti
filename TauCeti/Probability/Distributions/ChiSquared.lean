/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Dirac
public import TauCeti.Probability.Distributions.Gamma.Cdf
public import TauCeti.Probability.Distributions.Measurability
public import TauCeti.Probability.Density
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# The chi-squared distribution

The chi-squared law with `k` real degrees of freedom is the Gamma law with shape `k / 2` and
rate `1 / 2`. This file makes the boundary behavior part of the definition: degree zero is the
Dirac mass at zero, while a negative degree gives the zero measure. For positive degree it derives
the density, cumulative distribution function, mean, variance, exponential-integrability domain,
moment-generating function, and cumulant-generating function from the Gamma API. It also proves
additivity under convolution for nonnegative degrees and measurability in the degree parameter.

The positive-degree characteristic function is deferred to the generic Gamma characteristic
function: that generic theorem is the only remaining prerequisite for the corresponding
chi-squared formula. At degree zero, the characteristic function is proved here directly.

## Main definitions

* `TauCeti.Probability.chiSquaredMeasure` — the chi-squared law, totalized on every real degree;
* `TauCeti.Probability.chiSquaredPDFReal` and `TauCeti.Probability.chiSquaredPDF` — its density for
  positive degree, extended by zero otherwise.

## Main results

* `chiSquaredMeasure_eq_gammaMeasure` — the positive-degree identification with a Gamma law;
* `chiSquaredMeasure_zero` and `chiSquaredMeasure_of_neg` — the boundary and invalid cases;
* `chiSquaredMeasure_eq_withDensity`, `hasPDF_of_hasLaw_chiSquaredMeasure`, and
  `rnDeriv_chiSquaredMeasure` — the density API for positive degree;
* `cdf_chiSquaredMeasure_eq`, `integral_id_chiSquaredMeasure`, and
  `variance_id_chiSquaredMeasure` — the cdf and first two moments;
* `integrableExpSet_id_chiSquaredMeasure`, `mgf_id_chiSquaredMeasure`, and
  `cgf_id_chiSquaredMeasure` — the positive-degree exponential transforms;
* `chiSquaredMeasure_conv_chiSquaredMeasure` — additivity of nonnegative degrees;
* `measurable_chiSquaredMeasure` — parameter measurability.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 3, **Chi-squared**.
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley, 1994, ch. 18.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

open scoped ENNReal NNReal

namespace TauCeti

namespace Probability

variable {k l x t : ℝ}

/-! ### Definition and parameter cases -/

/-- The chi-squared measure with `k` real degrees of freedom.

For `0 < k` this is the Gamma law with shape `k / 2` and rate `1 / 2`. At `k = 0` it is the
Dirac mass at zero, so degree addition retains its convolution unit. For `k < 0` it is the zero
measure. -/
def chiSquaredMeasure (k : ℝ) : Measure ℝ :=
  if k = 0 then Measure.dirac 0 else if 0 < k then gammaMeasure (k / 2) (1 / 2) else 0

/-- A positive-degree chi-squared law is the corresponding Gamma law. -/
@[simp]
theorem chiSquaredMeasure_eq_gammaMeasure (hk : 0 < k) :
    chiSquaredMeasure k = gammaMeasure (k / 2) (1 / 2) := by
  rw [chiSquaredMeasure, ite_eq_right hk.ne', ite_eq_left hk]

/-- The chi-squared law with zero degrees of freedom is concentrated at zero. -/
@[simp]
theorem chiSquaredMeasure_zero : chiSquaredMeasure 0 = Measure.dirac 0 := by
  rw [chiSquaredMeasure, ite_eq_left rfl]

/-- A negative number of degrees of freedom gives the zero measure. -/
@[simp]
theorem chiSquaredMeasure_of_neg (hk : k < 0) : chiSquaredMeasure k = 0 := by
  rw [chiSquaredMeasure, ite_eq_right hk.ne, ite_eq_right (not_lt.mpr hk.le)]

/-- A positive-degree chi-squared law is a probability measure. -/
theorem isProbabilityMeasure_chiSquaredMeasure (hk : 0 < k) :
    IsProbabilityMeasure (chiSquaredMeasure k) := by
  rw [chiSquaredMeasure_eq_gammaMeasure hk]
  exact isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)

/-- The zero-degree chi-squared law is also a probability measure. -/
theorem isProbabilityMeasure_chiSquaredMeasure_zero :
    IsProbabilityMeasure (chiSquaredMeasure 0) := by
  rw [chiSquaredMeasure_zero]
  infer_instance

/-- Every chi-squared law of nonnegative degree is a probability measure. -/
theorem isProbabilityMeasure_chiSquaredMeasure_of_nonneg (hk : 0 ≤ k) :
    IsProbabilityMeasure (chiSquaredMeasure k) := by
  rcases hk.eq_or_lt with rfl | hk
  · exact isProbabilityMeasure_chiSquaredMeasure_zero
  · exact isProbabilityMeasure_chiSquaredMeasure hk

/-! ### Density -/

/-- The real-valued chi-squared density. It is the Gamma density for positive degree and zero for
nonpositive degree. At degree zero the measure is singular, so this function is not a density for
that boundary law. -/
def chiSquaredPDFReal (k x : ℝ) : ℝ :=
  if 0 < k then gammaPDFReal (k / 2) (1 / 2) x else 0

/-- The chi-squared density as an `ℝ≥0∞`-valued function. -/
def chiSquaredPDF (k x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (chiSquaredPDFReal k x)

/-- For positive degree, the real chi-squared density is the specialized Gamma density. -/
@[simp]
theorem chiSquaredPDFReal_of_pos (hk : 0 < k) (x : ℝ) :
    chiSquaredPDFReal k x = gammaPDFReal (k / 2) (1 / 2) x := by
  rw [chiSquaredPDFReal, ite_eq_left hk]

/-- For nonpositive degree, the real-valued density is zero. -/
@[simp]
theorem chiSquaredPDFReal_of_nonpos (hk : k ≤ 0) (x : ℝ) : chiSquaredPDFReal k x = 0 := by
  rw [chiSquaredPDFReal, ite_eq_right (not_lt.mpr hk)]

/-- For positive degree, the `ℝ≥0∞`-valued chi-squared density is the specialized Gamma density. -/
@[simp]
theorem chiSquaredPDF_of_pos (hk : 0 < k) (x : ℝ) :
    chiSquaredPDF k x = gammaPDF (k / 2) (1 / 2) x := by
  rw [chiSquaredPDF, chiSquaredPDFReal_of_pos hk, gammaPDF]

/-- For nonpositive degree, the `ℝ≥0∞`-valued density is zero. -/
@[simp]
theorem chiSquaredPDF_of_nonpos (hk : k ≤ 0) (x : ℝ) : chiSquaredPDF k x = 0 := by
  rw [chiSquaredPDF, chiSquaredPDFReal_of_nonpos hk, ENNReal.ofReal_zero]

/-- The closed formula for the real-valued density of a positive-degree chi-squared law. -/
theorem chiSquaredPDFReal_eq (hk : 0 < k) (x : ℝ) :
    chiSquaredPDFReal k x =
      if 0 ≤ x then
        (1 / 2 : ℝ) ^ (k / 2) / Real.Gamma (k / 2) * x ^ (k / 2 - 1) *
          Real.exp (-((1 / 2 : ℝ) * x))
      else 0 := by
  rw [chiSquaredPDFReal_of_pos hk, gammaPDFReal]

/-- The closed formula for the `ℝ≥0∞`-valued density of a positive-degree chi-squared law. -/
theorem chiSquaredPDF_eq (hk : 0 < k) (x : ℝ) :
    chiSquaredPDF k x =
      ENNReal.ofReal
        (if 0 ≤ x then
          (1 / 2 : ℝ) ^ (k / 2) / Real.Gamma (k / 2) * x ^ (k / 2 - 1) *
            Real.exp (-((1 / 2 : ℝ) * x))
        else 0) := by
  rw [chiSquaredPDF, chiSquaredPDFReal_eq hk]

/-- The real-valued chi-squared density is nonnegative for every parameter. -/
theorem chiSquaredPDFReal_nonneg (k x : ℝ) : 0 ≤ chiSquaredPDFReal k x := by
  rcases le_or_gt k 0 with hk | hk
  · rw [chiSquaredPDFReal_of_nonpos hk]
  · rw [chiSquaredPDFReal_of_pos hk]
    exact gammaPDFReal_nonneg (by positivity) (by norm_num) x

/-- The real-valued chi-squared density is measurable. -/
@[fun_prop]
theorem measurable_chiSquaredPDFReal (k : ℝ) : Measurable (chiSquaredPDFReal k) := by
  rcases le_or_gt k 0 with hk | hk
  · have h : chiSquaredPDFReal k = 0 := funext (chiSquaredPDFReal_of_nonpos hk)
    rw [h]
    fun_prop
  · have h : chiSquaredPDFReal k = gammaPDFReal (k / 2) (1 / 2) :=
      funext (chiSquaredPDFReal_of_pos hk)
    rw [h]
    fun_prop

/-- The `ℝ≥0∞`-valued chi-squared density is measurable. -/
@[fun_prop]
theorem measurable_chiSquaredPDF (k : ℝ) : Measurable (chiSquaredPDF k) := by
  unfold chiSquaredPDF
  exact (measurable_chiSquaredPDFReal k).ennreal_ofReal

/-- A positive-degree chi-squared law is Lebesgue measure weighted by its density. -/
theorem chiSquaredMeasure_eq_withDensity (hk : 0 < k) :
    chiSquaredMeasure k = volume.withDensity (chiSquaredPDF k) := by
  rw [chiSquaredMeasure_eq_gammaMeasure hk, gammaMeasure]
  congr 1
  exact funext fun x ↦ (chiSquaredPDF_of_pos hk x).symm

/-- A random variable with a positive-degree chi-squared law has a density. -/
theorem hasPDF_of_hasLaw_chiSquaredMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hk : 0 < k) (hX : HasLaw X (chiSquaredMeasure k) P) : HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_chiSquaredPDF k).aemeasurable
    (by rwa [chiSquaredMeasure_eq_withDensity hk] at hX)

/-- The density of a positive-degree chi-squared random variable is `chiSquaredPDF`. -/
theorem pdf_eq_chiSquaredPDF_of_hasLaw_chiSquaredMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hk : 0 < k) (hX : HasLaw X (chiSquaredMeasure k) P) :
    pdf X P =ᵐ[volume] chiSquaredPDF k :=
  pdf_eq_of_hasLaw_withDensity (measurable_chiSquaredPDF k).aemeasurable
    (by rwa [chiSquaredMeasure_eq_withDensity hk] at hX)

/-- The Radon--Nikodym derivative of a positive-degree chi-squared law is its density. -/
theorem rnDeriv_chiSquaredMeasure (hk : 0 < k) :
    (chiSquaredMeasure k).rnDeriv volume =ᵐ[volume] chiSquaredPDF k := by
  rw [chiSquaredMeasure_eq_withDensity hk]
  exact Measure.rnDeriv_withDensity volume (measurable_chiSquaredPDF k)

/-! ### Positive-degree formulas -/

/-- The cdf of a positive-degree chi-squared law is the regularized Gamma function. -/
@[simp]
theorem cdf_chiSquaredMeasure_eq (hk : 0 < k) (x : ℝ) :
    cdf (chiSquaredMeasure k) x = regularizedGamma (k / 2) (x / 2) := by
  rw [chiSquaredMeasure_eq_gammaMeasure hk,
    cdf_gammaMeasure_eq (by positivity) (by norm_num)]
  congr 1
  ring

/-- The mean of a positive-degree chi-squared law is its degree. -/
@[simp]
theorem integral_id_chiSquaredMeasure (hk : 0 < k) :
    ∫ x, x ∂chiSquaredMeasure k = k := by
  rw [chiSquaredMeasure_eq_gammaMeasure hk,
    integral_id_gammaMeasure (by positivity) (by norm_num)]
  ring

/-- The variance of a positive-degree chi-squared law is twice its degree. -/
@[simp]
theorem variance_id_chiSquaredMeasure (hk : 0 < k) :
    variance id (chiSquaredMeasure k) = 2 * k := by
  rw [chiSquaredMeasure_eq_gammaMeasure hk,
    variance_id_gammaMeasure (by positivity) (by norm_num)]
  ring

/-- The exponential moments of a positive-degree chi-squared law exist exactly below `1 / 2`. -/
@[simp]
theorem integrableExpSet_id_chiSquaredMeasure (hk : 0 < k) :
    integrableExpSet id (chiSquaredMeasure k) = Iio (1 / 2 : ℝ) := by
  rw [chiSquaredMeasure_eq_gammaMeasure hk,
    integrableExpSet_id_gammaMeasure (by positivity) (by norm_num)]

/-- The moment-generating function of a positive-degree chi-squared law. -/
@[simp]
theorem mgf_id_chiSquaredMeasure (hk : 0 < k) (ht : t < 1 / 2) :
    mgf id (chiSquaredMeasure k) t = (1 - 2 * t) ^ (-(k / 2)) := by
  rw [chiSquaredMeasure_eq_gammaMeasure hk,
    mgf_id_gammaMeasure (by positivity) (by norm_num) ht]
  congr 2
  ring

/-- The cumulant-generating function of a positive-degree chi-squared law. -/
@[simp]
theorem cgf_id_chiSquaredMeasure (hk : 0 < k) (ht : t < 1 / 2) :
    cgf id (chiSquaredMeasure k) t = -(k / 2) * Real.log (1 - 2 * t) := by
  rw [chiSquaredMeasure_eq_gammaMeasure hk,
    cgf_id_gammaMeasure (by positivity) (by norm_num) ht]
  congr 2
  ring

/-! ### Degree zero -/

/-- The cdf at degree zero is the step function of the Dirac mass at zero. -/
@[simp]
theorem cdf_chiSquaredMeasure_zero (x : ℝ) :
    cdf (chiSquaredMeasure 0) x = if 0 ≤ x then 1 else 0 := by
  rw [chiSquaredMeasure_zero, cdf_dirac]

/-- The zero-degree chi-squared law has mean zero. -/
@[simp]
theorem integral_id_chiSquaredMeasure_zero : ∫ x, x ∂chiSquaredMeasure 0 = 0 := by
  rw [chiSquaredMeasure_zero, integral_dirac]

/-- The zero-degree chi-squared law has variance zero. -/
@[simp]
theorem variance_id_chiSquaredMeasure_zero : variance id (chiSquaredMeasure 0) = 0 := by
  rw [chiSquaredMeasure_zero, variance_dirac]

/-- Every exponential moment exists at degree zero. -/
@[simp]
theorem integrableExpSet_id_chiSquaredMeasure_zero :
    integrableExpSet id (chiSquaredMeasure 0) = Set.univ := by
  rw [chiSquaredMeasure_zero, integrableExpSet_dirac]

/-- The moment-generating function is identically one at degree zero. -/
@[simp]
theorem mgf_id_chiSquaredMeasure_zero (t : ℝ) : mgf id (chiSquaredMeasure 0) t = 1 := by
  rw [chiSquaredMeasure_zero, mgf_dirac']
  simp

/-- The cumulant-generating function is identically zero at degree zero. -/
@[simp]
theorem cgf_id_chiSquaredMeasure_zero (t : ℝ) : cgf id (chiSquaredMeasure 0) t = 0 := by
  rw [chiSquaredMeasure_zero, cgf_dirac']
  simp

/-- The characteristic function is identically one at degree zero. -/
@[simp]
theorem charFun_chiSquaredMeasure_zero (t : ℝ) :
    charFun (chiSquaredMeasure 0) t = 1 := by
  rw [chiSquaredMeasure_zero, charFun_dirac]
  simp

/-! ### Additivity and parameter measurability -/

/-- Convolution adds nonnegative chi-squared degrees of freedom. The degree-zero law is the
convolution unit, while positive degrees reduce to additivity of Gamma shapes. -/
@[simp]
theorem chiSquaredMeasure_conv_chiSquaredMeasure (hk : 0 ≤ k) (hl : 0 ≤ l) :
    chiSquaredMeasure k ∗ chiSquaredMeasure l = chiSquaredMeasure (k + l) := by
  let _ := isProbabilityMeasure_chiSquaredMeasure_of_nonneg hk
  let _ := isProbabilityMeasure_chiSquaredMeasure_of_nonneg hl
  rcases hk.eq_or_lt with rfl | hk
  · simp
  rcases hl.eq_or_lt with rfl | hl
  · simp
  rw [chiSquaredMeasure_eq_gammaMeasure hk, chiSquaredMeasure_eq_gammaMeasure hl,
    gammaMeasure_conv_gammaMeasure (by positivity) (by positivity) (by norm_num),
    chiSquaredMeasure_eq_gammaMeasure (add_pos hk hl)]
  congr 2
  ring

/-- The family of chi-squared measures is measurable in its real degree parameter. -/
@[fun_prop]
theorem measurable_chiSquaredMeasure : Measurable chiSquaredMeasure := by
  -- Rewrite the sealed family definition as a function before applying piecewise measurability.
  rw [show chiSquaredMeasure = fun k : ℝ =>
    if k = 0 then Measure.dirac 0 else if 0 < k then gammaMeasure (k / 2) (1 / 2) else 0 from rfl]
  refine Measurable.ite (measurableSet_singleton 0) measurable_const
    (Measurable.ite ?_ ?_ measurable_const)
  · exact measurableSet_Ioi
  · let f : ℝ → ℝ × ℝ := fun k ↦ (k / 2, 1 / 2)
    have hf : Measurable f :=
      (measurable_id.div_const 2).prodMk
        (measurable_const : Measurable fun _ : ℝ ↦ (1 / 2 : ℝ))
    have h : Measurable ((fun p : ℝ × ℝ ↦ gammaMeasure p.1 p.2) ∘ f) :=
      measurable_gammaMeasure.comp hf
    -- Naming the composition avoids an expensive definitional-equality search through the Giry
    -- measurable-space instance.
    rw [show ((fun p : ℝ × ℝ ↦ gammaMeasure p.1 p.2) ∘ f) =
      (fun k : ℝ ↦ gammaMeasure (k / 2) (1 / 2)) from rfl] at h
    exact h

/-- Two degrees of freedom give the exponential law of rate `1 / 2`. -/
@[simp]
theorem chiSquaredMeasure_two : chiSquaredMeasure 2 = expMeasure (1 / 2) := by
  rw [chiSquaredMeasure_eq_gammaMeasure (by norm_num), expMeasure]
  norm_num

end Probability

end TauCeti
