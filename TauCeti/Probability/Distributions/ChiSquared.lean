/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Dirac
public import TauCeti.Probability.Distributions.Gamma.Cdf
public import TauCeti.Probability.Distributions.Measurability
public import TauCeti.Probability.Distributions.PDFInstances

/-!
# The chi-squared distribution

The chi-squared law with `k` degrees of freedom is the Gamma law with shape `k / 2` and rate
`1 / 2`. This file makes that specialization available as a total measurable family. Positive
degrees of freedom give the usual absolutely continuous law, zero degrees of freedom give the
Dirac measure at zero, and negative degrees of freedom give the zero measure.

For positive `k`, the file supplies the density, probability-measure instance, cdf, mean,
variance, exact exponential-integrability domain, moment-generating function, cumulant-generating
function, and additivity in the degrees of freedom. The corresponding formulas at `k = 0` are
recorded separately because that law is singular rather than density-defined.

The characteristic function at positive degree is deliberately not proved here: it is the direct
specialization of the Gamma characteristic function currently tracked separately by the same
roadmap. The zero-degree characteristic function needs no such dependency and is included.

## Main definitions and results

* `chiSquaredPDFReal`, `chiSquaredPDF`, and `chiSquaredMeasure` define the density and law;
* `isProbabilityMeasure_chiSquaredMeasure` covers every nonnegative degree;
* `cdf_chiSquaredMeasure_eq`, `integral_id_chiSquaredMeasure`, and
  `variance_id_chiSquaredMeasure` give the elementary distributional formulas;
* `integrableExpSet_id_chiSquaredMeasure`, `mgf_id_chiSquaredMeasure`, and
  `cgf_id_chiSquaredMeasure` give the exponential transforms at positive degree;
* `chiSquaredMeasure_conv_chiSquaredMeasure` adds nonnegative degrees of freedom;
* `measurable_chiSquaredMeasure` makes the family available for kernels.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 3, **Chi-squared**.
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley, 1994, chapter 18.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory

namespace TauCeti

namespace Probability

variable {k l t x : ℝ}

/-! ### Density and measure -/

/-- The real-valued chi-squared density with `k` degrees of freedom.

It is the Gamma density with shape `k / 2` and rate `1 / 2` when `k` is positive, and zero for
nonpositive `k`. In particular, this density does not represent the singular law at `k = 0`. -/
def chiSquaredPDFReal (k x : ℝ) : ℝ :=
  if 0 < k then gammaPDFReal (k / 2) (1 / 2) x else 0

/-- The chi-squared density, valued in `ℝ≥0∞`. -/
def chiSquaredPDF (k x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (chiSquaredPDFReal k x)

/-- The chi-squared law with `k` degrees of freedom.

It is `gammaMeasure (k / 2) (1 / 2)` for `0 < k`, `Measure.dirac 0` for `k = 0`, and the zero
measure for `k < 0`. -/
def chiSquaredMeasure (k : ℝ) : Measure ℝ :=
  if k = 0 then Measure.dirac 0 else if 0 < k then gammaMeasure (k / 2) (1 / 2) else 0

/-- At positive degree, the real chi-squared density is the corresponding Gamma density. -/
@[simp]
theorem chiSquaredPDFReal_of_pos (hk : 0 < k) (x : ℝ) :
    chiSquaredPDFReal k x = gammaPDFReal (k / 2) (1 / 2) x := by
  simp [chiSquaredPDFReal, hk]

/-- At positive degree, the `ℝ≥0∞`-valued chi-squared density is the corresponding Gamma
density. -/
@[simp]
theorem chiSquaredPDF_of_pos (hk : 0 < k) (x : ℝ) :
    chiSquaredPDF k x = gammaPDF (k / 2) (1 / 2) x := by
  simp [chiSquaredPDF, chiSquaredPDFReal, gammaPDF, hk]

/-- The explicit real chi-squared density at positive degree. -/
theorem chiSquaredPDFReal_eq (hk : 0 < k) (x : ℝ) :
    chiSquaredPDFReal k x =
      if 0 ≤ x then
        (1 / 2 : ℝ) ^ (k / 2) / Real.Gamma (k / 2) * x ^ (k / 2 - 1) *
          Real.exp (-((1 / 2 : ℝ) * x))
      else 0 := by
  simp [chiSquaredPDFReal, gammaPDFReal, hk]

/-- The chi-squared density vanishes at nonpositive degree. -/
@[simp]
theorem chiSquaredPDFReal_of_nonpos (hk : k ≤ 0) (x : ℝ) : chiSquaredPDFReal k x = 0 := by
  simp [chiSquaredPDFReal, not_lt.mpr hk]

/-- The `ℝ≥0∞`-valued chi-squared density vanishes at nonpositive degree. -/
@[simp]
theorem chiSquaredPDF_of_nonpos (hk : k ≤ 0) (x : ℝ) : chiSquaredPDF k x = 0 := by
  simp [chiSquaredPDF, hk]

/-- A positive-degree chi-squared law is its defining Gamma law. -/
@[simp]
theorem chiSquaredMeasure_of_pos (hk : 0 < k) :
    chiSquaredMeasure k = gammaMeasure (k / 2) (1 / 2) := by
  simp [chiSquaredMeasure, hk, hk.ne']

/-- The chi-squared law at zero degrees of freedom is concentrated at zero. -/
@[simp]
theorem chiSquaredMeasure_zero : chiSquaredMeasure 0 = Measure.dirac 0 := by
  simp [chiSquaredMeasure]

/-- A negative degree of freedom gives the zero measure. -/
@[simp]
theorem chiSquaredMeasure_of_neg (hk : k < 0) : chiSquaredMeasure k = 0 := by
  rw [chiSquaredMeasure, ite_eq_right hk.ne, ite_eq_right (not_lt.mpr hk.le)]

/-- At positive degree, the chi-squared law has density `chiSquaredPDF`. -/
theorem chiSquaredMeasure_eq_withDensity (hk : 0 < k) :
    chiSquaredMeasure k = volume.withDensity (chiSquaredPDF k) := by
  rw [chiSquaredMeasure_of_pos hk, gammaMeasure]
  congr 1
  funext x
  exact (chiSquaredPDF_of_pos hk x).symm

/-- The chi-squared density is measurable for every degree of freedom. -/
theorem measurable_chiSquaredPDF (k : ℝ) : Measurable (chiSquaredPDF k) := by
  by_cases hk : 0 < k
  · have heq : chiSquaredPDF k = gammaPDF (k / 2) (1 / 2) :=
      funext (chiSquaredPDF_of_pos hk)
    rw [heq]
    exact measurable_gammaPDF (k / 2) (1 / 2)
  · have heq : chiSquaredPDF k = 0 := by
      funext x
      simp [chiSquaredPDF, chiSquaredPDFReal, hk]
    rw [heq]
    exact measurable_const

/-! ### Probability measures and densities -/

/-- A chi-squared law with any nonnegative degree of freedom is a probability measure. -/
theorem isProbabilityMeasure_chiSquaredMeasure (hk : 0 ≤ k) :
    IsProbabilityMeasure (chiSquaredMeasure k) := by
  rcases hk.eq_or_lt with rfl | hk
  · rw [chiSquaredMeasure_zero]
    infer_instance
  · rw [chiSquaredMeasure_of_pos hk]
    exact isProbabilityMeasure_gammaMeasure (half_pos hk) (by norm_num)

/-- The zero-degree chi-squared law is a probability measure, despite being singular. -/
theorem isProbabilityMeasure_chiSquaredMeasure_zero :
    IsProbabilityMeasure (chiSquaredMeasure 0) :=
  isProbabilityMeasure_chiSquaredMeasure le_rfl

/-- A variable with a positive-degree chi-squared law has a density. -/
theorem hasPDF_of_hasLaw_chiSquaredMeasure {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {X : Omega → ℝ} (hk : 0 < k)
    (hX : HasLaw X (chiSquaredMeasure k) P) : HasPDF X P := by
  apply hasPDF_of_hasLaw_withDensity (measurable_chiSquaredPDF k).aemeasurable
  simpa only [chiSquaredMeasure_eq_withDensity hk] using hX

/-- The density of a variable with a positive-degree chi-squared law is `chiSquaredPDF`. -/
theorem pdf_eq_chiSquaredPDF_of_hasLaw_chiSquaredMeasure {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {X : Omega → ℝ} (hk : 0 < k)
    (hX : HasLaw X (chiSquaredMeasure k) P) : pdf X P =ᵐ[volume] chiSquaredPDF k := by
  apply pdf_eq_of_hasLaw_withDensity (measurable_chiSquaredPDF k).aemeasurable
  simpa only [chiSquaredMeasure_eq_withDensity hk] using hX

/-- The Radon–Nikodym derivative of a positive-degree chi-squared law is its density. -/
theorem rnDeriv_chiSquaredMeasure (hk : 0 < k) :
    (chiSquaredMeasure k).rnDeriv volume =ᵐ[volume] chiSquaredPDF k := by
  rw [chiSquaredMeasure_eq_withDensity hk]
  exact Measure.rnDeriv_withDensity volume (measurable_chiSquaredPDF k)

/-- The Radon–Nikodym derivative of the singular zero-degree law vanishes almost everywhere. -/
theorem rnDeriv_chiSquaredMeasure_zero :
    (chiSquaredMeasure 0).rnDeriv volume =ᵐ[volume] 0 := by
  rw [chiSquaredMeasure_zero]
  exact Measure.rnDeriv_eq_zero_of_mutuallySingular
    (mutuallySingular_dirac (0 : ℝ) volume) Measure.AbsolutelyContinuous.rfl

/-! ### Cdf, moments, and transforms -/

/-- The cdf of a positive-degree chi-squared law is the regularized Gamma function. -/
@[simp]
theorem cdf_chiSquaredMeasure_eq (hk : 0 < k) (x : ℝ) :
    cdf (chiSquaredMeasure k) x = regularizedGamma (k / 2) (x / 2) := by
  rw [chiSquaredMeasure_of_pos hk]
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using
    TauCeti.cdf_gammaMeasure_eq (a := k / 2) (r := 1 / 2) (half_pos hk) (by norm_num) x

/-- The cdf of the zero-degree chi-squared law is the step function at zero. -/
@[simp]
theorem cdf_chiSquaredMeasure_zero (x : ℝ) :
    cdf (chiSquaredMeasure 0) x = if 0 ≤ x then 1 else 0 := by
  rw [chiSquaredMeasure_zero, TauCeti.cdf_dirac]

/-- The mean of a positive-degree chi-squared law is its degree of freedom. -/
@[simp]
theorem integral_id_chiSquaredMeasure (hk : 0 < k) :
    ∫ x, x ∂chiSquaredMeasure k = k := by
  rw [chiSquaredMeasure_of_pos hk,
    TauCeti.integral_id_gammaMeasure (half_pos hk) (by norm_num)]
  ring

/-- The zero-degree chi-squared law has mean zero. -/
@[simp]
theorem integral_id_chiSquaredMeasure_zero : ∫ x, x ∂chiSquaredMeasure 0 = 0 := by
  rw [chiSquaredMeasure_zero, integral_dirac]

/-- The variance of a positive-degree chi-squared law is twice its degree of freedom. -/
@[simp]
theorem variance_id_chiSquaredMeasure (hk : 0 < k) :
    variance id (chiSquaredMeasure k) = 2 * k := by
  rw [chiSquaredMeasure_of_pos hk,
    TauCeti.variance_id_gammaMeasure (half_pos hk) (by norm_num)]
  ring

/-- The zero-degree chi-squared law has variance zero. -/
@[simp]
theorem variance_id_chiSquaredMeasure_zero : variance id (chiSquaredMeasure 0) = 0 := by
  rw [chiSquaredMeasure_zero, variance_dirac]

/-- The exponential moments of a positive-degree chi-squared law exist exactly below `1 / 2`. -/
@[simp]
theorem integrableExpSet_id_chiSquaredMeasure (hk : 0 < k) :
    integrableExpSet id (chiSquaredMeasure k) = Iio (1 / 2 : ℝ) := by
  rw [chiSquaredMeasure_of_pos hk,
    TauCeti.integrableExpSet_id_gammaMeasure (half_pos hk) (by norm_num)]

/-- Every exponential moment exists for the zero-degree chi-squared law. -/
@[simp]
theorem integrableExpSet_id_chiSquaredMeasure_zero :
    integrableExpSet id (chiSquaredMeasure 0) = univ := by
  rw [chiSquaredMeasure_zero]
  exact TauCeti.integrableExpSet_dirac _ _

/-- The moment-generating function of a positive-degree chi-squared law. -/
@[simp]
theorem mgf_id_chiSquaredMeasure (hk : 0 < k) (ht : t < 1 / 2) :
    mgf id (chiSquaredMeasure k) t = (1 - 2 * t) ^ (-(k / 2)) := by
  rw [chiSquaredMeasure_of_pos hk,
    TauCeti.mgf_id_gammaMeasure (half_pos hk) (by norm_num) ht]
  congr 2
  ring

/-- The moment-generating function of the zero-degree chi-squared law is one. -/
@[simp]
theorem mgf_id_chiSquaredMeasure_zero (t : ℝ) : mgf id (chiSquaredMeasure 0) t = 1 := by
  rw [chiSquaredMeasure_zero, mgf_dirac']
  simp

/-- The cumulant-generating function of a positive-degree chi-squared law is the real logarithm
of its moment-generating function. -/
@[simp]
theorem cgf_id_chiSquaredMeasure (hk : 0 < k) (ht : t < 1 / 2) :
    cgf id (chiSquaredMeasure k) t = Real.log ((1 - 2 * t) ^ (-(k / 2))) := by
  rw [cgf, mgf_id_chiSquaredMeasure hk ht]

/-- The cumulant-generating function of the zero-degree chi-squared law is zero. -/
@[simp]
theorem cgf_id_chiSquaredMeasure_zero (t : ℝ) : cgf id (chiSquaredMeasure 0) t = 0 := by
  rw [chiSquaredMeasure_zero, TauCeti.cgf_dirac']
  simp

/-- The characteristic function of the zero-degree chi-squared law is one. -/
@[simp]
theorem charFun_chiSquaredMeasure_zero (t : ℝ) : charFun (chiSquaredMeasure 0) t = 1 := by
  rw [chiSquaredMeasure_zero, charFun_dirac]
  simp

/-! ### Additivity and parameter measurability -/

/-- Convolution adds nonnegative degrees of freedom, including the Dirac boundary at zero. -/
@[simp]
theorem chiSquaredMeasure_conv_chiSquaredMeasure (hk : 0 ≤ k) (hl : 0 ≤ l) :
    chiSquaredMeasure k ∗ chiSquaredMeasure l = chiSquaredMeasure (k + l) := by
  let _ := isProbabilityMeasure_chiSquaredMeasure hk
  let _ := isProbabilityMeasure_chiSquaredMeasure hl
  rcases hk.eq_or_lt with rfl | hk
  · simp
  rcases hl.eq_or_lt with rfl | hl
  · simp
  rw [chiSquaredMeasure_of_pos hk, chiSquaredMeasure_of_pos hl,
    chiSquaredMeasure_of_pos (add_pos hk hl),
    TauCeti.gammaMeasure_conv_gammaMeasure (half_pos hk) (half_pos hl) (by norm_num)]
  congr 2
  ring

/-- Two degrees of freedom give the exponential law of rate `1 / 2`. -/
@[simp]
theorem chiSquaredMeasure_two : chiSquaredMeasure 2 = expMeasure (1 / 2) := by
  rw [chiSquaredMeasure_of_pos (by norm_num)]
  norm_num [expMeasure]

/-- The chi-squared family is measurable in its degree of freedom. -/
theorem measurable_chiSquaredMeasure : Measurable chiSquaredMeasure := by
  unfold chiSquaredMeasure
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  refine Measurable.ite (measurableSet_lt measurable_const measurable_id) ?_ measurable_const
  have heq : (fun k : ℝ => gammaMeasure (k / 2) (1 / 2)) =
      (fun p : ℝ × ℝ => gammaMeasure p.1 p.2) ∘ fun k : ℝ => (k / 2, 1 / 2) := rfl
  rw [heq]
  exact measurable_gammaMeasure.comp ((measurable_id.div_const 2).prodMk measurable_const)

end Probability

end TauCeti
