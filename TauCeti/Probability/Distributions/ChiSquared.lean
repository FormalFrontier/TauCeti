/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.Dirac
public import TauCeti.Probability.Distributions.Gamma.Cdf
public import TauCeti.Probability.Distributions.Gamma.CharFun
public import TauCeti.Probability.Distributions.Measurability
public import TauCeti.Probability.Distributions.PDFInstances

/-!
# The chi-squared distribution

The chi-squared law with `k` degrees of freedom is the gamma law of shape `k / 2` and rate `1 / 2`.
This file defines it for every real `k`, records its three parameter regimes, and transports the
elementary theory of the gamma law across the bridge: the density, the cumulative distribution
function, the mean `k`, the variance `2 * k`, the exponential-moment domain `Set.Iio (1 / 2)`, the
moment- and cumulant-generating functions there, and the characteristic function. It also proves
that the family is additive in its degrees of freedom.

**The three regimes.** Only `0 < k` gives a gamma law. At `k = 0` the shape would degenerate, and
the law is *defined* to be `Measure.dirac 0`: that is the value forced by additivity, since a
convolution unit must be a point mass at the origin, and it is the law of an empty sum of squared
standard Gaussians. Below `0` there is no law at all, and the measure is `0`. The boundary at
`k = 0` is singular with respect to Lebesgue measure, so it carries its own moment and transform
formulas rather than a density.

## Main definitions

* `TauCeti.Probability.chiSquaredPDFReal` — the real-valued candidate density formula,
  `x ^ (k / 2 - 1) * exp (-x / 2) / (2 ^ (k / 2) * Γ (k / 2))` on `[0, ∞)`,
  which is a probability density when `0 < k`;
* `TauCeti.Probability.chiSquaredPDF` — its `ℝ≥0∞`-valued companion, which is a probability
  density when `0 < k`;
* `TauCeti.Probability.chiSquaredMeasure` — the law.

## Main results

* `TauCeti.Probability.chiSquaredMeasure_eq_gammaMeasure` — the bridge to the gamma law;
* `TauCeti.Probability.isProbabilityMeasure_chiSquaredMeasure` — it is a probability measure for
  every `0 ≤ k`, the boundary `k = 0` included;
* `TauCeti.Probability.chiSquaredMeasure_eq_withDensity`,
  `TauCeti.Probability.hasPDF_of_hasLaw_chiSquaredMeasure` and
  `TauCeti.Probability.rnDeriv_chiSquaredMeasure` — the density, as a `withDensity`
  presentation, a `MeasureTheory.HasPDF` bridge and a Radon–Nikodym derivative;
* `TauCeti.Probability.measurable_chiSquaredMeasure` — measurability in the degrees of freedom,
  so the family can be used as a kernel;
* `TauCeti.Probability.cdf_chiSquaredMeasure_eq` — the cdf is `P (k / 2, x / 2)`;
* `TauCeti.Probability.integral_id_chiSquaredMeasure` and
  `TauCeti.Probability.variance_id_chiSquaredMeasure` — the mean `k` and the variance `2 * k`;
* `TauCeti.Probability.integrableExpSet_id_chiSquaredMeasure`,
  `TauCeti.Probability.mgf_id_chiSquaredMeasure` and
  `TauCeti.Probability.cgf_id_chiSquaredMeasure` — for `0 < k` the exponential moments exist
  exactly below `1 / 2`; on that half-line the mgf is `(1 - 2 * t) ^ (-(k / 2))` for every
  `0 ≤ k`;
* `TauCeti.Probability.charFun_chiSquaredMeasure` — the characteristic function is
  `(1 - 2 * I * t) ^ (-k / 2)`, for every real `t`;
* `TauCeti.Probability.chiSquaredMeasure_conv_chiSquaredMeasure` — degrees of freedom add under
  convolution;
* `TauCeti.Probability.chiSquaredMeasure_two` — two degrees of freedom give the exponential law of
  rate `1 / 2`.

## Implementation

Every positive-parameter statement is the gamma statement of shape `k / 2` and rate `1 / 2`, read
through `chiSquaredMeasure_eq_gammaMeasure`; nothing is recomputed. The arithmetic that remains is
the substitution `r = 1 / 2` in the gamma formulas: it turns `a / r` into `k`, `a / r ^ 2` into
`2 * k`, and `(1 - t / r) ^ (-a)` into `(1 - 2 * t) ^ (-(k / 2))`.

The density is stated in the textbook normalisation `2 ^ (k / 2) * Γ (k / 2)` rather than as
`gammaPDFReal (k / 2) (1 / 2)`, and `chiSquaredPDFReal_eq_gammaPDFReal` identifies the two; the
only content of that identification is `(1 / 2) ^ (k / 2) = (2 ^ (k / 2))⁻¹`.

The boundary `k = 0` uses the Dirac formulas of `TauCeti/Probability/Distributions/Dirac.lean`
together with Mathlib's `ProbabilityTheory.mgf_dirac'`, `ProbabilityTheory.variance_dirac` and
`MeasureTheory.charFun_dirac`. Its exponential-moment domain is all of `ℝ`, strictly larger than
the positive-parameter domain `Set.Iio (1 / 2)`, which is why the two regimes cannot share a
statement.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 3, the **Chi-squared** target,
  together with the chi-squared case of items 1–4 of "What every distribution must provide", and
  the completion check `chiSquaredMeasure 2 = expMeasure (1 / 2)`.
* Formal declaration scaffold: `TauCetiRoadmap/StandardDistributions/Suggested.lean`, Layer 3.
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1, 2nd ed.,
  Wiley (1994), ch. 18.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

open scoped ENNReal MeasureTheory

namespace TauCeti

namespace Probability

variable {k l : ℝ}

/-! ### The density -/

/-- The candidate density formula for the chi-squared law with `k` degrees of freedom, in the
textbook normalisation: `x ^ (k / 2 - 1) * exp (-x / 2) / (2 ^ (k / 2) * Γ (k / 2))` on the
nonnegative half-line, and `0` below it. It is a probability density when `0 < k`. -/
def chiSquaredPDFReal (k x : ℝ) : ℝ :=
  if 0 ≤ x then x ^ (k / 2 - 1) * exp (-x / 2) / (2 ^ (k / 2) * Real.Gamma (k / 2)) else 0

/-- The `ℝ≥0∞`-valued companion to `chiSquaredPDFReal`. It is a probability density when
`0 < k`. -/
def chiSquaredPDF (k x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (chiSquaredPDFReal k x)

/-- On the nonnegative half-line, the candidate real-valued chi-squared density is given by its
textbook formula. -/
@[simp]
theorem chiSquaredPDFReal_of_nonneg (hx : 0 ≤ x) :
    chiSquaredPDFReal k x =
      x ^ (k / 2 - 1) * exp (-x / 2) / (2 ^ (k / 2) * Real.Gamma (k / 2)) := by
  rw [chiSquaredPDFReal, ite_eq_left hx]

/-- Below zero, the candidate real-valued chi-squared density vanishes. -/
@[simp]
theorem chiSquaredPDFReal_of_neg (hx : x < 0) : chiSquaredPDFReal k x = 0 := by
  rw [chiSquaredPDFReal, ite_eq_right (not_le.mpr hx)]

/-- On the nonnegative half-line, the `ℝ≥0∞`-valued candidate chi-squared density is given by its
textbook formula. -/
@[simp]
theorem chiSquaredPDF_of_nonneg (hx : 0 ≤ x) :
    chiSquaredPDF k x = ENNReal.ofReal
      (x ^ (k / 2 - 1) * exp (-x / 2) / (2 ^ (k / 2) * Real.Gamma (k / 2))) := by
  rw [chiSquaredPDF, chiSquaredPDFReal_of_nonneg hx]

/-- Below zero, the `ℝ≥0∞`-valued candidate chi-squared density vanishes. -/
@[simp]
theorem chiSquaredPDF_of_neg (hx : x < 0) : chiSquaredPDF k x = 0 := by
  rw [chiSquaredPDF, chiSquaredPDFReal_of_neg hx, ENNReal.ofReal_zero]

/-- The chi-squared density is the gamma density of shape `k / 2` and rate `1 / 2`. -/
theorem chiSquaredPDFReal_eq_gammaPDFReal (k x : ℝ) :
    chiSquaredPDFReal k x = gammaPDFReal (k / 2) (1 / 2) x := by
  rw [chiSquaredPDFReal, gammaPDFReal]
  split_ifs with hx
  · have hneg : -((1 : ℝ) / 2 * x) = -x / 2 := by ring
    rw [hneg, Real.div_rpow zero_le_one (by norm_num), Real.one_rpow]
    ring
  · rfl

/-- The `ℝ≥0∞`-valued chi-squared density is the gamma density of shape `k / 2` and rate
`1 / 2`. -/
theorem chiSquaredPDF_eq_gammaPDF (k x : ℝ) : chiSquaredPDF k x = gammaPDF (k / 2) (1 / 2) x := by
  rw [chiSquaredPDF, gammaPDF, chiSquaredPDFReal_eq_gammaPDFReal]

/-- The chi-squared density is nonnegative for nonnegative degrees of freedom. -/
theorem chiSquaredPDFReal_nonneg (hk : 0 ≤ k) (x : ℝ) : 0 ≤ chiSquaredPDFReal k x := by
  rcases hk.eq_or_lt' with rfl | hk
  · simp [chiSquaredPDFReal_eq_gammaPDFReal, gammaPDFReal]
  · rw [chiSquaredPDFReal_eq_gammaPDFReal]
    exact gammaPDFReal_nonneg (by positivity) one_half_pos x

/-- The real-valued chi-squared density is measurable. -/
@[fun_prop]
theorem measurable_chiSquaredPDFReal (k : ℝ) : Measurable (chiSquaredPDFReal k) := by
  have h : chiSquaredPDFReal k = gammaPDFReal (k / 2) (1 / 2) :=
    funext (chiSquaredPDFReal_eq_gammaPDFReal k)
  rw [h]
  exact measurable_gammaPDFReal _ _

/-- The chi-squared density is measurable. -/
@[fun_prop]
theorem measurable_chiSquaredPDF (k : ℝ) : Measurable (chiSquaredPDF k) := by
  have h : chiSquaredPDF k = gammaPDF (k / 2) (1 / 2) := funext (chiSquaredPDF_eq_gammaPDF k)
  rw [h]
  exact measurable_gammaPDF _ _

/-! ### The measure and its three regimes -/

/-- The chi-squared law with `k` degrees of freedom: the gamma law of shape `k / 2` and rate
`1 / 2` for `0 < k`, the point mass at the origin for `k = 0`, and the zero measure for `k < 0`. -/
def chiSquaredMeasure (k : ℝ) : Measure ℝ :=
  if k = 0 then Measure.dirac 0 else if 0 < k then gammaMeasure (k / 2) (1 / 2) else 0

/-- For positive degrees of freedom the chi-squared law is a gamma law. -/
theorem chiSquaredMeasure_eq_gammaMeasure (hk : 0 < k) :
    chiSquaredMeasure k = gammaMeasure (k / 2) (1 / 2) := by
  rw [chiSquaredMeasure, ite_eq_right hk.ne', ite_eq_left hk]

/-- At zero degrees of freedom the chi-squared law is the point mass at the origin. -/
@[simp]
theorem chiSquaredMeasure_zero : chiSquaredMeasure 0 = Measure.dirac 0 := by
  rw [chiSquaredMeasure, ite_eq_left rfl]

/-- There is no chi-squared law with negative degrees of freedom: the measure is zero. -/
@[simp]
theorem chiSquaredMeasure_of_neg (hk : k < 0) : chiSquaredMeasure k = 0 := by
  rw [chiSquaredMeasure, ite_eq_right hk.ne, ite_eq_right (not_lt.mpr hk.le)]

/-- The chi-squared law is a probability measure for every nonnegative number of degrees of
freedom, the boundary `k = 0` included. -/
theorem isProbabilityMeasure_chiSquaredMeasure (hk : 0 ≤ k) :
    IsProbabilityMeasure (chiSquaredMeasure k) := by
  rcases hk.eq_or_lt' with rfl | h
  · rw [chiSquaredMeasure_zero]
    infer_instance
  · rw [chiSquaredMeasure_eq_gammaMeasure h]
    exact isProbabilityMeasure_gammaMeasure (by positivity) one_half_pos

/-- For positive degrees of freedom the chi-squared law has the chi-squared density with respect
to Lebesgue measure. -/
theorem chiSquaredMeasure_eq_withDensity (hk : 0 < k) :
    chiSquaredMeasure k = volume.withDensity (chiSquaredPDF k) := by
  rw [chiSquaredMeasure_eq_gammaMeasure hk, gammaMeasure,
    funext (chiSquaredPDF_eq_gammaPDF k)]

/-- The chi-squared family is measurable in its degrees of freedom, so it can be used as a
kernel. -/
@[fun_prop]
theorem measurable_chiSquaredMeasure : Measurable fun k : ℝ ↦ chiSquaredMeasure k := by
  have h : (fun k : ℝ ↦ gammaMeasure (k / 2) (1 / 2)) =
      (fun p : ℝ × ℝ ↦ gammaMeasure p.1 p.2) ∘ fun k : ℝ ↦ (k / 2, 1 / 2) := rfl
  unfold chiSquaredMeasure
  refine Measurable.ite (by simp) measurable_const ?_
  refine Measurable.ite (measurableSet_lt measurable_const measurable_id) ?_ measurable_const
  rw [h]
  exact measurable_gammaMeasure.comp (by fun_prop)

/-! ### Densities of random variables -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A variable with a chi-squared law of positive degrees of freedom has a density. -/
theorem hasPDF_of_hasLaw_chiSquaredMeasure (hk : 0 < k)
    (hX : HasLaw X (chiSquaredMeasure k) P) : HasPDF X P := by
  rw [chiSquaredMeasure_eq_gammaMeasure hk] at hX
  exact hasPDF_of_hasLaw_gammaMeasure hX

/-- The density of a chi-squared law of positive degrees of freedom is `chiSquaredPDF`. -/
theorem pdf_eq_chiSquaredPDF_of_hasLaw_chiSquaredMeasure (hk : 0 < k)
    (hX : HasLaw X (chiSquaredMeasure k) P) : pdf X P =ᵐ[volume] chiSquaredPDF k := by
  rw [chiSquaredMeasure_eq_gammaMeasure hk] at hX
  refine (pdf_eq_gammaPDF_of_hasLaw_gammaMeasure hX).trans (.of_forall fun x ↦ ?_)
  rw [chiSquaredPDF_eq_gammaPDF]

/-- The Radon–Nikodym derivative of a chi-squared law of positive degrees of freedom is
`chiSquaredPDF`. -/
theorem rnDeriv_chiSquaredMeasure (hk : 0 < k) :
    (chiSquaredMeasure k).rnDeriv volume =ᵐ[volume] chiSquaredPDF k := by
  rw [chiSquaredMeasure_eq_gammaMeasure hk]
  refine (rnDeriv_gammaMeasure _ _).trans (.of_forall fun x ↦ ?_)
  rw [chiSquaredPDF_eq_gammaPDF]

/-! ### The cumulative distribution function -/

/-- The cumulative distribution function of a chi-squared law with positive degrees of freedom is
the regularized lower incomplete gamma function `P (k / 2, x / 2)`. -/
@[simp]
theorem cdf_chiSquaredMeasure_eq (hk : 0 < k) (x : ℝ) :
    cdf (chiSquaredMeasure k) x = regularizedGamma (k / 2) (x / 2) := by
  rw [chiSquaredMeasure_eq_gammaMeasure hk, cdf_gammaMeasure_eq (by positivity) one_half_pos]
  ring_nf

/-- At zero degrees of freedom the cumulative distribution function is the unit step at the
origin. -/
theorem cdf_chiSquaredMeasure_zero (x : ℝ) :
    cdf (chiSquaredMeasure 0) x = if 0 ≤ x then 1 else 0 := by
  rw [chiSquaredMeasure_zero, cdf_dirac]

/-! ### Moments -/

/-- The mean of a chi-squared law with nonnegative degrees of freedom is its number of degrees of
freedom. -/
@[simp]
theorem integral_id_chiSquaredMeasure (hk : 0 ≤ k) : ∫ x, x ∂chiSquaredMeasure k = k := by
  rcases hk.eq_or_lt' with rfl | hk
  · rw [chiSquaredMeasure_zero, integral_dirac]
  · rw [chiSquaredMeasure_eq_gammaMeasure hk,
      integral_id_gammaMeasure (by positivity) one_half_pos]
    ring

/-- The variance of a chi-squared law with nonnegative degrees of freedom is twice its number of
degrees of freedom. -/
@[simp]
theorem variance_id_chiSquaredMeasure (hk : 0 ≤ k) :
    variance id (chiSquaredMeasure k) = 2 * k := by
  rcases hk.eq_or_lt' with rfl | hk
  · rw [chiSquaredMeasure_zero]
    simpa only [mul_zero] using variance_dirac 0
  · rw [chiSquaredMeasure_eq_gammaMeasure hk,
      variance_id_gammaMeasure (by positivity) one_half_pos]
    ring

/-! ### Exponential moments and transforms -/

/-- The exponential moments of a chi-squared law with positive degrees of freedom are exactly
those of rate `t < 1 / 2`. -/
@[simp]
theorem integrableExpSet_id_chiSquaredMeasure (hk : 0 < k) :
    integrableExpSet id (chiSquaredMeasure k) = Iio (1 / 2) := by
  rw [chiSquaredMeasure_eq_gammaMeasure hk,
    integrableExpSet_id_gammaMeasure (by positivity) one_half_pos]

/-- The moment-generating function of a chi-squared law with nonnegative degrees of freedom on the
half-line `t < 2⁻¹`. -/
@[simp]
theorem mgf_id_chiSquaredMeasure (hk : 0 ≤ k) {t : ℝ} (ht : t < 2⁻¹) :
    mgf id (chiSquaredMeasure k) t = (1 - 2 * t) ^ (-(k / 2)) := by
  rcases hk.eq_or_lt' with rfl | hk
  · rw [chiSquaredMeasure_zero, mgf_dirac']
    simp
  · rw [chiSquaredMeasure_eq_gammaMeasure hk,
      mgf_id_gammaMeasure (by positivity) one_half_pos (by rwa [one_div])]
    congr 1
    all_goals ring

/-- The cumulant-generating function of a chi-squared law with nonnegative degrees of freedom on
the half-line `t < 2⁻¹`. It is the real logarithm of
`TauCeti.Probability.mgf_id_chiSquaredMeasure`. -/
@[simp]
theorem cgf_id_chiSquaredMeasure (hk : 0 ≤ k) {t : ℝ} (ht : t < 2⁻¹) :
    cgf id (chiSquaredMeasure k) t = -(k / 2) * Real.log (1 - 2 * t) := by
  rcases hk.eq_or_lt' with rfl | hk
  · rw [chiSquaredMeasure_zero, cgf_dirac']
    simp
  · rw [chiSquaredMeasure_eq_gammaMeasure hk,
      cgf_id_gammaMeasure (by positivity) one_half_pos (by rwa [one_div])]
    congr 2
    all_goals ring

/-- The characteristic function of a chi-squared law with nonnegative degrees of freedom, at every
real `t`. The base has real part `1`, so the principal power does not meet the branch cut. -/
@[simp]
theorem charFun_chiSquaredMeasure (hk : 0 ≤ k) (t : ℝ) :
    charFun (chiSquaredMeasure k) t = (1 - 2 * Complex.I * t) ^ (-(k : ℂ) / 2) := by
  rcases hk.eq_or_lt' with rfl | hk
  · rw [chiSquaredMeasure_zero, charFun_dirac]
    simp
  · rw [chiSquaredMeasure_eq_gammaMeasure hk, charFun_gammaMeasure (by positivity) one_half_pos]
    push_cast
    congr 1 <;> ring

/-- At zero degrees of freedom every exponential moment exists. -/
theorem integrableExpSet_id_chiSquaredMeasure_zero :
    integrableExpSet id (chiSquaredMeasure 0) = univ := by
  rw [chiSquaredMeasure_zero, integrableExpSet_dirac]

/-- At zero degrees of freedom the moment-generating function is identically `1`. -/
theorem mgf_id_chiSquaredMeasure_zero (t : ℝ) : mgf id (chiSquaredMeasure 0) t = 1 := by
  rw [chiSquaredMeasure_zero, mgf_dirac']
  simp

/-- At zero degrees of freedom the cumulant-generating function is identically `0`. -/
theorem cgf_id_chiSquaredMeasure_zero (t : ℝ) : cgf id (chiSquaredMeasure 0) t = 0 := by
  rw [chiSquaredMeasure_zero, cgf_dirac']
  simp

/-! ### Additivity and the exponential law -/

/-- Degrees of freedom add under convolution, including at the boundary `k = 0`, where the
chi-squared law is the convolution unit. -/
theorem chiSquaredMeasure_conv_chiSquaredMeasure (hk : 0 ≤ k) (hl : 0 ≤ l) :
    chiSquaredMeasure k ∗ chiSquaredMeasure l = chiSquaredMeasure (k + l) := by
  -- At a zero factor the law is the point mass at the origin, the convolution unit; the
  -- probability measure instance is what makes the other factor `SFinite`.
  rcases hk.eq_or_lt' with rfl | hk'
  · have := isProbabilityMeasure_chiSquaredMeasure hl
    rw [chiSquaredMeasure_zero, zero_add]
    simp
  rcases hl.eq_or_lt' with rfl | hl'
  · have := isProbabilityMeasure_chiSquaredMeasure hk
    rw [chiSquaredMeasure_zero, add_zero]
    simp
  rw [chiSquaredMeasure_eq_gammaMeasure hk', chiSquaredMeasure_eq_gammaMeasure hl',
    chiSquaredMeasure_eq_gammaMeasure (by linarith),
    gammaMeasure_conv_gammaMeasure (by positivity) (by positivity) one_half_pos]
  ring_nf

/-- Two degrees of freedom give the exponential law of rate `1 / 2`. -/
theorem chiSquaredMeasure_two : chiSquaredMeasure 2 = expMeasure (1 / 2) := by
  rw [chiSquaredMeasure_eq_gammaMeasure two_pos, expMeasure]
  norm_num

end Probability

end TauCeti
