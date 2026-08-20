/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Moments.Variance
import TauCeti.Probability.Distributions.PDFInstances
import TauCeti.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Moments of the exponential law

The mean and variance of `ProbabilityTheory.expMeasure r`:

```text
∫ x, x ∂(expMeasure r) = r⁻¹        Var[id; expMeasure r] = (r ^ 2)⁻¹
```

**Both come from one moment formula.** `integral_pow_id_expMeasure` computes every moment,
`∫ x ^ n = n ! / r ^ n`, and the mean and the second moment are its `n = 1` and `n = 2` cases.
Proving those two separately would repeat the same density transport and Gamma-integral argument
twice, so the general statement is the one proved and the two specializations are `simpa` from it.

**The engine is `TauCeti.MeasureTheory.Integral.ExpDecay`.** `integral_pow_mul_exp_neg_mul_Ioi`
already evaluates `∫ t in Ioi 0, t ^ n * exp (-(a * t))` as `n ! / a ^ (n + 1)`, and
`integrableOn_pow_mul_exp_neg_mul_Ioi` supplies the matching integrability.  Nothing analytic is
reproved here; the work is the density transport that turns an integral against `expMeasure` into
one of those.

**The moment formula holds at every `n`; its Gamma-integral route does not.** At `n = 0` the
integrand `x ^ n * pdf x` does not vanish at the origin, so it is not the indicator of `Ioi 0`
that route needs, and the private `integrand_eq_indicator` carries `n ≠ 0` for that reason.  The
zero case is discharged from the probability-measure instance instead.

## Main results

* `integrable_pow_id_expMeasure` — every moment is integrable;
* `integral_pow_id_expMeasure` — the `n`-th moment, `n ! / r ^ n`;
* `integral_id_expMeasure`, `integral_sq_id_expMeasure` — the mean and the second moment;
* `variance_id_expMeasure` — the variance.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 1, exponential — the mean and
  variance.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Real

namespace TauCeti

namespace Probability

variable {a r : ℝ} {n : ℕ}

/-- The exponential density in closed form.  Kept private: it only unfolds Mathlib's definition
through `gammaPDFReal 1`, so it is a proof convenience rather than API. -/
private theorem exponentialPDFReal_apply (x : ℝ) :
    exponentialPDFReal r x = if 0 ≤ x then r * exp (-(r * x)) else 0 := by
  rw [exponentialPDFReal, gammaPDFReal]
  split_ifs with hx
  · rw [Real.rpow_one, Real.Gamma_one, sub_self, Real.rpow_zero]
    ring
  · rfl

/-- `expMeasure` is a `withDensity` measure by definition.  Named so the proofs below rewrite with
it rather than repeating a bare definitional conversion. -/
private theorem expMeasure_eq_withDensity (r : ℝ) :
    expMeasure r = volume.withDensity (exponentialPDF r) := (rfl)

/-- The `ℝ≥0∞`-valued density is `ENNReal.ofReal` of the real one, by definition. -/
private theorem exponentialPDF_apply (r x : ℝ) :
    exponentialPDF r x = ENNReal.ofReal (exponentialPDFReal r x) := (rfl)

/-- An integral against `expMeasure` is a density integral against `volume`. -/
private theorem integral_expMeasure (hr : 0 < r) (g : ℝ → ℝ) :
    ∫ x, g x ∂(expMeasure r) = ∫ x, exponentialPDFReal r x * g x := by
  have hmeas : Measurable (exponentialPDF r) := measurable_gammaPDF 1 r
  have key : ∀ x : ℝ, (exponentialPDF r x).toReal • g x = exponentialPDFReal r x * g x := by
    intro x
    rw [smul_eq_mul, exponentialPDF_apply,
      ENNReal.toReal_ofReal (exponentialPDFReal_nonneg hr x)]
  rw [expMeasure_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul hmeas
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  exact integral_congr_ae (ae_of_all _ fun x => key x)

/-- The moment integrand is the Gamma integrand supported on `Ioi 0`.  This needs `n ≠ 0`: at
`n = 0` the left side is the density itself, which does not vanish at the origin. -/
private theorem integrand_eq_indicator (hn : n ≠ 0) :
    (fun x => exponentialPDFReal r x * x ^ n)
      = (Ioi (0:ℝ)).indicator (fun x => r * (x ^ n * exp (-(r * x)))) := by
  funext x
  by_cases hx : (0:ℝ) < x
  · rw [Set.indicator_of_mem (mem_Ioi.mpr hx), exponentialPDFReal_apply]
    split_ifs with h
    · ring
    · exact absurd hx.le h
  · rw [Set.indicator_of_notMem (by simpa using hx), exponentialPDFReal_apply]
    have hx' : x ≤ 0 := not_lt.mp hx
    split_ifs with h
    · have hx0 : x = 0 := le_antisymm hx' h
      rw [hx0, zero_pow hn, mul_zero]
    · ring

/-- **Every moment of the exponential law is integrable.**  This is not implied by the moment
formula below: Lean's integral is defined for non-integrable functions too, so an integral equality
alone says nothing about finiteness. -/
@[simp]
theorem integrable_pow_id_expMeasure (hr : 0 < r) (n : ℕ) :
    Integrable (fun x => x ^ n) (expMeasure r) := by
  have hprob : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hmeas : Measurable (exponentialPDF r) := measurable_gammaPDF 1 r
  have htoReal : ∀ x : ℝ,
      x ^ n * (exponentialPDF r x).toReal = exponentialPDFReal r x * x ^ n := by
    intro x
    rw [exponentialPDF_apply, ENNReal.toReal_ofReal (exponentialPDFReal_nonneg hr x)]
    ring
  rw [expMeasure_eq_withDensity,
    integrable_withDensity_iff hmeas (ae_of_all _ fun x => ENNReal.ofReal_lt_top),
    funext htoReal, integrand_eq_indicator hn, integrable_indicator_iff measurableSet_Ioi]
  exact (integrableOn_pow_mul_exp_neg_mul_Ioi n hr).const_mul r

/-- **The moments of the exponential law.** `∫ x ^ n ∂(expMeasure r) = n ! / r ^ n`, for every `n`.

The mean and the second moment below are the `n = 1` and `n = 2` cases; stating the general formula
avoids running the same density transport and Gamma-integral argument twice.

At `n = 0` both sides are `1`, from the probability-measure instance; the Gamma-integral route is
used for positive `n`. -/
@[simp]
theorem integral_pow_id_expMeasure (hr : 0 < r) (n : ℕ) :
    ∫ x, x ^ n ∂(expMeasure r) = (Nat.factorial n : ℝ) / r ^ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
    simp
  rw [integral_expMeasure hr, integrand_eq_indicator hn,
    integral_indicator measurableSet_Ioi, integral_const_mul,
    integral_pow_mul_exp_neg_mul_Ioi n hr]
  field_simp
  ring

/-- **The mean of the exponential law** with rate `r` is `r⁻¹`. -/
@[simp]
theorem integral_id_expMeasure (hr : 0 < r) : ∫ x, x ∂(expMeasure r) = r⁻¹ := by
  simpa using integral_pow_id_expMeasure hr 1

/-- The second moment of the exponential law with rate `r` is `2 / r ^ 2`. -/
theorem integral_sq_id_expMeasure (hr : 0 < r) : ∫ x, x ^ 2 ∂(expMeasure r) = 2 / r ^ 2 := by
  simpa using integral_pow_id_expMeasure hr 2

/-- **The variance of the exponential law** with rate `r` is `(r ^ 2)⁻¹`. -/
@[simp]
theorem variance_id_expMeasure (hr : 0 < r) : Var[id; expMeasure r] = (r ^ 2)⁻¹ := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have h₂ : Integrable (fun x => id x ^ 2) (expMeasure r) :=
    integrable_pow_id_expMeasure hr 2
  have hLp : MemLp id 2 (expMeasure r) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 h₂
  rw [variance_eq_sub hLp]
  simp only [Pi.pow_apply, id_eq]
  rw [integral_sq_id_expMeasure hr, integral_id_expMeasure hr]
  field_simp
  ring

end Probability

end TauCeti
