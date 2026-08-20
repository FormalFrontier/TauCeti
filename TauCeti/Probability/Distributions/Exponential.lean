/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.PDFInstances
public import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Moments of the exponential law

The mean and variance of `ProbabilityTheory.expMeasure r`:

```text
∫ x ∂(expMeasure r) = r⁻¹        Var[id; expMeasure r] = (r ^ 2)⁻¹
```

**Both come from one moment formula.** `integral_pow_id_expMeasure` computes every moment,
`∫ x ^ n = n ! / r ^ n`, and the mean and the second moment are its `n = 1` and `n = 2` cases.
Proving those two separately would repeat the same density transport and Gamma-integral argument
twice, so the general statement is the one proved and the two specializations are `simpa` from it.

**The engine is Mathlib's Gamma integral.** `integral_rpow_mul_exp_neg_mul_Ioi` evaluates
`∫ t in Ioi 0, t ^ (a - 1) * exp (-(r * t))` as `(1 / r) ^ a * Γ a`; at `a = n + 1` the Gamma factor
is `n !`.  Nothing here integrates by parts or reproves a convergence result — except that Mathlib
states integrability of that integrand only at rate `r = 1` (`GammaIntegral_convergent`), so
`integrableOn_gammaIntegrand` transports it to a general rate by scaling.

**`n ≠ 0` is not decoration.** At `n = 0` the integrand `x ^ n * pdf x` does not vanish at the
origin, so it is not the indicator of `Ioi 0` that the Gamma integral needs; the hypothesis is what
makes the pointwise identity true rather than true off a null set.

## Main results

* `integral_pow_id_expMeasure` — the `n`-th moment, `n ! / r ^ n`;
* `integral_id_expMeasure`, `integral_sq_id_expMeasure` — the mean and the second moment;
* `variance_id_expMeasure` — the variance.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 1, exponential — the mean and
  variance.  The mgf, cgf, characteristic function, memorylessness, and the minimum of two
  independent exponentials are separate targets and are not built here.
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

/-- Integrability of the Gamma integrand at a general rate.  Mathlib proves this at `r = 1`
(`GammaIntegral_convergent`); the general case follows by scaling. -/
private theorem integrableOn_gammaIntegrand (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun x => x ^ (a - 1) * exp (-(r * x))) (Ioi 0) := by
  have h : IntegrableOn (fun x => exp (-(r * x)) * (r * x) ^ (a - 1)) (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff
      (fun t => exp (-t) * t ^ (a - 1)) 0 hr).2 (by simpa using Real.GammaIntegral_convergent ha)
    simpa using this
  refine IntegrableOn.congr_fun (h.const_mul ((r ^ (a - 1))⁻¹)) (fun x hx => ?_) measurableSet_Ioi
  rw [Real.mul_rpow hr.le (le_of_lt hx)]
  field_simp

/-- An integral against `expMeasure` is a density integral against `volume`. -/
private theorem integral_expMeasure (hr : 0 < r) (g : ℝ → ℝ) :
    ∫ x, g x ∂(expMeasure r) = ∫ x, exponentialPDFReal r x * g x := by
  have hmeas : Measurable (exponentialPDF r) := measurable_gammaPDF 1 r
  have key : ∀ x : ℝ, (exponentialPDF r x).toReal • g x = exponentialPDFReal r x * g x := by
    intro x
    rw [smul_eq_mul, show exponentialPDF r x = ENNReal.ofReal (exponentialPDFReal r x) from rfl,
      ENNReal.toReal_ofReal (exponentialPDFReal_nonneg hr x)]
  rw [show expMeasure r = volume.withDensity (exponentialPDF r) from rfl,
    integral_withDensity_eq_integral_toReal_smul hmeas
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  exact integral_congr_ae (ae_of_all _ fun x => key x)

/-- The moment integrand is the Gamma integrand supported on `Ioi 0`.  This needs `n ≠ 0`: at
`n = 0` the left side is the density itself, which does not vanish at the origin. -/
private theorem integrand_eq_indicator (hn : n ≠ 0) :
    (fun x => exponentialPDFReal r x * x ^ n)
      = (Ioi (0:ℝ)).indicator (fun x => r * (x ^ ((n : ℝ) + 1 - 1) * exp (-(r * x)))) := by
  funext x
  by_cases hx : (0:ℝ) < x
  · rw [Set.indicator_of_mem (mem_Ioi.mpr hx), exponentialPDFReal_apply]
    split_ifs with h
    · rw [add_sub_cancel_right, Real.rpow_natCast]
      ring
    · exact absurd hx.le h
  · rw [Set.indicator_of_notMem (by simpa using hx), exponentialPDFReal_apply]
    have hx' : x ≤ 0 := not_lt.mp hx
    split_ifs with h
    · have hx0 : x = 0 := le_antisymm hx' h
      rw [hx0, zero_pow hn, mul_zero]
    · ring

/-- Every moment of the exponential law is integrable. -/
private theorem integrable_pow_id_expMeasure (hr : 0 < r) (hn : n ≠ 0) :
    Integrable (fun x => x ^ n) (expMeasure r) := by
  have hmeas : Measurable (exponentialPDF r) := measurable_gammaPDF 1 r
  have htoReal : ∀ x : ℝ,
      x ^ n * (exponentialPDF r x).toReal = exponentialPDFReal r x * x ^ n := by
    intro x
    rw [show exponentialPDF r x = ENNReal.ofReal (exponentialPDFReal r x) from rfl,
      ENNReal.toReal_ofReal (exponentialPDFReal_nonneg hr x)]
    ring
  rw [show expMeasure r = volume.withDensity (exponentialPDF r) from rfl,
    integrable_withDensity_iff hmeas (ae_of_all _ fun x => ENNReal.ofReal_lt_top),
    funext htoReal, integrand_eq_indicator hn, integrable_indicator_iff measurableSet_Ioi]
  exact (integrableOn_gammaIntegrand (by positivity) hr).const_mul r

/-- **The moments of the exponential law.** `∫ x ^ n ∂(expMeasure r) = n ! / r ^ n`.

The mean and the second moment below are the `n = 1` and `n = 2` cases; stating the general formula
avoids running the same density transport and Gamma-integral argument twice. -/
theorem integral_pow_id_expMeasure (hr : 0 < r) (hn : n ≠ 0) :
    ∫ x, x ^ n ∂(expMeasure r) = (Nat.factorial n : ℝ) / r ^ n := by
  rw [integral_expMeasure hr, integrand_eq_indicator hn,
    integral_indicator measurableSet_Ioi, integral_const_mul,
    integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hr, Real.Gamma_nat_eq_factorial,
    show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  field_simp
  rw [one_div, inv_pow, pow_succ]
  field_simp

/-- **The mean of the exponential law** with rate `r` is `r⁻¹`. -/
theorem integral_id_expMeasure (hr : 0 < r) : ∫ x, x ∂(expMeasure r) = r⁻¹ := by
  simpa using integral_pow_id_expMeasure hr one_ne_zero

/-- The second moment of the exponential law with rate `r` is `2 / r ^ 2`. -/
theorem integral_sq_id_expMeasure (hr : 0 < r) : ∫ x, x ^ 2 ∂(expMeasure r) = 2 / r ^ 2 := by
  simpa using integral_pow_id_expMeasure hr two_ne_zero

/-- **The variance of the exponential law** with rate `r` is `(r ^ 2)⁻¹`. -/
theorem variance_id_expMeasure (hr : 0 < r) : Var[id; expMeasure r] = (r ^ 2)⁻¹ := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have h₂ : Integrable (fun x => id x ^ 2) (expMeasure r) :=
    integrable_pow_id_expMeasure hr two_ne_zero
  have hLp : MemLp id 2 (expMeasure r) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 h₂
  rw [variance_eq_sub hLp]
  simp only [Pi.pow_apply, id_eq]
  rw [integral_sq_id_expMeasure hr, integral_id_expMeasure hr]
  field_simp
  ring

end Probability

end TauCeti
