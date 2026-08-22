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

/-!
# Moments of the exponential law

The mean and variance of `ProbabilityTheory.expMeasure r`, for a positive rate `0 < r`:

```text
∫ x, x ∂(expMeasure r) = r⁻¹        Var[id; expMeasure r] = (r ^ 2)⁻¹
```

Every result below carries that hypothesis, but the two regimes it excludes differ.  At `r < 0` the
identities fail outright.  At `r = 0` the density is identically zero, so `expMeasure 0` is the zero
measure and the two displays above hold only as junk-value coincidences (`0 = 0⁻¹`); what genuinely
fails there is the `n = 0` moment, `0 ≠ 0 ! / 0 ^ 0 = 1`.

**Both come from one moment formula.** `integral_pow_expMeasure` computes every moment,
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

* `integrable_pow_expMeasure` — every moment is integrable, for `0 < r`;
* `integral_pow_expMeasure` — the `n`-th moment, `n ! / r ^ n`, for `0 < r`;
* `integral_id_expMeasure`, `integral_sq_expMeasure` — the mean and the second moment;
* `variance_id_expMeasure` — the variance.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 1, exponential — the mean and
  variance.
* [mathlib4#35504](https://github.com/leanprover-community/mathlib4/pull/35504), the upstream
  exponential mgf, moments and memorylessness work that the roadmap names as the source for this
  material.  It has not landed at Tau Ceti's current Mathlib pin, so the declarations here follow
  its names and theorem shapes and should be dropped once the pin provides them.
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

/-- The `ℝ≥0∞` density at rate `r`, read as a real number, is `exponentialPDFReal`. -/
private theorem toReal_gammaPDF_one (hr : 0 < r) (x : ℝ) :
    (gammaPDF 1 r x).toReal = exponentialPDFReal r x := by
  unfold gammaPDF exponentialPDFReal
  rw [ENNReal.toReal_ofReal (gammaPDFReal_nonneg one_pos hr x)]

/-- An integral against `expMeasure` is a density integral against `volume`. -/
private theorem integral_expMeasure (hr : 0 < r) (g : ℝ → ℝ) :
    ∫ x, g x ∂(expMeasure r) = ∫ x, exponentialPDFReal r x * g x := by
  have hmeas : Measurable (gammaPDF 1 r) := measurable_gammaPDF 1 r
  have key : ∀ x : ℝ, (gammaPDF 1 r x).toReal • g x = exponentialPDFReal r x * g x := by
    intro x
    rw [smul_eq_mul, toReal_gammaPDF_one hr]
  unfold expMeasure gammaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hmeas
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

/-- The integrability companion of `integral_expMeasure`: integrability against `expMeasure` is
integrability of the density product against `volume`. -/
private theorem integrable_expMeasure_iff (hr : 0 < r) (g : ℝ → ℝ) :
    Integrable g (expMeasure r)
      ↔ Integrable (fun x => exponentialPDFReal r x * g x) volume := by
  have hmeas : Measurable (gammaPDF 1 r) := measurable_gammaPDF 1 r
  have htoReal : ∀ x : ℝ, g x * (gammaPDF 1 r x).toReal = exponentialPDFReal r x * g x := by
    intro x
    rw [toReal_gammaPDF_one hr]
    ring
  unfold expMeasure gammaMeasure
  rw [integrable_withDensity_iff hmeas (ae_of_all _ fun x => ENNReal.ofReal_lt_top),
    funext htoReal]

/-- **Every moment of the exponential law is integrable.**  This is not implied by the moment
formula below: Lean's integral is defined for non-integrable functions too, so an integral equality
alone says nothing about finiteness. -/
@[simp]
theorem integrable_pow_expMeasure (hr : 0 < r) (n : ℕ) :
    Integrable (fun x => x ^ n) (expMeasure r) := by
  have hprob : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [integrable_expMeasure_iff hr, integrand_eq_indicator hn,
    integrable_indicator_iff measurableSet_Ioi]
  exact (integrableOn_pow_mul_exp_neg_mul_Ioi n hr).const_mul r

/-- **The moments of the exponential law.** `∫ x ^ n ∂(expMeasure r) = n ! / r ^ n`, for every `n`.

No nondegeneracy hypothesis on `n` is needed: at `n = 0` both sides are `1`.  The mean and the
second moment below are the `n = 1` and `n = 2` cases. -/
@[simp]
theorem integral_pow_expMeasure (hr : 0 < r) (n : ℕ) :
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
  simpa using integral_pow_expMeasure hr 1

/-- The second moment of the exponential law with rate `r` is `2 / r ^ 2`. -/
theorem integral_sq_expMeasure (hr : 0 < r) : ∫ x, x ^ 2 ∂(expMeasure r) = 2 / r ^ 2 := by
  simpa using integral_pow_expMeasure hr 2

/-- **The variance of the exponential law** with rate `r` is `(r ^ 2)⁻¹`. -/
@[simp]
theorem variance_id_expMeasure (hr : 0 < r) : Var[id; expMeasure r] = (r ^ 2)⁻¹ := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have h₂ : Integrable (fun x => id x ^ 2) (expMeasure r) :=
    integrable_pow_expMeasure hr 2
  have hLp : MemLp id 2 (expMeasure r) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 h₂
  rw [variance_eq_sub hLp]
  simp only [Pi.pow_apply, id_eq]
  rw [integral_sq_expMeasure hr, integral_id_expMeasure hr]
  field_simp
  ring

end Probability

end TauCeti
