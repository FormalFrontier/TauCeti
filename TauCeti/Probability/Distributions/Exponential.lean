/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import TauCeti.Probability.Distributions.PDFInstances
import TauCeti.MeasureTheory.Integral.ExpDecay

/-!
# Moments and transforms of the exponential law

The moments and transforms of `ProbabilityTheory.expMeasure r`, for a positive rate `0 < r`:

```text
∫ x, x ∂(expMeasure r) = r⁻¹        Var[id; expMeasure r] = (r ^ 2)⁻¹
mgf id (expMeasure r) t = r / (r - t)      (for t < r)
charFun (expMeasure r) t = r / (r - I * t)  (for every t)
```

Every result below carries that hypothesis, but the two regimes it excludes differ.  At `r < 0` the
identities fail outright.  At `r = 0` the density is identically zero, so `expMeasure 0` is the zero
measure and the displays above hold only as junk-value
coincidences (`0 = 0⁻¹` for the mean); what genuinely
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
* `variance_id_expMeasure` — the variance;
* `integrableExpSet_id_expMeasure` — the moment-generating domain is exactly `Iio r`;
* `mgf_id_expMeasure`, `mgf_id_expMeasure_pos`, `cgf_id_expMeasure` — the mgf on that domain, its
  strict positivity, and the cgf;
* `charFun_expMeasure` — the characteristic function, at every real `t`.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 1, exponential — the moments,
  the moment-generating domain, the mgf and cgf, and the characteristic function.
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
private theorem integral_expMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hr : 0 < r) (g : ℝ → E) :
    ∫ x, g x ∂(expMeasure r) = ∫ x, exponentialPDFReal r x • g x := by
  have hmeas : Measurable (gammaPDF 1 r) := measurable_gammaPDF 1 r
  have key : ∀ x : ℝ, (gammaPDF 1 r x).toReal • g x = exponentialPDFReal r x • g x := by
    intro x
    rw [toReal_gammaPDF_one hr]
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
  rw [integral_expMeasure hr]
  simp only [smul_eq_mul]
  rw [integrand_eq_indicator hn,
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

/-! ### The moment-generating domain

The exponential moment `∫ exp (t * x)` exists exactly for `t < r`.  Both directions come from
`TauCeti.integrableOn_exp_mul_Ioi_iff`: after the density transport the integrand is a constant
multiple of `exp ((t - r) * x)` on `[0, ∞)`, whose integrability is equivalent to `t - r < 0`.
-/

/-- The exponential-moment integrand in closed form: off the negative half-line it is a constant
multiple of a single exponential at rate `t - r`. -/
private theorem expIntegrand_eq_indicator (t : ℝ) :
    (fun x => exponentialPDFReal r x * exp (t * x))
      = (Ici (0:ℝ)).indicator (fun x => r * exp ((t - r) * x)) := by
  funext x
  rw [exponentialPDFReal_apply]
  by_cases hx : (0:ℝ) ≤ x
  · rw [Set.indicator_of_mem (mem_Ici.mpr hx)]
    split_ifs
    -- split the single exponential at rate `t - r` into the density and mgf factors
    have hsplit : (t - r) * x = t * x + -(r * x) := by ring
    rw [hsplit, Real.exp_add]
    ring
  · rw [Set.indicator_of_notMem (by simpa using hx)]
    split_ifs
    ring

/-- **The moment-generating domain of the exponential law** is exactly `Iio r`. -/
@[simp]
theorem integrableExpSet_id_expMeasure (hr : 0 < r) :
    integrableExpSet id (expMeasure r) = Set.Iio r := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, id_eq, Set.mem_Iio]
  rw [integrable_expMeasure_iff hr, expIntegrand_eq_indicator t,
    integrable_indicator_iff measurableSet_Ici,
    integrableOn_Ici_iff_integrableOn_Ioi]
  unfold IntegrableOn
  rw [integrable_const_mul_iff (isUnit_iff_ne_zero.2 hr.ne') (fun x => exp ((t - r) * x))]
  exact integrableOn_exp_mul_Ioi_iff.trans sub_neg

/-- The sign normalization both transform proofs need: `integral_exp_mul_Ioi` and its complex
counterpart report a value at rate `a - b`, while the statements are oriented at `b - a`.  Holds
unconditionally — at `a = b` both sides are the junk value `0`. -/
private theorem mul_neg_one_div_sub {K : Type*} [Field K] (c a b : K) :
    c * (-1 / (a - b)) = c / (b - a) := by
  rw [neg_div, mul_neg, mul_one_div, ← neg_sub a b, div_neg]

/-! ### The moment generating function and its logarithm -/

/-- **The moment generating function of the exponential law**, on its domain `t < r`. -/
@[simp]
theorem mgf_id_expMeasure (hr : 0 < r) (ht : t < r) :
    mgf id (expMeasure r) t = r / (r - t) := by
  unfold mgf
  simp only [id_eq]
  rw [integral_expMeasure hr]
  simp only [smul_eq_mul]
  rw [expIntegrand_eq_indicator t, integral_indicator measurableSet_Ici,
    integral_Ici_eq_integral_Ioi, integral_const_mul, integral_exp_mul_Ioi (sub_neg.2 ht) 0]
  simp only [mul_zero, Real.exp_zero]
  exact mul_neg_one_div_sub r t r

/-- The moment generating function is strictly positive on its domain.

Proved from Mathlib's `mgf_pos` and the domain equality, through Mathlib's own
`integrable_of_mem_integrableExpSet`, rather than by `div_pos` on the closed form: positivity is a
consequence of the exponential moment *existing*, which is what a consumer reasoning about the
cgf's domain actually has. -/
theorem mgf_id_expMeasure_pos (hr : 0 < r) (ht : t < r) : 0 < mgf id (expMeasure r) t := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  refine mgf_pos (integrable_of_mem_integrableExpSet ?_)
  rw [integrableExpSet_id_expMeasure hr]
  exact ht

/-- **The cumulant generating function of the exponential law**, on its domain `t < r`. -/
@[simp]
theorem cgf_id_expMeasure (hr : 0 < r) (ht : t < r) :
    cgf id (expMeasure r) t = Real.log (r / (r - t)) := by
  unfold cgf
  rw [mgf_id_expMeasure hr ht]

/-! ### The characteristic function -/

/-- The characteristic-function integrand in closed form on the positive half-line. -/
private theorem charIntegrand_eq (t : ℝ) {x : ℝ} (hx : 0 < x) :
    exponentialPDFReal r x • Complex.exp ((t : ℂ) * x * Complex.I)
      = (r : ℂ) * Complex.exp (((t : ℂ) * Complex.I - r) * x) := by
  rw [exponentialPDFReal_apply]
  split_ifs with h
  · rw [Complex.real_smul]
    push_cast [Complex.ofReal_exp]
    rw [mul_assoc, ← Complex.exp_add]
    ring_nf
  · exact absurd hx.le h

/-- **The characteristic function of the exponential law.**

Unlike the mgf this needs no hypothesis on `t`: the density-transported integrand has modulus
`r * exp (-(r * x))` on `[0, ∞)` whatever `t` is, so the integral converges at every real `t`. -/
@[simp]
theorem charFun_expMeasure (hr : 0 < r) (t : ℝ) :
    charFun (expMeasure r) t = (r : ℂ) / (r - Complex.I * t) := by
  have ha : ((t : ℂ) * Complex.I - r).re < 0 := by simp [hr]
  have hzero : ∀ x ∉ Ici (0:ℝ),
      exponentialPDFReal r x • Complex.exp ((t : ℂ) * x * Complex.I) = 0 := by
    intro x hx
    have hpdf : exponentialPDFReal r x = 0 := by
      rw [exponentialPDFReal_apply]
      split_ifs with h
      · exact absurd h (by simpa using hx)
      · rfl
    rw [hpdf, zero_smul]
  rw [charFun_apply_real, integral_expMeasure hr,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, integral_Ici_eq_integral_Ioi,
    setIntegral_congr_fun measurableSet_Ioi (fun x hx => charIntegrand_eq t (mem_Ioi.mp hx)),
    integral_const_mul, integral_exp_mul_complex_Ioi ha 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show ((t : ℂ) * Complex.I - r) = (Complex.I * t - r) by ring]
  exact mul_neg_one_div_sub (r : ℂ) (Complex.I * t) r

end Probability

end TauCeti
