/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Beta
import TauCeti.Analysis.Calculus.RealCharts
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Euler's beta integrals, in real-valued form

Mathlib defines Euler's beta function `ProbabilityTheory.beta` by the Gamma quotient, and proves
that it is the value of `Complex.betaIntegral`, the complex-valued interval integral of
`t ^ (a - 1) * (1 - t) ^ (b - 1)` over `[0, 1]`. This file records the real-variable facts about
the real-valued beta integrand `t ^ (a - 1) * (1 - t) ^ (b - 1)` that a real-analysis consumer
needs: its interval integrability on `[0, 1]`, the value `Β(a, b)` of its
integral over `[0, 1]`, the derivative of the kernel `t ^ a * (1 - t) ^ b` it primitivises, and
the splitting of the integrand that raises the second parameter by one. Two parameter identities
for `Β` itself — symmetry and the unit step in the first parameter — are recorded alongside.

It also records Euler's *second* beta integral, the half-line form
`∫ x in Ioi 0, x ^ (a - 1) * (1 + x) ^ (-(a + b)) = Β(a, b)`, together with its integrability
statement, and specialises it to the Cauchy-type kernel `(1 + x ^ 2) ^ (-s)` on the whole line.

These are the analytic prerequisites of
`TauCeti/Analysis/SpecialFunctions/IncompleteBeta.lean`;
`TauCeti/Probability/Distributions/Beta/Basic.lean` uses the beta integral for its moment formula,
and `TauCeti/Probability/Distributions/StudentT/Basic.lean` normalizes its density with the
`(1 + x ^ 2) ^ (-s)` form of the second integral.

## Main results

* `TauCeti.intervalIntegrable_rpow_mul_one_sub_rpow` — interval integrability of the beta
  integrand between any two points of `[0, 1]`;
* `TauCeti.integral_rpow_mul_one_sub_rpow` — Euler's beta integral,
  `∫ t in 0..1, t ^ (a - 1) * (1 - t) ^ (b - 1) = Β(a, b)`;
* `TauCeti.hasDerivAt_rpow_mul_one_sub_rpow` — the derivative of `t ^ a * (1 - t) ^ b`;
* `TauCeti.integral_rpow_mul_one_sub_rpow_add_one_right` — raising the second parameter by one
  splits the integral as a difference;
* `TauCeti.integrableOn_rpow_mul_one_add_rpow` and `TauCeti.integral_rpow_mul_one_add_rpow` —
  Euler's second beta integral,
  `∫ x in Ioi 0, x ^ (a - 1) * (1 + x) ^ (-(a + b)) = Β(a, b)`;
* `TauCeti.abs_deriv_smul_one_add_rpow` — the change-of-variables identity relating the first and
  second beta-integral kernels under the chart `u ↦ u / (1 - u)`;
* `TauCeti.integrable_one_add_sq_rpow`, `TauCeti.integral_one_add_sq_rpow`,
  `TauCeti.integrable_one_add_sq_div_rpow`, and `TauCeti.integral_one_add_sq_div_rpow` — the
  Cauchy-type kernel `(1 + x ^ 2 / ν) ^ (-s)` is integrable on the line for `0 < ν` and
  `1 / 2 < s`, with total mass `√ν * Β(1 / 2, s - 1 / 2)`;
* `ProbabilityTheory.beta_comm` — symmetry of `Β`;
* `ProbabilityTheory.beta_one_right` — the value `Β(a, 1) = 1 / a`;
* `ProbabilityTheory.beta_add_one_left` — the unit step `Β(a + 1, b) = a / (a + b) * Β(a, b)`.

## Implementation notes

The proof of `TauCeti.intervalIntegrable_rpow_mul_one_sub_rpow` transposes the argument of
Mathlib's `Complex.betaIntegral_convergent` and `Complex.betaIntegral_convergent_left` to the
real-valued setting: split `[0, 1]` at `1 / 2` and handle each endpoint singularity with
`intervalIntegral.intervalIntegrable_rpow'` against a factor that is continuous there, obtaining
the right half from the left one by the reflection `t ↦ 1 - t`. The proof of
`TauCeti.integral_rpow_mul_one_sub_rpow` adapts the normalization argument for
`ProbabilityTheory.betaMeasure` in Mathlib, `ProbabilityTheory.lintegral_betaPDF_eq_one`:
descend from `Complex.betaIntegral` by taking real parts.

Both changes of variables for the second integral are one-dimensional, run through
`MeasureTheory.integral_image_eq_integral_abs_deriv_smul` and its integrability companion. The
chart `u ↦ u / (1 - u)` carries `(0, 1)` onto `(0, ∞)` and turns the first integrand into the
second; the chart `t ↦ √t` carries `(0, ∞)` onto itself and turns `(1 + x ^ 2) ^ (-s)` into the
second integrand with first parameter `1 / 2`. Full-line integrability is an instance of Mathlib's
`integrable_rpow_neg_one_add_norm_sq`, and the integral value folds the two halves of the line
together with `MeasureTheory.integral_comp_abs`.

## References

* Tau Ceti roadmap, `StandardDistributions`, Layer 2, "Regularized incomplete beta", for which
  these are the prerequisites, and Layer 3, **Student's t**, which needs the second integral.
* [NIST Digital Library of Mathematical Functions, §5.12](https://dlmf.nist.gov/5.12).
-/

public section

namespace TauCeti

open MeasureTheory ProbabilityTheory Set

variable {a b x : ℝ}

/-- The integrand `t ^ (a - 1) * (1 - t) ^ (b - 1)` of Euler's beta integral is interval
integrable between any two points of `[0, 1]`. Both endpoint singularities are integrable
precisely because the exponents exceed `-1`. -/
theorem intervalIntegrable_rpow_mul_one_sub_rpow (ha : 0 < a) (hb : 0 < b) {u v : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun t : ℝ => t ^ (a - 1) * (1 - t) ^ (b - 1)) volume u v := by
  -- only the singularity at `0` needs an argument; the one at `1` is its mirror image
  have half : ∀ p q : ℝ, 0 < p →
      IntervalIntegrable (fun t : ℝ => t ^ (p - 1) * (1 - t) ^ (q - 1)) volume 0 (1 / 2) := by
    intro p q hp
    refine (intervalIntegral.intervalIntegrable_rpow' (by linarith)).mul_continuousOn ?_
    refine ContinuousOn.rpow_const (by fun_prop) fun t ht => Or.inl ?_
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
    have ht1 : t < 1 := by linarith [ht.2]
    exact sub_ne_zero_of_ne ht1.ne'
  have key : IntervalIntegrable (fun t : ℝ => t ^ (a - 1) * (1 - t) ^ (b - 1)) volume 0 1 := by
    have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    have hright := (half b a hb).comp_sub_left 1
    simp only [sub_zero, sub_sub_cancel] at hright
    have hmul : (fun t : ℝ => (1 - t) ^ (b - 1) * t ^ (a - 1)) =
        fun t : ℝ => t ^ (a - 1) * (1 - t) ^ (b - 1) := by
      ext t
      rw [mul_comm]
    rw [hhalf, hmul] at hright
    exact (half a b ha).trans hright.symm
  refine key.mono_set (uIcc_subset_uIcc ?_ ?_) <;>
    rw [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  exacts [hu, hv]

/-- Euler's beta integral, in real-valued interval form: for positive parameters the integral of
`t ^ (a - 1) * (1 - t) ^ (b - 1)` over `[0, 1]` is `Β(a, b)`. -/
theorem integral_rpow_mul_one_sub_rpow (ha : 0 < a) (hb : 0 < b) :
    ∫ t in (0 : ℝ)..1, t ^ (a - 1) * (1 - t) ^ (b - 1) = beta a b := by
  rw [beta_eq_betaIntegralReal a b ha hb, Complex.betaIntegral,
    intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
    ← RCLike.re_to_complex, ← integral_re]
  · refine setIntegral_congr_fun measurableSet_Ioc fun t ⟨ht0, ht1⟩ ↦ ?_
    norm_cast
    rw [← Complex.ofReal_cpow, ← Complex.ofReal_cpow, RCLike.re_to_complex,
      Complex.re_mul_ofReal, Complex.ofReal_re]
    all_goals linarith
  · convert! Complex.betaIntegral_convergent (u := a) (v := b) (by simpa) (by simpa)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one : (0 : ℝ) ≤ 1), IntegrableOn]

/-- The derivative of the kernel `t ^ a * (1 - t) ^ b` primitivised by the beta integrand. Each
endpoint has to be avoided only when the exponent that degenerates there is smaller than `1`:
`t ^ a` is differentiable at `0` as soon as `1 ≤ a`, and `(1 - t) ^ b` at `1` as soon as
`1 ≤ b`. -/
theorem hasDerivAt_rpow_mul_one_sub_rpow (a b : ℝ) {t : ℝ} (ht0 : t ≠ 0 ∨ 1 ≤ a)
    (ht1 : t ≠ 1 ∨ 1 ≤ b) :
    HasDerivAt (fun t : ℝ => t ^ a * (1 - t) ^ b)
      (a * (t ^ (a - 1) * (1 - t) ^ b) - b * (t ^ a * (1 - t) ^ (b - 1))) t := by
  have h1t : (1 : ℝ) - t ≠ 0 ∨ 1 ≤ b := ht1.imp_left fun ht => sub_ne_zero_of_ne (Ne.symm ht)
  have h₁ : HasDerivAt (fun t : ℝ => t ^ a) (a * t ^ (a - 1)) t :=
    Real.hasDerivAt_rpow_const ht0
  have h₂ : HasDerivAt (fun t : ℝ => (1 - t) ^ b) (b * (1 - t) ^ (b - 1) * (-1)) t :=
    (Real.hasDerivAt_rpow_const h1t).comp t ((hasDerivAt_id t).const_sub 1)
  refine (h₁.mul h₂).congr_deriv ?_
  ring

/-- Raising the second parameter of the beta integrand by one splits its integral as a
difference: off the endpoints
`t ^ (a - 1) * (1 - t) ^ b = t ^ (a - 1) * (1 - t) ^ (b - 1) - t ^ a * (1 - t) ^ (b - 1)`. -/
theorem integral_rpow_mul_one_sub_rpow_add_one_right (ha : 0 < a) (hb : 0 < b)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∫ t in (0 : ℝ)..x, t ^ (a - 1) * (1 - t) ^ b =
      (∫ t in (0 : ℝ)..x, t ^ (a - 1) * (1 - t) ^ (b - 1)) -
        ∫ t in (0 : ℝ)..x, t ^ a * (1 - t) ^ (b - 1) := by
  have hmem : x ∈ Icc (0 : ℝ) 1 := ⟨hx0, hx1⟩
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hI := intervalIntegrable_rpow_mul_one_sub_rpow ha hb hzero hmem
  have hJ : IntervalIntegrable (fun t : ℝ => t ^ a * (1 - t) ^ (b - 1)) volume 0 x := by
    simpa using
      intervalIntegrable_rpow_mul_one_sub_rpow (by linarith : (0 : ℝ) < a + 1) hb hzero hmem
  rw [← intervalIntegral.integral_sub hI hJ]
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
  rw [uIoc_of_le hx0] at ht
  have ht0 : 0 < t := ht.1
  rcases eq_or_lt_of_le (ht.2.trans hx1) with rfl | ht1
  · rw [Real.one_rpow, Real.one_rpow, sub_self, Real.zero_rpow hb.ne']
    ring
  · have h1t : (0 : ℝ) < 1 - t := by linarith
    rw [Real.rpow_sub_one ht0.ne' a, Real.rpow_sub_one h1t.ne' b]
    field_simp

/-! ### Euler's second beta integral -/

section SecondIntegral

variable {s : ℝ}

/-- Under the chart `u ↦ u / (1 - u)` the integrand of Euler's second beta integral becomes the
integrand of Euler's first one. -/
lemma abs_deriv_smul_one_add_rpow (a b : ℝ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    |((1 - u) ^ 2)⁻¹| • ((u / (1 - u)) ^ (a - 1) * (1 + u / (1 - u)) ^ (-(a + b))) =
      u ^ (a - 1) * (1 - u) ^ (b - 1) := by
  obtain ⟨hu0, hu1⟩ := hu
  have h1u : (0 : ℝ) < 1 - u := by linarith
  have hbase : (1 : ℝ) + u / (1 - u) = (1 - u)⁻¹ := by field_simp; ring
  have e1 : ((1 - u) ^ (2 : ℕ))⁻¹ = (1 - u) ^ (-2 : ℝ) := by
    have hneg : (-2 : ℝ) = -(2 : ℕ) := by norm_num
    rw [hneg, Real.rpow_neg h1u.le, Real.rpow_natCast]
  have e2 : ((1 - u)⁻¹) ^ (-(a + b)) = (1 - u) ^ (a + b) := by
    rw [Real.inv_rpow h1u.le, ← Real.rpow_neg h1u.le, neg_neg]
  have e3 : (1 - u) ^ (-2 : ℝ) * (((1 - u) ^ (a - 1))⁻¹ * (1 - u) ^ (a + b)) =
      (1 - u) ^ (b - 1) := by
    rw [← Real.rpow_neg h1u.le, ← Real.rpow_add h1u, ← Real.rpow_add h1u]
    congr 1
    ring
  rw [smul_eq_mul, abs_of_nonneg (by positivity), hbase, Real.div_rpow hu0.le h1u.le, e1, e2,
    div_eq_mul_inv]
  calc (1 - u) ^ (-2 : ℝ) * (u ^ (a - 1) * ((1 - u) ^ (a - 1))⁻¹ * (1 - u) ^ (a + b))
      = u ^ (a - 1) *
        ((1 - u) ^ (-2 : ℝ) * (((1 - u) ^ (a - 1))⁻¹ * (1 - u) ^ (a + b))) := by ring
    _ = u ^ (a - 1) * (1 - u) ^ (b - 1) := by rw [e3]

/-- The integrand of Euler's second beta integral is integrable on the positive half-line
whenever both parameters are positive. -/
theorem integrableOn_rpow_mul_one_add_rpow (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x ^ (a - 1) * (1 + x) ^ (-(a + b))) (Ioi 0) := by
  have hIoo : IntegrableOn (fun t : ℝ => t ^ (a - 1) * (1 - t) ^ (b - 1)) (Ioo 0 1) := by
    refine IntegrableOn.mono_set ?_ Ioo_subset_Ioc_self
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one : (0 : ℝ) ≤ 1)).mp
      (intervalIntegrable_rpow_mul_one_sub_rpow ha hb ⟨le_rfl, zero_le_one⟩
        ⟨zero_le_one, le_rfl⟩)
  have hchart : (fun u : ℝ => u / (1 - u)) '' Ioo (0 : ℝ) 1 = Ioi (0 : ℝ) := by
    rw [image_div_one_sub_Ioo (u0 := 0) zero_lt_one]
    norm_num
  rw [← hchart,
    integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
      (fun u hu => (hasDerivAt_div_one_sub (ne_of_lt hu.2)).hasDerivWithinAt)
      (injOn_div_one_sub_Ioo (u0 := 0))]
  exact hIoo.congr_fun (fun u hu => (abs_deriv_smul_one_add_rpow a b hu).symm) measurableSet_Ioo

/-- **Euler's second beta integral**: for positive parameters the integral of
`x ^ (a - 1) * (1 + x) ^ (-(a + b))` over the positive half-line is `Β(a, b)`. -/
theorem integral_rpow_mul_one_add_rpow (ha : 0 < a) (hb : 0 < b) :
    ∫ x in Ioi (0 : ℝ), x ^ (a - 1) * (1 + x) ^ (-(a + b)) = beta a b := by
  have hchart : (fun u : ℝ => u / (1 - u)) '' Ioo (0 : ℝ) 1 = Ioi (0 : ℝ) := by
    rw [image_div_one_sub_Ioo (u0 := 0) zero_lt_one]
    norm_num
  rw [← hchart,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun u hu => (hasDerivAt_div_one_sub (ne_of_lt hu.2)).hasDerivWithinAt)
      (injOn_div_one_sub_Ioo (u0 := 0)),
    setIntegral_congr_fun measurableSet_Ioo (fun u hu => abs_deriv_smul_one_add_rpow a b hu),
    ← integral_rpow_mul_one_sub_rpow ha hb,
    intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  exact setIntegral_congr_set Ioo_ae_eq_Ioc

/-! ### The Cauchy-type kernel `(1 + x ^ 2) ^ (-s)` -/

/-- The square root carries the positive half-line onto itself. -/
private lemma image_sqrt_Ioi : Real.sqrt '' Ioi 0 = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact Real.sqrt_pos.mpr ht
  · intro hx
    exact ⟨x ^ 2, mem_Ioi.mpr (pow_pos (mem_Ioi.mp hx) 2), Real.sqrt_sq (mem_Ioi.mp hx).le⟩

/-- The square root is injective on the positive half-line. -/
private lemma injOn_sqrt_Ioi : InjOn Real.sqrt (Ioi 0) := by
  intro u hu v hv huv
  have := congrArg (· ^ 2) huv
  simpa [Real.sq_sqrt (mem_Ioi.mp hu).le, Real.sq_sqrt (mem_Ioi.mp hv).le] using this

/-- Under the square root the kernel `(1 + x ^ 2) ^ (-s)` becomes the integrand of Euler's second
beta integral with first parameter `1 / 2`. -/
private lemma abs_deriv_sqrt_smul (s : ℝ) {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    |1 / (2 * Real.sqrt t)| • ((1 + Real.sqrt t ^ 2) ^ (-s)) =
      2⁻¹ * (t ^ (-(1 / 2) : ℝ) * (1 + t) ^ (-s)) := by
  have ht0 : (0 : ℝ) < t := ht
  have hst : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hpow : t ^ (-(1 / 2) : ℝ) = (Real.sqrt t)⁻¹ := by
    rw [Real.rpow_neg ht0.le, Real.sqrt_eq_rpow]
  rw [smul_eq_mul, Real.sq_sqrt ht0.le, abs_of_nonneg (by positivity), hpow]
  field_simp

/-- The Cauchy-type kernel `(1 + x ^ 2) ^ (-s)` is integrable on the line when `1 / 2 < s`. -/
theorem integrable_one_add_sq_rpow (hs : 1 / 2 < s) :
    Integrable (fun x : ℝ => (1 + x ^ 2) ^ (-s)) := by
  have hrs : (Module.finrank ℝ ℝ : ℝ) < 2 * s := by
    simp only [Module.finrank_self]
    norm_num at hs ⊢
    linarith
  convert integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) hrs using 1
  funext x
  simp only [Real.norm_eq_abs, sq_abs]
  ring_nf

/-- The total mass of the Cauchy-type kernel `(1 + x ^ 2) ^ (-s)` is `Β(1/2, s - 1/2)`. -/
theorem integral_one_add_sq_rpow (hs : 1 / 2 < s) :
    ∫ x : ℝ, (1 + x ^ 2) ^ (-s) = beta (1 / 2) (s - 1 / 2) := by
  have hb : (0 : ℝ) < s - 1 / 2 := by linarith
  have hbp := integral_rpow_mul_one_add_rpow (a := 1 / 2) (b := s - 1 / 2) (by norm_num) hb
  have hsum : (1 / 2 : ℝ) + (s - 1 / 2) = s := by ring
  have hsub : (1 / 2 : ℝ) - 1 = -(1 / 2) := by norm_num
  rw [hsum, hsub] at hbp
  have habs : ∫ x : ℝ, (1 + x ^ 2) ^ (-s) = 2 * ∫ x in Ioi (0 : ℝ), (1 + x ^ 2) ^ (-s) := by
    have h := integral_comp_abs (f := fun y : ℝ => (1 + y ^ 2) ^ (-s))
    simp only [sq_abs] at h
    exact h
  rw [habs, ← image_sqrt_Ioi,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun t ht => (Real.hasDerivAt_sqrt (ne_of_gt (mem_Ioi.mp ht))).hasDerivWithinAt)
      injOn_sqrt_Ioi,
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => abs_deriv_sqrt_smul s ht),
    integral_const_mul, hbp]
  ring

/-- Rescaling by `√ν` turns `(1 + x ^ 2 / ν) ^ (-s)` into the Cauchy-type kernel. -/
private lemma one_add_sq_div_eq {ν : ℝ} (hν : 0 < ν) (s x : ℝ) :
    (1 + ((√ν)⁻¹ * x) ^ 2) ^ (-s) = (1 + x ^ 2 / ν) ^ (-s) := by
  rw [mul_pow, inv_pow, Real.sq_sqrt hν.le, inv_mul_eq_div]

/-- The rescaled Cauchy-type kernel is integrable on the line. -/
theorem integrable_one_add_sq_div_rpow {ν s : ℝ} (hν : 0 < ν) (hs : 1 / 2 < s) :
    Integrable fun x : ℝ => (1 + x ^ 2 / ν) ^ (-s) := by
  have hsν : (√ν)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hν).ne'
  have h := (integrable_comp_mul_left_iff
    (fun y : ℝ => (1 + y ^ 2) ^ (-s)) hsν).mpr (integrable_one_add_sq_rpow hs)
  simpa only [one_add_sq_div_eq hν] using h

/-- **The total mass of a rescaled Cauchy-type kernel.** Rescaling by `√ν` reduces it to
Euler's second beta integral. -/
theorem integral_one_add_sq_div_rpow {ν s : ℝ} (hν : 0 < ν) (hs : 1 / 2 < s) :
    ∫ x : ℝ, (1 + x ^ 2 / ν) ^ (-s) = √ν * beta (1 / 2) (s - 1 / 2) := by
  have h := Measure.integral_comp_inv_mul_left (fun y : ℝ => (1 + y ^ 2) ^ (-s)) √ν
  simp only [one_add_sq_div_eq hν, abs_of_nonneg (Real.sqrt_nonneg ν), smul_eq_mul] at h
  rw [h, integral_one_add_sq_rpow hs]

end SecondIntegral

end TauCeti

namespace ProbabilityTheory

variable {a b : ℝ}

/-- Euler's beta function is symmetric in its two parameters. -/
theorem beta_comm (a b : ℝ) : beta a b = beta b a := by
  rw [ProbabilityTheory.beta, ProbabilityTheory.beta, mul_comm (Real.Gamma a), add_comm a b]

/-- Euler's beta function at second parameter `1`. -/
@[simp]
theorem beta_one_right (ha : 0 < a) : beta a 1 = 1 / a := by
  rw [ProbabilityTheory.beta, Real.Gamma_one, mul_one, Real.Gamma_add_one ha.ne']
  field_simp

/-- The unit step of Euler's beta function in its first parameter. -/
theorem beta_add_one_left (ha : a ≠ 0) (hab : a + b ≠ 0) :
    beta (a + 1) b = a / (a + b) * beta a b := by
  have hshift : a + 1 + b = a + b + 1 := by ring
  rw [ProbabilityTheory.beta, ProbabilityTheory.beta, hshift, Real.Gamma_add_one ha,
    Real.Gamma_add_one hab]
  field_simp

end ProbabilityTheory
