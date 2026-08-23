/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Beta

/-!
# Euler's beta integral, in real-valued interval form

Mathlib defines Euler's beta function `ProbabilityTheory.beta` by the Gamma quotient, and proves
that it is the value of `Complex.betaIntegral`, the complex-valued interval integral of
`t ^ (a - 1) * (1 - t) ^ (b - 1)` over `[0, 1]`. This file records the real-variable facts about
the real-valued beta integrand `t ^ (a - 1) * (1 - t) ^ (b - 1)` that a real-analysis consumer
needs: its interval integrability on `[0, 1]`, the value `Β(a, b)` of its
integral over `[0, 1]`, the derivative of the kernel `t ^ a * (1 - t) ^ b` it primitivises, and
the splitting of the integrand that raises the second parameter by one. Two parameter identities
for `Β` itself — symmetry and the unit step in the first parameter — are recorded alongside.

These are the analytic prerequisites of
`TauCeti/Analysis/SpecialFunctions/IncompleteBeta.lean`, and
`TauCeti/Probability/Distributions/Beta.lean` uses the beta integral for its moment formula.

## Main results

* `TauCeti.intervalIntegrable_rpow_mul_one_sub_rpow` — interval integrability of the beta
  integrand between any two points of `[0, 1]`;
* `TauCeti.integral_rpow_mul_one_sub_rpow` — Euler's beta integral,
  `∫ t in 0..1, t ^ (a - 1) * (1 - t) ^ (b - 1) = Β(a, b)`;
* `TauCeti.hasDerivAt_rpow_mul_one_sub_rpow` — the derivative of `t ^ a * (1 - t) ^ b`;
* `TauCeti.integral_rpow_mul_one_sub_rpow_add_one_right` — raising the second parameter by one
  splits the integral as a difference;
* `ProbabilityTheory.beta_comm` — symmetry of `Β`;
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

## References

* Tau Ceti roadmap, `StandardDistributions`, Layer 2, "Regularized incomplete beta", for which
  these are the prerequisites.
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

end TauCeti

namespace ProbabilityTheory

variable {a b : ℝ}

/-- Euler's beta function is symmetric in its two parameters. -/
theorem beta_comm (a b : ℝ) : beta a b = beta b a := by
  rw [ProbabilityTheory.beta, ProbabilityTheory.beta, mul_comm (Real.Gamma a), add_comm a b]

/-- The unit step of Euler's beta function in its first parameter. -/
theorem beta_add_one_left (ha : a ≠ 0) (hab : a + b ≠ 0) :
    beta (a + 1) b = a / (a + b) * beta a b := by
  have hshift : a + 1 + b = a + b + 1 := by ring
  rw [ProbabilityTheory.beta, ProbabilityTheory.beta, hshift, Real.Gamma_add_one ha,
    Real.Gamma_add_one hab]
  field_simp

end ProbabilityTheory
