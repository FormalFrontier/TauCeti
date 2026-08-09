/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Bochner.CharFun.PositiveDefinite
public import TauCeti.Analysis.PositiveDefinite.Pullback
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# The Gaussian is a positive-definite function

The Gaussian `a ↦ exp (-c‖a‖²)` on a finite-dimensional real inner-product space `V` is
continuous and positive definite for every `c ≥ 0`. This supplies the positive-definiteness
half of the Gaussian acceptance example requested in Part C of the `OneParameterSemigroups`
roadmap in TauCetiRoadmap ("positive-definite functions and Bochner's theorem"); the
representing-measure half is a later Bochner-representation milestone.

The positive-definiteness is not proved from scratch: Mathlib's
`ProbabilityTheory.charFun_stdGaussian` computes the characteristic function of the standard
Gaussian measure on `V` to be `t ↦ exp (-‖t‖²/2)`, and
`TauCeti.charFun_isPositiveDefinite_of_star_eq_neg` (the finite-measure Fourier-transform
correspondence) already records that a characteristic function is positive definite for the
negation involution `a⋆ = -a`. Rescaling the argument by `√(2c)` turns `exp (-‖·‖²/2)` into
`exp (-c‖·‖²)`.

## Main declarations

* `TauCeti.charFun_stdGaussian_sqrt_smul`: `charFun (stdGaussian V) (√(2c) • a) = exp (-c‖a‖²)`.
* `TauCeti.isPositiveDefinite_cexp_neg_mul_sq_norm`: `a ↦ exp (-c‖a‖²)` is positive definite for
  `c ≥ 0` under the negation involution.
* `TauCeti.isPositiveDefiniteKernel_cexp_neg_mul_sq_norm`: the involution-free kernel form,
  `(a, b) ↦ exp (-c‖a - b‖²)` is a positive-definite kernel.
* `TauCeti.continuous_cexp_neg_mul_sq_norm`: `a ↦ exp (-c‖a‖²)` is continuous.
* `TauCeti.isPositiveDefinite_cexp_neg_sq_norm`: the positive-definiteness half of the Gaussian
  acceptance example (`c = 1`), `a ↦ exp (-‖a‖²)`.
* `TauCeti.isPositiveDefiniteKernel_cexp_neg_sq_norm`: the involution-free kernel form of the
  `c = 1` acceptance example, `(a, b) ↦ exp (-‖a - b‖²)`.

## References

* W. Rudin, *Fourier Analysis on Groups* (1962) — Bochner's theorem and positive-definite
  functions.
* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

open MeasureTheory ProbabilityTheory Complex
open scoped ComplexOrder

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The Gaussian `a ↦ exp (-c‖a‖²)` is continuous on `V` for every real `c`. -/
theorem continuous_cexp_neg_mul_sq_norm (c : ℝ) :
    Continuous fun a : V => Complex.exp (-(c * ‖a‖ ^ 2 : ℝ)) := by
  fun_prop

/-- The characteristic function of the standard Gaussian measure on `V`, with its argument
rescaled by `√(2c)`, is the Gaussian `a ↦ exp (-c‖a‖²)`. -/
theorem charFun_stdGaussian_sqrt_smul {c : ℝ} (hc : 0 ≤ c) (a : V) :
    charFun (stdGaussian V) (Real.sqrt (2 * c) • a) = Complex.exp (-(c * ‖a‖ ^ 2 : ℝ)) := by
  have hsq : Real.sqrt (2 * c) ^ 2 = 2 * c := Real.sq_sqrt (by positivity)
  have hn : ‖(Real.sqrt (2 * c)) • a‖ ^ 2 = 2 * c * ‖a‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, hsq]
  rw [charFun_stdGaussian, ← Complex.ofReal_pow, hn]
  congr 1
  push_cast
  ring

/-- The Gaussian `a ↦ exp (-c‖a‖²)` on a finite-dimensional real inner-product space is positive
definite for every `c ≥ 0`, under the negation involution `a⋆ = -a`.

It is the characteristic function of the standard Gaussian measure with the argument rescaled
by `√(2c)`. -/
theorem isPositiveDefinite_cexp_neg_mul_sq_norm [StarAddMonoid V]
    (hstar : ∀ x : V, star x = -x) {c : ℝ} (hc : 0 ≤ c) :
    IsPositiveDefinite fun a : V => Complex.exp (-(c * ‖a‖ ^ 2 : ℝ)) := by
  have hpull := (charFun_isPositiveDefinite_of_star_eq_neg (μ := stdGaussian V)
    hstar).comp_smul hstar (Real.sqrt (2 * c))
  have heq : (fun a : V => Complex.exp (-(c * ‖a‖ ^ 2 : ℝ)))
      = fun a : V => charFun (stdGaussian V) (Real.sqrt (2 * c) • a) := by
    funext a
    exact (charFun_stdGaussian_sqrt_smul hc a).symm
  rw [heq]
  exact hpull

/-- The translation-invariant kernel attached to the Gaussian, `(a, b) ↦ exp (-c‖a - b‖²)`, is
positive definite for every `c ≥ 0`. This is the kernel form of
`isPositiveDefinite_cexp_neg_mul_sq_norm`, avoiding any explicit choice of involution on the
domain. -/
theorem isPositiveDefiniteKernel_cexp_neg_mul_sq_norm {c : ℝ} (hc : 0 ≤ c) :
    IsPositiveDefiniteKernel fun a b : V => Complex.exp (-(c * ‖a - b‖ ^ 2 : ℝ)) := by
  have hscaled := isPositiveDefiniteKernel_comp
    (charFun_isPositiveDefiniteKernel (μ := stdGaussian V))
    (fun a : V => Real.sqrt (2 * c) • a)
  have heq : (fun a b : V => Complex.exp (-(c * ‖a - b‖ ^ 2 : ℝ)))
      = fun a b : V => charFun (stdGaussian V)
        (Real.sqrt (2 * c) • a - Real.sqrt (2 * c) • b) := by
    funext a b
    rw [← smul_sub, charFun_stdGaussian_sqrt_smul hc]
  rw [heq]
  exact hscaled

/-- The positive-definiteness half of the Gaussian acceptance example (`c = 1`):
`a ↦ exp (-‖a‖²)` is positive definite under the negation involution. -/
theorem isPositiveDefinite_cexp_neg_sq_norm [StarAddMonoid V] (hstar : ∀ x : V, star x = -x) :
    IsPositiveDefinite fun a : V => Complex.exp (-(‖a‖ ^ 2 : ℝ)) := by
  simpa only [one_mul] using
    isPositiveDefinite_cexp_neg_mul_sq_norm hstar (V := V) (c := 1) zero_le_one

/-- The involution-free kernel form of the Gaussian acceptance example (`c = 1`):
`(a, b) ↦ exp (-‖a - b‖²)` is a positive-definite kernel. Unlike
`isPositiveDefinite_cexp_neg_sq_norm`, this requires no choice of involution on `V`. -/
theorem isPositiveDefiniteKernel_cexp_neg_sq_norm :
    IsPositiveDefiniteKernel fun a b : V => Complex.exp (-(‖a - b‖ ^ 2 : ℝ)) := by
  simpa only [one_mul] using
    isPositiveDefiniteKernel_cexp_neg_mul_sq_norm (V := V) (c := 1) zero_le_one

end TauCeti
