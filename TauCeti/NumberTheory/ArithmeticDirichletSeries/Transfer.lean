/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.LogIntegral
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.AbelSummation

/-!
# From the weighted prime count to the unweighted one

A prime-number-theorem argument delivers its conclusion for a *logarithmically weighted* count: a
Tauberian theorem applied to a logarithmic derivative sees the von Mangoldt coefficients, hence the
count `ψ` weighted by `log p` and taken over prime powers, and a separate elementary estimate for
the prime-power contribution passes from `ψ` to the count `ϑ` over primes alone.  The statement one
wants is about the *unweighted* count `π`.  This file carries out that last passage for the primes
of a number field, taking the asymptotic for `ϑ` as given: if `ϑ(x) = δx + o(x)`, then
`π(x) = δ Li(x) + o(x/log x)`, where `Li` is the offset logarithmic integral of
`TauCeti/Analysis/SpecialFunctions/LogIntegral.lean`.

The bridge is the exact Abel-summation identity
`TauCeti.primeCount_eq_primeTheta_div_log_add_integral` of Layer 6.1 together with the
antiderivative identity `TauCeti.Real.logIntegral_eq_div_log_sub_add` for `Li`.  Subtracting the two
cancels the main terms and leaves
`TauCeti.primeCount_sub_mul_logIntegral_eq`, an identity valid for every `x ≥ 2` and every `δ`,
whose three remaining summands are each `o (x / log x)`.

## Main results

* `TauCeti.primeCount_sub_mul_logIntegral_eq`: the exact identity
  `π(x) - δ Li(x) = (ϑ(x) - δx)/log x + ∫ t in 2..x, (ϑ(t) - δt)/(t log² t) + 2δ/log 2`.
* `TauCeti.primeCount_sub_mul_logIntegral_isLittleO`: the transfer itself, stated so that it covers
  the density `δ = 0` as well.
* `TauCeti.primeCount_asymptotic_of_primeTheta`: the quotient form `ϑ(x) ∼ δx ⟹ π(x) ∼ δ Li(x)`
  for `δ ≠ 0`, and `TauCeti.primeCount_isLittleO_logIntegral` for the zero-density case, where an
  asymptotic equivalence would be false and the correct statement is `π(x) = o(Li x)`.

## Roadmap role

This is Layer **6.2** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`, which asks for the
transfer `ϑ(x) ∼ δx ⟹ π(x) ∼ δ Li(x)` "including the zero-density and `δ = 0` cases"; Layer 10.3
exports it as `primeCount_asymptotic_of_primeTheta`.  Nothing here uses an analytic continuation or
a nonvanishing statement: the hypothesis on `ϑ` is taken as given here, and Layer 10 supplies it.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.

Mathlib's `Chebyshev.primeCounting_sub_theta_div_log_isBigO` performs the same partial-summation
step for the rational primes; the argument below follows it, and replaces its explicit Chebyshev
bound by the hypothesis on `ϑ`.
-/

public section

namespace TauCeti

open Asymptotics Filter MeasureTheory
open scoped nonZeroDivisors NumberField
open IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}

/-- The error term `ϑ(t) - δ t` is interval integrable: `ϑ` is monotone and `t ↦ δ t` is
continuous. -/
theorem intervalIntegrable_primeTheta_sub_const_mul (S : Set (HeightOneSpectrum (𝓞 K)))
    (δ a b : ℝ) :
    IntervalIntegrable (fun t ↦ primeTheta K S t - δ * t) volume a b :=
  (primeTheta_mono S).intervalIntegrable.sub
    (Continuous.intervalIntegrable (by fun_prop) a b)

/-- **The exact remainder identity.**  Subtracting `δ Li(x)` from the Abel-summation formula for
`π(x)` cancels the two `x / log x` main terms and leaves a boundary quotient, an integral against
`(t log² t)⁻¹` of the same error term, and the constant coming from the base point `2` of `Li`.

The identity holds for every real `δ`; no hypothesis relating `ϑ` and `δ` is used. -/
theorem primeCount_sub_mul_logIntegral_eq (S : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) {x : ℝ}
    (hx : 2 ≤ x) :
    primeCount K S x - δ * Real.logIntegral x =
      (primeTheta K S x - δ * x) / Real.log x +
        (∫ t in (2 : ℝ)..x, (primeTheta K S t - δ * t) / (t * Real.log t ^ 2)) +
        2 * δ / Real.log 2 := by
  have hsplit : (∫ t in (2 : ℝ)..x, primeTheta K S t / (t * Real.log t ^ 2)) =
      (∫ t in (2 : ℝ)..x, (primeTheta K S t - δ * t) / (t * Real.log t ^ 2)) +
        δ * ∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      (Real.intervalIntegrable_div_mul_log_sq one_lt_two (by linarith)
        (intervalIntegrable_primeTheta_sub_const_mul S δ 2 x))
      ((Real.intervalIntegrable_inv_log_pow 2 one_lt_two (by linarith)).const_mul δ)]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx] at ht
    have h2t : (2 : ℝ) ≤ t := ht.1
    have ht0 : t ≠ 0 := by linarith
    have hlt : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
    field_simp
    ring
  rw [primeCount_eq_primeTheta_div_log_add_integral, ← intervalIntegral.integral_of_le hx, hsplit,
    Real.logIntegral_eq_div_log_sub_add hx, sub_div]
  ring

/-- **The transfer from `ϑ` to `π`.**  If the logarithmically weighted count of the primes of `S`
satisfies `ϑ(x) = δx + o(x)`, then the unweighted count satisfies `π(x) = δ Li(x) + o(x/log x)`.

Stated with an error term rather than as an equivalence, this covers `δ = 0` as well; the two
quotient forms are `TauCeti.primeCount_asymptotic_of_primeTheta` and
`TauCeti.primeCount_isLittleO_logIntegral`. -/
theorem primeCount_sub_mul_logIntegral_isLittleO
    (h : (fun x ↦ primeTheta K S x - δ * x) =o[atTop] id) :
    (fun x ↦ primeCount K S x - δ * Real.logIntegral x) =o[atTop] fun x : ℝ ↦ x / Real.log x := by
  have hboundary : (fun x ↦ (primeTheta K S x - δ * x) / Real.log x) =o[atTop]
      fun x : ℝ ↦ x / Real.log x := by
    simpa [div_eq_mul_inv] using
      h.mul_isBigO (isBigO_refl (fun x : ℝ ↦ (Real.log x)⁻¹) atTop)
  have hintegral :
      (fun x ↦ ∫ t in (2 : ℝ)..x, (primeTheta K S t - δ * t) / (t * Real.log t ^ 2)) =o[atTop]
        fun x : ℝ ↦ x / Real.log x :=
    Real.isLittleO_integral_div_mul_log_sq
      (fun x _ ↦ intervalIntegrable_primeTheta_sub_const_mul S δ 2 x) h.isBigO
  have hconst := Real.isLittleO_const_div_log (2 * δ / Real.log 2)
  refine ((hboundary.add hintegral).add hconst).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  exact (primeCount_sub_mul_logIntegral_eq S δ hx).symm

/-- **The zero-density case.**  If the logarithmically weighted count of `S` is `o(x)`, then `S`
contains `o(Li x)` primes up to `x`.  An asymptotic equivalence is *not* the right statement here:
`π ~ 0` would force `π` to vanish eventually. -/
theorem primeCount_isLittleO_logIntegral (h : primeTheta K S =o[atTop] id) :
    primeCount K S =o[atTop] Real.logIntegral := by
  have h0 : (fun x ↦ primeCount K S x - (0 : ℝ) * Real.logIntegral x) =o[atTop]
      fun x : ℝ ↦ x / Real.log x :=
    primeCount_sub_mul_logIntegral_isLittleO (by simpa using h)
  simpa using h0.trans_isBigO Real.logIntegral_isEquivalent_div_log.isBigO_symm

/-- **`ϑ(x) ∼ δx` implies `π(x) ∼ δ Li(x)`,** for a nonzero density `δ`.  This is the transfer the
prime-number-theorem chain consumes: Layer 10 produces the asymptotic for `ϑ` from a Tauberian
theorem, and this turns it into one for `π`. -/
theorem primeCount_asymptotic_of_primeTheta (hδ : δ ≠ 0)
    (h : primeTheta K S ~[atTop] fun x ↦ δ * x) :
    primeCount K S ~[atTop] fun x ↦ δ * Real.logIntegral x := by
  have hlin : (fun x : ℝ ↦ δ * x) =O[atTop] (id : ℝ → ℝ) :=
    (isBigO_refl (id : ℝ → ℝ) atTop).const_mul_left δ
  have h' : (fun x ↦ primeTheta K S x - δ * x) =o[atTop] id :=
    h.isLittleO.trans_isBigO hlin
  exact (primeCount_sub_mul_logIntegral_isLittleO h').trans_isBigO
    (Real.logIntegral_isEquivalent_div_log.isBigO_symm.const_mul_right hδ)

end TauCeti
