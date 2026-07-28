module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import TauCeti.Probability.Distributions.Gaussian.PolynomialMemLp
public import TauCeti.RingTheory.Polynomial.Hermite.Derivative

/-!
# The Gaussian orthogonality relation for the probabilists' Hermite polynomials

Mathlib defines the probabilists' Hermite polynomials `Polynomial.hermite : ℕ → ℤ[X]` and knows the
Gaussian integral `∫ x, exp (-b x²) = √(π / b)`, but it records **no orthogonality relation**
between the Hermite polynomials against the Gaussian weight. This file proves that relation, the
milestone **A1** of the `OrthogonalL2Bases` roadmap
(`TauCetiRoadmap/OrthogonalL2Bases/README.md`, Part A1): the Hermite polynomials are pairwise
orthogonal, and self-paired to `n! · √(2π)`, in `L²` of the Gaussian weight.

* `integrable_aeval_mul_gaussian`: every polynomial is integrable against the Gaussian weight
  `e^{-x²/2}`;
* `integral_aeval_mul_hermite_succ`, the **one-step weighted-pairing recursion**
  `∫ p · H_{n+1} · w = ∫ p' · Hₙ · w`;
* `integral_aeval_mul_hermite`, iterating the recursion, `∫ p · Hₙ · w = ∫ (dⁿ/dxⁿ p) · w`;
* **Milestone (Lebesgue form)** `integral_hermite_mul_hermite_mul_gaussian`:
  `∫ x, Hₘ(x) · Hₙ(x) · e^{-x²/2} = if m = n then n! · √(2π) else 0`, obtained by peeling the larger
  index down to a constant (`Polynomial.iterate_derivative_hermite`);
* **Milestone (Gaussian-measure form)** `integral_hermite_mul_hermite_gaussianReal`:
  `∫ x, Hₘ(x) · Hₙ(x) ∂(gaussianReal 0 1) = if m = n then n! else 0`, the Lebesgue form divided by
  the `√(2π)` density. This is the form the Gaussian Hermite basis (A3′) consumes directly.

The Hermite lowering identities `Polynomial.derivative_hermite`,
`Polynomial.iterate_derivative_hermite` are reused from
`TauCeti/RingTheory/Polynomial/Hermite/Derivative.lean`.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial ProbabilityTheory Real

/-- **Integrability of a polynomial against the Gaussian weight** `e^{-x²/2}`: every real
polynomial, evaluated pointwise and multiplied by the Gaussian weight, is Lebesgue-integrable. -/
theorem integrable_aeval_mul_gaussian (p : ℤ[X]) :
    Integrable (fun x : ℝ => aeval x p * Real.exp (-(x ^ 2 / 2))) := by
  have h := integrable_eval_mul_gaussianEnvelope 0 (p.map (Int.castRingHom ℝ)) (w := 1) one_ne_zero
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [eval_map, aeval_def, algebraMap_int_eq, sub_zero, NNReal.coe_one, mul_one, neg_div]

/-- The Rodrigues-type step behind the recursion, at the level of `aeval`: from Mathlib's defining
recursion `hermite (n+1) = X · hermite n - derivative (hermite n)`,
`H'ₙ(x) = x · Hₙ(x) - H_{n+1}(x)`. -/
private theorem aeval_derivative_hermite (n : ℕ) (x : ℝ) :
    aeval x (derivative (hermite n)) = x * aeval x (hermite n) - aeval x (hermite (n + 1)) := by
  have h : derivative (hermite n) = X * hermite n - hermite (n + 1) := by
    rw [hermite_succ n]; ring
  rw [h, map_sub, map_mul, aeval_X]

/-- A product of two `aeval`s of polynomials against the Gaussian weight `e^{-x²/2}` is
Lebesgue-integrable. -/
private theorem integrable_aeval_mul_aeval_mul_gaussian (p q : ℤ[X]) :
    Integrable (fun x : ℝ => aeval x p * aeval x q * Real.exp (-(x ^ 2 / 2))) := by
  have e : (fun x : ℝ => aeval x p * aeval x q * Real.exp (-(x ^ 2 / 2)))
      = fun x : ℝ => aeval x (p * q) * Real.exp (-(x ^ 2 / 2)) := by
    ext x; rw [map_mul]
  rw [e]; exact integrable_aeval_mul_gaussian _

/-- **One-step weighted-pairing recursion** (target A1): the weighted pairing of `p` with `H_{n+1}`
equals the weighted pairing of its derivative `p'` with `Hₙ`,
`∫ p · H_{n+1} · e^{-x²/2} = ∫ p' · Hₙ · e^{-x²/2}`. -/
theorem integral_aeval_mul_hermite_succ (p : ℤ[X]) (n : ℕ) :
    (∫ x : ℝ, aeval x p * aeval x (hermite (n + 1)) * Real.exp (-(x ^ 2 / 2)))
      = ∫ x : ℝ, aeval x (derivative p) * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2)) := by
  have hderiv : ∀ x : ℝ, HasDerivAt
      (fun x : ℝ => aeval x p * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2)))
      (aeval x (derivative p) * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2))
        - aeval x p * aeval x (hermite (n + 1)) * Real.exp (-(x ^ 2 / 2))) x := by
    intro x
    have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-x) x := by
      have h2 : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-(2 * x / 2)) x := (hsq.div_const 2).neg
      rwa [show -(2 * x / 2) = -x from by ring] at h2
    have hw' : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) (Real.exp (-(x ^ 2 / 2)) * -x) x :=
      h1.exp
    have hbase := ((p.hasDerivAt_aeval x).mul ((hermite n).hasDerivAt_aeval x)).mul hw'
    have hval : aeval x (derivative p) * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2))
        - aeval x p * aeval x (hermite (n + 1)) * Real.exp (-(x ^ 2 / 2))
        = (aeval x (derivative p) * aeval x (hermite n)
            + aeval x p * aeval x (derivative (hermite n))) * Real.exp (-(x ^ 2 / 2))
          + aeval x p * aeval x (hermite n) * (Real.exp (-(x ^ 2 / 2)) * -x) := by
      rw [aeval_derivative_hermite]; ring
    rw [hval]
    exact hbase
  have ht1 := integrable_aeval_mul_aeval_mul_gaussian (derivative p) (hermite n)
  have ht2 := integrable_aeval_mul_aeval_mul_gaussian p (hermite (n + 1))
  have hf := integrable_aeval_mul_aeval_mul_gaussian p (hermite n)
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hderiv (ht1.sub ht2) hf
  rw [integral_sub ht1 ht2] at hzero
  exact (sub_eq_zero.mp hzero).symm

/-- **Iterated recursion**: pairing `p` with `Hₙ` against the Gaussian weight equals pairing the
`n`-th derivative of `p` with `H₀ = 1`, i.e. `∫ p · Hₙ · e^{-x²/2} = ∫ (dⁿ/dxⁿ p) · e^{-x²/2}`. -/
private theorem integral_aeval_mul_hermite (p : ℤ[X]) (n : ℕ) :
    (∫ x : ℝ, aeval x p * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2)))
      = ∫ x : ℝ, aeval x (derivative^[n] p) * Real.exp (-(x ^ 2 / 2)) := by
  induction n generalizing p with
  | zero => simp only [Function.iterate_zero, id_eq, hermite_zero, map_one, mul_one]
  | succ n ih =>
    rw [integral_aeval_mul_hermite_succ, ih (derivative p), Function.iterate_succ_apply]

/-- The Gaussian integral of the bare weight: `∫ x, e^{-x²/2} = √(2π)`. -/
private theorem integral_gaussian_half :
    (∫ x : ℝ, Real.exp (-(x ^ 2 / 2))) = Real.sqrt (2 * π) := by
  have h := integral_gaussian (1 / 2)
  have e : (fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2)) = fun x : ℝ => Real.exp (-(x ^ 2 / 2)) := by
    ext x; rw [show -(1 / 2 : ℝ) * x ^ 2 = -(x ^ 2 / 2) from by ring]
  rw [e] at h
  rw [h, show π / (1 / 2) = 2 * π from by ring]

/-- Commuting the two factors under the integral. -/
private theorem integral_hermite_swap (m n : ℕ) :
    (∫ x : ℝ, aeval x (hermite m) * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2)))
      = ∫ x : ℝ, aeval x (hermite n) * aeval x (hermite m) * Real.exp (-(x ^ 2 / 2)) := by
  congr 1; ext x; ring

/-- **The Hermite orthogonality relation, Lebesgue form** (milestone A1):
`∫ x, Hₘ(x) · Hₙ(x) · e^{-x²/2} = if m = n then n! · √(2π) else 0`. -/
theorem integral_hermite_mul_hermite_mul_gaussian (m n : ℕ) :
    (∫ x : ℝ, aeval x (hermite m) * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2)))
      = if m = n then (n.factorial : ℝ) * Real.sqrt (2 * π) else 0 := by
  rcases lt_trichotomy m n with h | rfl | h
  · rw [if_neg h.ne, integral_aeval_mul_hermite, iterate_derivative_hermite,
      Nat.descFactorial_eq_zero_iff_lt.mpr h]
    simp
  · rw [if_pos rfl, integral_aeval_mul_hermite]
    have hconst : (fun x : ℝ => aeval x (derivative^[m] (hermite m)) * Real.exp (-(x ^ 2 / 2)))
        = fun x : ℝ => (m.factorial : ℝ) * Real.exp (-(x ^ 2 / 2)) := by
      ext x
      rw [iterate_derivative_hermite, Nat.sub_self, Nat.descFactorial_self, hermite_zero]
      simp [nsmul_eq_mul]
    rw [hconst, integral_const_mul, integral_gaussian_half]
  · rw [if_neg h.ne', integral_hermite_swap, integral_aeval_mul_hermite, iterate_derivative_hermite,
      Nat.descFactorial_eq_zero_iff_lt.mpr h]
    simp

/-- The probability-density form of the weight: `gaussianPDFReal 0 1 x = (√(2π))⁻¹ · e^{-x²/2}`. -/
private theorem gaussianPDFReal_zero_one (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [show -x ^ 2 / 2 = -(x ^ 2 / 2) from by ring]

/-- **The Hermite orthogonality relation, Gaussian-measure form** (milestone A1):
`∫ x, Hₘ(x) · Hₙ(x) ∂(gaussianReal 0 1) = if m = n then n! else 0`. This is the Lebesgue form
divided by the `√(2π)` density; it is the relation the Gaussian Hermite basis (A3′) consumes. -/
theorem integral_hermite_mul_hermite_gaussianReal (m n : ℕ) :
    (∫ x : ℝ, aeval x (hermite m) * aeval x (hermite n) ∂(gaussianReal 0 1))
      = if m = n then (n.factorial : ℝ) else 0 := by
  have hne : Real.sqrt (2 * π) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (mul_pos two_pos Real.pi_pos)
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero)]
  simp only [smul_eq_mul]
  rw [show (fun x : ℝ => gaussianPDFReal 0 1 x * (aeval x (hermite m) * aeval x (hermite n)))
        = fun x : ℝ => (Real.sqrt (2 * π))⁻¹
            * (aeval x (hermite m) * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2))) from by
      ext x; rw [gaussianPDFReal_zero_one]; ring,
    integral_const_mul, integral_hermite_mul_hermite_mul_gaussian]
  split_ifs with h
  · rw [mul_comm (n.factorial : ℝ) _, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  · rw [mul_zero]

end TauCeti
