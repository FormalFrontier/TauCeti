/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# The exponential generating function of the probabilists' Hermite polynomials

Mathlib defines `Polynomial.hermite` by the one-step recursion
`hermite (n + 1) = X * hermite n - derivative (hermite n)` and develops its coefficient and
derivative API, but it records nothing about the classical exponential generating function

  `∑' n, Hₙ(x) · tⁿ / n! = exp (x · t - t² / 2)`.

This file proves that identity (target **A1** of the `OrthogonalL2Bases` roadmap, listed in
`TauCetiRoadmap/OrthogonalL2Bases/README.md` and `Suggested.lean`). It is the analytic companion of
the algebraic Hermite recurrences: the generating function is the standard tool that packages the
whole family at once and, together with the weighted-orthogonality integral, drives the
orthogonal-polynomial completeness arguments the roadmap builds on.

## Proof outline

Fix `x : ℂ` and work with the entire function `f z = exp (x·z - z²/2)` on `ℂ`. A short induction on
`n`, using only the chain rule and the defining recursion `hermite (n + 1) = X · hermite n -
derivative (hermite n)`, evaluates its iterated derivatives in closed form,

  `iteratedDeriv n f z = aeval (x - z) (hermite n) · f z`,

so at the base point `z = 0` (where `f 0 = 1`) we get `iteratedDeriv n f 0 = Hₙ(x)`. Because `f` is
complex differentiable everywhere, Mathlib's `Complex.hasSum_taylorSeries_of_entire` says `f` equals
its Taylor series about `0` at every point, which is exactly the summability statement of the
generating function at an arbitrary complex `t`.

The primary statement is the complex `HasSum` form `TauCeti.hasSum_hermite_generating_function`,
which is where the analytic content actually lives; the real `tsum` form
`TauCeti.hermite_generating_function` (the roadmap target A1) follows from it by casting `ℝ → ℂ`.
-/

public section

namespace TauCeti

open Polynomial Complex

/-- Derivative of the entire function `z ↦ exp (x·z - z²/2)`: its value at `z` times `x - z`. -/
private theorem hasDerivAt_cexp_quadratic (x z : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.exp (x * w - w ^ 2 / 2))
      (Complex.exp (x * z - z ^ 2 / 2) * (x - z)) z := by
  have hu : HasDerivAt (fun w : ℂ => x * w - w ^ 2 / 2) (x - z) z := by
    have h1 : HasDerivAt (fun w : ℂ => x * w) (x * 1) z :=
      (hasDerivAt_id z).const_mul _
    have h2 := (hasDerivAt_pow 2 z).div_const (2 : ℂ)
    have hv : x * 1 - ((2 : ℕ) : ℂ) * z ^ (2 - 1) / 2 = x - z := by
      have he : (2 : ℕ) - 1 = 1 := rfl
      rw [he, pow_one]
      push_cast
      ring
    have h3 := h1.sub h2
    rw [hv] at h3
    exact h3
  exact hu.cexp

/-- Closed form for the iterated derivatives of `z ↦ exp (x·z - z²/2)`: the `n`-th derivative at
`z` is `Hₙ(x - z)` times the function value, proved by induction on `n` from the defining recursion
`hermite (n + 1) = X · hermite n - derivative (hermite n)`. -/
private theorem iteratedDeriv_cexp_quadratic (x : ℂ) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun w : ℂ => Complex.exp (x * w - w ^ 2 / 2)) z
      = aeval (x - z) (hermite n) * Complex.exp (x * z - z ^ 2 / 2) := by
  induction n generalizing z with
  | zero => simp [iteratedDeriv_zero, hermite_zero]
  | succ n ih =>
    have hfun : iteratedDeriv n (fun w : ℂ => Complex.exp (x * w - w ^ 2 / 2))
        = fun z : ℂ => aeval (x - z) (hermite n) * Complex.exp (x * z - z ^ 2 / 2) :=
      funext ih
    have hP : HasDerivAt (fun z : ℂ => aeval (x - z) (hermite n))
        (-aeval (x - z) (derivative (hermite n))) z := by
      have h1 : HasDerivAt (fun w : ℂ => x - w) (-1) z := by
        simpa using (hasDerivAt_id z).const_sub x
      have h3 := ((hermite n).hasDerivAt_aeval (x - z)).comp z h1
      simpa [Function.comp_def, mul_neg_one] using h3
    have hHD : HasDerivAt (iteratedDeriv n (fun w : ℂ => Complex.exp (x * w - w ^ 2 / 2)))
        (-aeval (x - z) (derivative (hermite n)) * Complex.exp (x * z - z ^ 2 / 2)
          + aeval (x - z) (hermite n) * (Complex.exp (x * z - z ^ 2 / 2) * (x - z))) z := by
      rw [hfun]
      exact hP.mul (hasDerivAt_cexp_quadratic x z)
    rw [iteratedDeriv_succ, hHD.deriv, hermite_succ]
    simp only [map_sub, map_mul, aeval_X]
    ring

/-- **Exponential generating function of the probabilists' Hermite polynomials, summable form.**
For all complex `x` and `t`, the family `Hₙ(x) · tⁿ / n!` is summable with sum
`exp (x · t - t² / 2)`, where `Hₙ = Polynomial.hermite n`.

This is the analytic heart of the identity: it carries the summability that the `tsum` form
`hermite_generating_function` discards, and it holds over all of `ℂ` (the real case is a
specialization by casting). -/
theorem hasSum_hermite_generating_function (x t : ℂ) :
    HasSum (fun n : ℕ => aeval x (hermite n) * t ^ n / (n.factorial : ℂ))
      (Complex.exp (x * t - t ^ 2 / 2)) := by
  -- The entire function `f z = exp (x·z - z²/2)` on the complex plane.
  set f : ℂ → ℂ := fun z => Complex.exp (x * z - z ^ 2 / 2) with hf_def
  have hf_diff : Differentiable ℂ f := by
    rw [hf_def]
    exact fun z => (hasDerivAt_cexp_quadratic x z).differentiableAt
  -- Evaluating the iterated-derivative closed form at `z = 0` gives `iteratedDeriv n f 0 = Hₙ(x)`.
  have hval : ∀ n : ℕ, iteratedDeriv n f 0 = aeval x (hermite n) := by
    intro n
    rw [hf_def, iteratedDeriv_cexp_quadratic]
    simp
  -- `f` equals its Taylor series about `0`; specialize at `t`.
  have htaylor := hasSum_taylorSeries_of_entire hf_diff 0 t
  -- Rewrite the Taylor terms into the generating-function terms.
  have hfun_eq :
      (fun n : ℕ => (n.factorial : ℂ)⁻¹ • (t - 0) ^ n • iteratedDeriv n f 0)
        = fun n : ℕ => aeval x (hermite n) * t ^ n / (n.factorial : ℂ) := by
    funext n
    rw [hval n]
    simp only [sub_zero, smul_eq_mul]
    ring
  -- The value of `f` at `t` is the exponential on the right-hand side.
  have hft : f t = Complex.exp (x * t - t ^ 2 / 2) := by rw [hf_def]
  rw [hfun_eq, hft] at htaylor
  exact htaylor

/-- **Exponential generating function of the probabilists' Hermite polynomials.** For all real `x`
and `t`,
`∑' n, Hₙ(x) · tⁿ / n! = exp (x · t - t² / 2)`,
where `Hₙ = Polynomial.hermite n`. This is target **A1** of the `OrthogonalL2Bases` roadmap; it is
the real specialization of `hasSum_hermite_generating_function`. -/
theorem hermite_generating_function (x t : ℝ) :
    ∑' n : ℕ, aeval x (hermite n) * t ^ n / (n.factorial : ℝ)
      = Real.exp (x * t - t ^ 2 / 2) := by
  -- Compatibility of `aeval` with the coercion `ℝ → ℂ`.
  have hcast_aeval : ∀ n : ℕ, ((aeval x (hermite n) : ℝ) : ℂ) = aeval (x : ℂ) (hermite n) := by
    intro n
    have h : (algebraMap ℤ ℂ).comp (RingHom.id ℤ) = (algebraMap ℝ ℂ).comp (algebraMap ℤ ℝ) := by
      ext k; simp
    simpa [Polynomial.map_id, Complex.coe_algebraMap] using
      map_aeval_eq_aeval_map h (hermite n) x
  -- Cast the complex `HasSum` down to `ℝ`, then read off the `tsum`.
  have hsum : HasSum (fun n : ℕ => aeval x (hermite n) * t ^ n / (n.factorial : ℝ))
      (Real.exp (x * t - t ^ 2 / 2)) := by
    rw [← Complex.hasSum_ofReal]
    have hterm : ∀ n : ℕ,
        ((aeval x (hermite n) * t ^ n / (n.factorial : ℝ) : ℝ) : ℂ)
          = aeval (x : ℂ) (hermite n) * (t : ℂ) ^ n / (n.factorial : ℂ) := by
      intro n
      rw [← hcast_aeval n]
      push_cast
      ring
    have hexp : ((Real.exp (x * t - t ^ 2 / 2) : ℝ) : ℂ)
        = Complex.exp ((x : ℂ) * (t : ℂ) - (t : ℂ) ^ 2 / 2) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    simp only [hterm, hexp]
    exact hasSum_hermite_generating_function (x : ℂ) (t : ℂ)
  exact hsum.tsum_eq

end TauCeti
