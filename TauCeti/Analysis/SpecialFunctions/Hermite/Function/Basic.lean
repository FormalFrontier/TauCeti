/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import TauCeti.RingTheory.Polynomial.Hermite.Derivative

/-!
# Basic Hermite functions

This file starts the object API for the Hermite functions used by the
`OrthogonalL2Bases` roadmap.  The `n`th function is the normalized
probabilists' Hermite polynomial evaluated at `x * sqrt 2`, multiplied by the
Gaussian envelope `exp (-x^2 / 2)`.

The API here is deliberately pointwise: the definition, continuity and
smoothness, the first three base formulas `ψ₀`, `ψ₁`, and `ψ₂`, and the parity formula
`ψₙ(-x) = (-1)ⁿ ψₙ(x)`. Orthogonality, `L²` packaging, and the oscillator identities are later
milestones built on this basic object.
-/

public section

namespace TauCeti

open Polynomial

/-- The real Hermite function
`ψₙ(x) = Hₙ(x√2) exp(-x² / 2) / sqrt(n! sqrt π)`, using Mathlib's
probabilists' Hermite polynomial `Polynomial.hermite`. -/
noncomputable def hermiteFunction (n : ℕ) (x : ℝ) : ℝ :=
  aeval (x * Real.sqrt 2) (hermite n) * Real.exp (-(x ^ 2 / 2)) /
    Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi)

/-- The defining equation for the real Hermite function. -/
lemma hermiteFunction_def (n : ℕ) (x : ℝ) :
    hermiteFunction n x =
      aeval (x * Real.sqrt 2) (hermite n) * Real.exp (-(x ^ 2 / 2)) /
        Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) :=
  hermiteFunction.eq_1 n x

/-- The square root normalization factor in the Hermite function is positive. -/
lemma sqrt_factorial_mul_sqrt_pi_pos (n : ℕ) :
    0 < Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) := by
  refine Real.sqrt_pos.2 (mul_pos ?_ (Real.sqrt_pos.2 Real.pi_pos))
  positivity

/-- The square root normalization factor in the Hermite function is nonzero. -/
lemma sqrt_factorial_mul_sqrt_pi_ne_zero (n : ℕ) :
    Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) ≠ 0 :=
  (sqrt_factorial_mul_sqrt_pi_pos n).ne'

private noncomputable def gaussianEnvelope (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2 / 2))

@[simp]
private lemma gaussianEnvelope_def (x : ℝ) :
    gaussianEnvelope x = Real.exp (-(x ^ 2 / 2)) :=
  gaussianEnvelope.eq_1 x

private lemma continuous_gaussianEnvelope : Continuous gaussianEnvelope := by
  unfold gaussianEnvelope
  exact Real.continuous_exp.comp (((continuous_id.pow 2).div_const 2).neg)

private lemma contDiff_gaussianEnvelope : ContDiff ℝ ⊤ gaussianEnvelope := by
  unfold gaussianEnvelope
  exact Real.contDiff_exp.comp (((contDiff_id.pow 2).div_const 2).neg)

private lemma continuous_hermiteFunction_poly (n : ℕ) :
    Continuous fun x : ℝ => aeval (x * Real.sqrt 2) (hermite n) :=
  (hermite n).continuous_aeval.comp (continuous_id.mul continuous_const)

private lemma contDiff_hermiteFunction_poly (n : ℕ) :
    ContDiff ℝ ⊤ fun x : ℝ => aeval (x * Real.sqrt 2) (hermite n) :=
  (hermite n).contDiff_aeval ⊤ |>.comp (contDiff_id.mul contDiff_const)

/-- The real Hermite functions are continuous. -/
lemma continuous_hermiteFunction (n : ℕ) : Continuous (hermiteFunction n) := by
  unfold hermiteFunction
  exact ((continuous_hermiteFunction_poly n).mul continuous_gaussianEnvelope).div_const
    (Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi))

/-- The real Hermite functions are smooth. -/
lemma contDiff_hermiteFunction (n : ℕ) : ContDiff ℝ ⊤ (hermiteFunction n) := by
  unfold hermiteFunction
  exact ((contDiff_hermiteFunction_poly n).mul contDiff_gaussianEnvelope).div_const
    (Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi))

/-- The zeroth Hermite function is the Gaussian divided by `sqrt (sqrt π)`. -/
@[simp]
lemma hermiteFunction_zero (x : ℝ) :
    hermiteFunction 0 x = Real.exp (-(x ^ 2 / 2)) / Real.sqrt (Real.sqrt Real.pi) := by
  simp [hermiteFunction]

/-- The first Hermite function is `sqrt 2 * x` times the zeroth Hermite function. -/
@[simp]
lemma hermiteFunction_one (x : ℝ) :
    hermiteFunction 1 x = Real.sqrt 2 * x * hermiteFunction 0 x := by
  rw [hermiteFunction_zero]
  simp only [hermiteFunction, hermite_one, aeval_X, Nat.factorial_one, Nat.cast_one, one_mul]
  ring

/-- The first Hermite function as an explicit scalar multiple of the Gaussian envelope. -/
lemma hermiteFunction_one_eq (x : ℝ) :
    hermiteFunction 1 x =
      Real.sqrt 2 * x * Real.exp (-(x ^ 2 / 2)) / Real.sqrt (Real.sqrt Real.pi) := by
  rw [hermiteFunction_one, hermiteFunction_zero]
  ring

/-- The second probabilists' Hermite polynomial is `X^2 - 1`, evaluated over `ℝ`. -/
private lemma aeval_hermite_two (x : ℝ) :
    aeval x (hermite 2) = x ^ 2 - 1 := by
  rw [Polynomial.hermite_add_two 0, hermite_one, hermite_zero]
  simp [pow_two]

/-- The second Hermite function in pointwise form. -/
lemma hermiteFunction_two (x : ℝ) :
    hermiteFunction 2 x =
      ((x * Real.sqrt 2) ^ 2 - 1) * Real.exp (-(x ^ 2 / 2)) /
        Real.sqrt ((2 : ℝ) * Real.sqrt Real.pi) := by
  rw [hermiteFunction_def, aeval_hermite_two]
  norm_num [Nat.factorial]

/-! ## Parity -/

/-- **Target A2 (parity).** `ψₙ(-x) = (-1)ⁿ ψₙ(x)`: the Gaussian envelope `exp(-x²/2)` is even and
the polynomial factor `Hₙ(x√2)` carries the parity of `Hₙ` (`Polynomial.hermite_aeval_neg`). -/
@[simp]
theorem hermiteFunction_neg (n : ℕ) (x : ℝ) :
    hermiteFunction n (-x) = (-1) ^ n * hermiteFunction n x := by
  have h1 : (-x) * Real.sqrt 2 = -(x * Real.sqrt 2) := by ring
  have h2 : ((-x) ^ 2 / 2 : ℝ) = x ^ 2 / 2 := by ring
  rw [hermiteFunction_def, hermiteFunction_def, h1, Polynomial.hermite_aeval_neg, h2]
  ring

end TauCeti
