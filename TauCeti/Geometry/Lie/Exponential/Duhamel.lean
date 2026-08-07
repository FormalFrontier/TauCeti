/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Duhamel's formula for the Banach-algebra exponential

This file expresses a finite increment of the exponential in a possibly noncommutative real
Banach algebra as an integral. Unlike a first-order derivative formula, the identity is exact for
every increment.

## Main result

* `exp_add_sub_exp_eq_integral`: `exp (x + h) - exp x` is the integral of
  `exp ((1 - t) (x + h)) * h * exp (t x)` over the unit interval.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "Differential of the exponential".
-/

public section

open NormedSpace MeasureTheory

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- The rational normed algebra structure obtained by restricting the real scalars. -/
noncomputable local instance normedAlgebraRatOfReal : NormedAlgebra ℚ A :=
  .restrictScalars ℚ ℝ A

private theorem hasDerivAt_duhamelPath (x h : A) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ exp ((1 - s) • (x + h)) * exp (s • x))
      (-(exp ((1 - t) • (x + h)) * h * exp (t • x))) t := by
  have hleft : HasDerivAt
      (fun s : ℝ ↦ exp ((1 - s) • (x + h)))
      (-(exp ((1 - t) • (x + h)) * (x + h))) t := by
    exact (hasDerivAt_exp_smul_const (x + h) (1 - t)).comp_const_sub 1 t
  have hright : HasDerivAt
      (fun s : ℝ ↦ exp (s • x))
      (x * exp (t • x)) t :=
    hasDerivAt_exp_smul_const' x t
  convert hleft.mul hright using 1
  · ext s
    rfl
  · noncomm_ring

/-- Duhamel's exact finite-increment formula for the exponential in a possibly noncommutative real
Banach algebra. -/
theorem exp_add_sub_exp_eq_integral (x h : A) :
    exp (x + h) - exp x =
      ∫ t in (0 : ℝ)..1, exp ((1 - t) • (x + h)) * h * exp (t • x) := by
  let F : ℝ → A := fun t ↦ exp ((1 - t) • (x + h)) * exp (t • x)
  let F' : ℝ → A := fun t ↦ -(exp ((1 - t) • (x + h)) * h * exp (t • x))
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F (F' t) t := by
    intro t _ht
    exact hasDerivAt_duhamelPath x h t
  have hint : IntervalIntegrable F' volume (0 : ℝ) 1 := by
    exact Continuous.intervalIntegrable (μ := volume) (by fun_prop) 0 1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  dsimp only [F, F'] at hFTC
  simp only [one_smul, sub_self, sub_zero, zero_smul, exp_zero, mul_one, one_mul,
    intervalIntegral.integral_neg] at hFTC
  have hneg := congrArg Neg.neg hFTC
  simpa only [neg_neg, neg_sub] using hneg.symm
