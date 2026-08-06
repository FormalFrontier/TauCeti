/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# The regularized exponential quotient

This file packages the everywhere-defined power series representing `(1 - exp (-a)) / a` without
requiring `a` to be invertible. This is the analytic factor in the differential of a Lie-group
exponential map.

## Main results

* `regularizedExpNeg`: the convergent series `∑ n, (n + 1)!⁻¹ • (-a)ⁿ`.
* `regularizedExpNeg_eq_tsum`: the defining series exposed across module boundaries.
* `regularizedExpNeg_commute`: the series commutes with its argument.
* `mul_regularizedExpNeg`: multiplying the series by `a` gives `1 - exp (-a)`.
* `regularizedExpNeg_mul`: the corresponding right-multiplication identity.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The conjugation formulas".
* Mathlib's `spectrum.exp_mem_exp`, whose proof supplies the shifted-exponential series argument
  adapted here.
-/

public section

open NormedSpace

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- The regularized value of `(1 - exp (-a)) / a`, defined by its everywhere-convergent power
series. At a noninvertible `a`, the series rather than the quotient is the definition. -/
noncomputable def regularizedExpNeg (a : A) : A :=
  ∑' n : ℕ, ((n + 1).factorial⁻¹ : ℝ) • (-a) ^ n

omit [CompleteSpace A] in
/-- The defining series for the regularized exponential quotient. -/
theorem regularizedExpNeg_eq_tsum (a : A) :
    regularizedExpNeg a = ∑' n : ℕ, (((n + 1).factorial)⁻¹ : ℝ) • (-a) ^ n := by
  rw [regularizedExpNeg]

private theorem summable_regularizedExpNeg (a : A) :
    Summable fun n : ℕ ↦ ((n + 1).factorial⁻¹ : ℝ) • (-a) ^ n := by
  refine .of_norm_bounded_eventually (Real.summable_pow_div_factorial ‖-a‖) ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
  rw [norm_smul, mul_comm, norm_inv, Real.norm_natCast, ← div_eq_mul_inv]
  gcongr
  · exact norm_pow_le' _ (pos_iff_ne_zero.mpr hn)
  · exact n.le_succ

/-- The regularized exponential quotient takes the removable value `1` at zero. -/
@[simp]
theorem regularizedExpNeg_zero : regularizedExpNeg (0 : A) = 1 := by
  rw [regularizedExpNeg]
  convert (summable_regularizedExpNeg (0 : A)).tsum_eq_zero_add using 1
  all_goals simp

private theorem exp_neg_eq_one_add_mul_regularizedExpNeg (a : A) :
    exp (-a) = 1 + (-a) * regularizedExpNeg a := by
  have hmul :
      (∑' n : ℕ, ((n + 1).factorial⁻¹ : ℝ) • (-a) ^ (n + 1)) =
        (-a) * regularizedExpNeg a := by
    simpa only [regularizedExpNeg, mul_smul_comm, pow_succ'] using
      (summable_regularizedExpNeg a).tsum_mul_left (-a)
  rw [exp_eq_tsum ℝ]
  convert! (expSeries_summable' (𝕂 := ℝ) (-a)).tsum_eq_zero_add
  · simp
  · exact hmul.symm

/-- Multiplying the regularized quotient on the left by its argument recovers its numerator. -/
theorem mul_regularizedExpNeg (a : A) :
    a * regularizedExpNeg a = 1 - exp (-a) := by
  rw [exp_neg_eq_one_add_mul_regularizedExpNeg]
  noncomm_ring

omit [CompleteSpace A] in
/-- The regularized exponential quotient commutes with its argument. -/
theorem regularizedExpNeg_commute (a : A) : Commute a (regularizedExpNeg a) := by
  rw [regularizedExpNeg_eq_tsum]
  exact Commute.tsum_right _ fun n ↦ ((Commute.refl a).neg_right.pow_right n).smul_right _

/-- Multiplying the regularized quotient on the right by its argument recovers its numerator. -/
theorem regularizedExpNeg_mul (a : A) :
    regularizedExpNeg a * a = 1 - exp (-a) := by
  rw [← (regularizedExpNeg_commute a).eq, mul_regularizedExpNeg]
