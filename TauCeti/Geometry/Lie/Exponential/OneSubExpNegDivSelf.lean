/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# The quotient `(1 - exp (-a)) / a`

This file packages the power series representing `(1 - exp (-a)) / a` without requiring `a` to be
invertible. In a complete normed algebra the series is summable at every point. It is the analytic
factor in the differential of a Lie-group exponential map.

## Main results

* `oneSubExpNegDivSelf`: the series `∑ n, (n + 1)!⁻¹ • (-a)ⁿ`.
* `summable_oneSubExpNegDivSelf`: the series is summable in a complete normed algebra.
* `oneSubExpNegDivSelf_commute`: the series commutes with its argument.
* `mul_oneSubExpNegDivSelf`: multiplying the series by `a` gives `1 - exp (-a)`.
* `oneSubExpNegDivSelf_mul`: the corresponding right-multiplication identity.

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

/-- The value of `(1 - exp (-a)) / a` with its removable singularity filled in, defined by a power
series. The series is summable everywhere when `A` is complete. -/
noncomputable def oneSubExpNegDivSelf (a : A) : A :=
  ∑' n : ℕ, ((n + 1).factorial⁻¹ : ℝ) • (-a) ^ n

omit [CompleteSpace A] in
/-- The defining series for `oneSubExpNegDivSelf`. -/
theorem oneSubExpNegDivSelf_eq_tsum (a : A) :
    oneSubExpNegDivSelf a = ∑' n : ℕ, (((n + 1).factorial)⁻¹ : ℝ) • (-a) ^ n := by
  rw [oneSubExpNegDivSelf]

/-- The series defining `oneSubExpNegDivSelf` is summable in a complete normed algebra. -/
theorem summable_oneSubExpNegDivSelf (a : A) :
    Summable fun n : ℕ ↦ ((n + 1).factorial⁻¹ : ℝ) • (-a) ^ n := by
  refine .of_norm_bounded_eventually (Real.summable_pow_div_factorial ‖-a‖) ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
  rw [norm_smul, mul_comm, norm_inv, Real.norm_natCast, ← div_eq_mul_inv]
  gcongr
  · exact norm_pow_le' _ (pos_iff_ne_zero.mpr hn)
  · exact n.le_succ

omit [CompleteSpace A] in
/-- The quotient with its removable singularity filled in takes the value `1` at zero. -/
@[simp]
theorem oneSubExpNegDivSelf_zero : oneSubExpNegDivSelf (0 : A) = 1 := by
  rw [oneSubExpNegDivSelf_eq_tsum, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

/-- Multiplying the filled-in quotient on the left by its argument recovers its numerator. -/
theorem mul_oneSubExpNegDivSelf (a : A) :
    a * oneSubExpNegDivSelf a = 1 - exp (-a) := by
  have hmul :
      (∑' n : ℕ, ((n + 1).factorial⁻¹ : ℝ) • (-a) ^ (n + 1)) =
        (-a) * oneSubExpNegDivSelf a := by
    simpa only [oneSubExpNegDivSelf, mul_smul_comm, pow_succ'] using
      (summable_oneSubExpNegDivSelf a).tsum_mul_left (-a)
  rw [exp_eq_tsum ℝ]
  change a * oneSubExpNegDivSelf a =
    1 - ∑' n : ℕ, ((n.factorial : ℝ)⁻¹ : ℝ) • (-a) ^ n
  rw [(expSeries_summable' (𝕂 := ℝ) (-a)).tsum_eq_zero_add]
  rw [show ((0 : ℕ).factorial : ℝ)⁻¹ • (-a) ^ 0 = 1 by simp, hmul]
  noncomm_ring

omit [CompleteSpace A] in
/-- The filled-in quotient commutes with its argument. -/
theorem oneSubExpNegDivSelf_commute (a : A) : Commute a (oneSubExpNegDivSelf a) := by
  rw [oneSubExpNegDivSelf_eq_tsum]
  exact Commute.tsum_right _ fun n ↦ ((Commute.refl a).neg_right.pow_right n).smul_right _

/-- Multiplying the filled-in quotient on the right by its argument recovers its numerator. -/
theorem oneSubExpNegDivSelf_mul (a : A) :
    oneSubExpNegDivSelf a * a = 1 - exp (-a) := by
  rw [← (oneSubExpNegDivSelf_commute a).eq, mul_oneSubExpNegDivSelf]

/-- At an invertible argument, the filled-in quotient is left division by that argument. -/
theorem oneSubExpNegDivSelf_eq_invOf_mul (a : A) [Invertible a] :
    oneSubExpNegDivSelf a = ⅟ a * (1 - exp (-a)) := by
  rw [← mul_oneSubExpNegDivSelf, ← mul_assoc, invOf_mul_self, one_mul]

/-- At an invertible argument, the filled-in quotient is right division by that argument. -/
theorem oneSubExpNegDivSelf_eq_mul_invOf (a : A) [Invertible a] :
    oneSubExpNegDivSelf a = (1 - exp (-a)) * ⅟ a := by
  rw [← oneSubExpNegDivSelf_mul, mul_assoc, mul_invOf_self, mul_one]
