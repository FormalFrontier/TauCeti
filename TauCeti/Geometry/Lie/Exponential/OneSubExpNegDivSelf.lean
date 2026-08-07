/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# The quotient `(1 - exp (-a)) / a`

This file packages the power series representing `(1 - exp (-a)) / a` without requiring `a` to be
invertible. In a complete normed algebra over an `RCLike` field the series is summable at every
point. It is the analytic factor in the differential of a Lie-group exponential map.

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

variable {𝕂 A : Type*} [RCLike 𝕂] [NormedRing A] [NormedAlgebra 𝕂 A] [CompleteSpace A]

/-- The value of `(1 - exp (-a)) / a` with its removable singularity filled in, defined by a power
series. The series is summable everywhere when `A` is complete. -/
noncomputable def oneSubExpNegDivSelf (𝕂 : Type*) [RCLike 𝕂] {A : Type*} [NormedRing A]
    [NormedAlgebra 𝕂 A] (a : A) : A :=
  ∑' n : ℕ, ((n + 1).factorial⁻¹ : 𝕂) • (-a) ^ n

omit [CompleteSpace A] in
/-- The defining series for `oneSubExpNegDivSelf`. -/
theorem oneSubExpNegDivSelf_eq_tsum (a : A) :
    oneSubExpNegDivSelf 𝕂 a = ∑' n : ℕ, (((n + 1).factorial)⁻¹ : 𝕂) • (-a) ^ n := by
  rfl

/-- The series defining `oneSubExpNegDivSelf` is summable in a complete normed algebra. -/
theorem summable_oneSubExpNegDivSelf (a : A) :
    Summable fun n : ℕ ↦ ((n + 1).factorial⁻¹ : 𝕂) • (-a) ^ n := by
  refine .of_norm_bounded_eventually (Real.summable_pow_div_factorial ‖-a‖) ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
  rw [norm_smul, mul_comm, norm_inv, RCLike.norm_natCast, ← div_eq_mul_inv]
  gcongr
  · exact norm_pow_le' _ (pos_iff_ne_zero.mpr hn)
  · exact n.le_succ

omit [CompleteSpace A] in
/-- The quotient with its removable singularity filled in takes the value `1` at zero. -/
@[simp]
theorem oneSubExpNegDivSelf_zero : oneSubExpNegDivSelf 𝕂 (0 : A) = 1 := by
  rw [oneSubExpNegDivSelf_eq_tsum, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

/-- Multiplying the filled-in quotient on the left by its argument recovers its numerator. -/
@[simp]
theorem mul_oneSubExpNegDivSelf (a : A) :
    a * oneSubExpNegDivSelf 𝕂 a = 1 - exp (-a) := by
  have hmul :
      (∑' n : ℕ, ((n + 1).factorial⁻¹ : 𝕂) • (-a) ^ (n + 1)) =
        (-a) * oneSubExpNegDivSelf 𝕂 a := by
    simpa only [oneSubExpNegDivSelf_eq_tsum, mul_smul_comm, pow_succ'] using
      (summable_oneSubExpNegDivSelf (𝕂 := 𝕂) a).tsum_mul_left (-a)
  simp only [exp_eq_tsum 𝕂]
  rw [(expSeries_summable' (𝕂 := 𝕂) (-a)).tsum_eq_zero_add]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_zero]
  rw [hmul]
  noncomm_ring

omit [CompleteSpace A] in
/-- The filled-in quotient commutes with its argument. -/
theorem oneSubExpNegDivSelf_commute (a : A) : Commute a (oneSubExpNegDivSelf 𝕂 a) := by
  rw [oneSubExpNegDivSelf_eq_tsum]
  exact Commute.tsum_right _ fun n ↦ ((Commute.refl a).neg_right.pow_right n).smul_right _

/-- Multiplying the filled-in quotient on the right by its argument recovers its numerator. -/
@[simp]
theorem oneSubExpNegDivSelf_mul (a : A) :
    oneSubExpNegDivSelf 𝕂 a * a = 1 - exp (-a) := by
  rw [← (oneSubExpNegDivSelf_commute a).eq, mul_oneSubExpNegDivSelf]

/-- At an invertible argument, the filled-in quotient is left division by that argument. -/
theorem oneSubExpNegDivSelf_eq_invOf_mul (a : A) [Invertible a] :
    oneSubExpNegDivSelf 𝕂 a = ⅟ a * (1 - exp (-a)) := by
  rw [← mul_oneSubExpNegDivSelf (𝕂 := 𝕂), ← mul_assoc, invOf_mul_self, one_mul]

/-- At an invertible argument, the filled-in quotient is right division by that argument. -/
theorem oneSubExpNegDivSelf_eq_mul_invOf (a : A) [Invertible a] :
    oneSubExpNegDivSelf 𝕂 a = (1 - exp (-a)) * ⅟ a := by
  rw [← oneSubExpNegDivSelf_mul (𝕂 := 𝕂), mul_assoc, mul_invOf_self, mul_one]
