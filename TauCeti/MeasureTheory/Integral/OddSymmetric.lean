/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integrals of odd functions over symmetric intervals

An odd integrand into a real normed space integrates to zero over an interval `[-R, R]`
symmetric about the origin.

No integrability hypothesis is needed. The substitution `t ↦ -t` carries `[-R, R]` to itself, so
`intervalIntegral.integral_comp_neg` identifies the integral with the integral of `t ↦ g (-t)`;
oddness turns that into the negative of the original, and in a real vector space an element equal
to its own negative is zero. In particular the statement is also true (vacuously, both sides being
`0`) when `g` fails to be integrable.

## Main results

* `intervalIntegral.integral_eq_zero_of_odd` — `∫ t in -R..R, g t = 0` for odd `g`.
-/

public section

namespace intervalIntegral

/-- **An odd integrand integrates to zero over a symmetric interval.** No integrability
hypothesis is needed: the substitution `t ↦ -t` maps `[-R, R]` to itself, so the integral equals
its own negative. -/
@[simp]
theorem integral_eq_zero_of_odd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hodd : Function.Odd g) (R : ℝ) :
    ∫ t in (-R)..R, g t = 0 := by
  have hfun : (fun t => g (-t)) = fun t => -g t := funext hodd
  have hcomp : ∫ t in (-R)..R, g (-t) = ∫ t in (-R)..R, g t := by
    simp [intervalIntegral.integral_comp_neg (a := -R) (b := R) g]
  rw [hfun, intervalIntegral.integral_neg] at hcomp
  -- `hcomp` says the integral is its own negative; in a real vector space that forces `0`.
  have htwo : (2 : ℝ) • (∫ t in (-R)..R, g t) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← hcomp]
    abel
  simpa using htwo

end intervalIntegral

end
