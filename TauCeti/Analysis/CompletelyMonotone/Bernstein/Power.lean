/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Composition
public import TauCeti.Analysis.CompletelyMonotone.Power
-- Proof-only: the derivative and the continuity of a real power with a constant exponent.
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Fractional powers are Bernstein functions

The power `t ↦ t^s` with `0 ≤ s ≤ 1` is a Bernstein function: it is nonnegative and continuous
on `[0, ∞)`, smooth on `(0, ∞)`, and its derivative `t ↦ s · t^{s-1}` is the completely monotone
negative power of `TauCeti.isCompletelyMonotoneOnIoi_rpow_neg`, since `s - 1 = -(1 - s)` with
`1 - s ≥ 0`.

Feeding this into `TauCeti.IsContinuousCompletelyMonotoneOnIoi.comp_isBernsteinFunction` produces
the stretched exponentials `t ↦ e^{-x t^s}`. These are the acceptance example the
`OneParameterSemigroups` roadmap asks the composition closure to deliver. The endpoint `s = 1`
recovers the exponential `t ↦ e^{-x t}` and `s = 0` the constant `t ↦ e^{-x}`.

## Main declarations

* `TauCeti.isBernsteinFunction_rpow`: `t ↦ t^s` is a Bernstein function for `0 ≤ s ≤ 1`.
* `TauCeti.isContinuousCompletelyMonotoneOnIoi_exp_neg_mul_rpow`: the stretched exponential
  `t ↦ e^{-x t^s}` is completely monotone.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Example 1.5 and Chapter 5.
-/

public section

open Set
open scoped ContDiff

namespace TauCeti

/-- For `0 ≤ s ≤ 1` the power `t ↦ t^s` is a Bernstein function: its derivative is the
completely monotone negative power `t ↦ s · t^{-(1-s)}`. -/
theorem isBernsteinFunction_rpow {s : ℝ} (hs : 0 ≤ s) (hs₁ : s ≤ 1) :
    IsBernsteinFunction fun t : ℝ => t ^ s := by
  have hderiv : EqOn (deriv fun t : ℝ => t ^ s) (s • fun t : ℝ => t ^ (-(1 - s))) (Ioi 0) := by
    intro t ht
    rw [(Real.hasDerivAt_rpow_const (Or.inl (mem_Ioi.mp ht).ne')).deriv]
    simp [Pi.smul_apply, smul_eq_mul, neg_sub]
  exact isBernsteinFunction_iff.mpr
    ⟨(Real.continuous_rpow_const hs).continuousOn,
      fun t ht => (Real.contDiffAt_rpow_const_of_ne (mem_Ioi.mp ht).ne').contDiffWithinAt,
      fun t ht => Real.rpow_nonneg ht s,
      ((isCompletelyMonotoneOnIoi_rpow_neg (by linarith : (0 : ℝ) ≤ 1 - s)).smul hs).congr hderiv⟩

/-- The **stretched exponential** `t ↦ e^{-x t^s}` is completely monotone on `[0, ∞)` for
`x ≥ 0` and `0 ≤ s ≤ 1`: it is the composition of the completely monotone `t ↦ e^{-x t}` with the
Bernstein function `t ↦ t^s`. -/
theorem isContinuousCompletelyMonotoneOnIoi_exp_neg_mul_rpow {x s : ℝ} (hx : 0 ≤ x) (hs : 0 ≤ s)
    (hs₁ : s ≤ 1) :
    IsContinuousCompletelyMonotoneOnIoi fun t : ℝ => Real.exp (-x * t ^ s) :=
  (isBernsteinFunction_rpow hs hs₁).isContinuousCompletelyMonotoneOnIoi_exp_neg_mul hx

end TauCeti
