/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Negative real powers are completely monotone

This file proves the open-half-line negative-power example requested by the
`OneParameterSemigroups` roadmap.

For a real exponent `s ≥ 0` the `n`-th derivative of `y ↦ y^{-s}` is
`(descPochhammer ℝ n)(-s) · y^{-s-n}`, and the falling factorial `(-s)(-s-1)⋯(-s-n+1)`
carries the sign `(-1)ⁿ`, so `(-1)ⁿ` times the derivative is `s(s+1)⋯(s+n-1) · y^{-s-n} ≥ 0`.
Thus on the open half-line, `t ↦ t^{-s}` is completely monotone for every `s ≥ 0`. The case
`s = 1` is `t ↦ 1/t`, whose (infinite) representing measure is Lebesgue measure, the
Hausdorff–Bernstein–Widder example the roadmap flags for the open half-line.

The iterated derivative of `y ↦ y^s` is Mathlib's `Real.iter_deriv_rpow_const`, and the sign of
the falling factorial at a negative argument is packaged in the private lemma
`neg_one_pow_mul_descPochhammer_neg_nonneg`.

## Main declarations

* `TauCeti.isCompletelyMonotoneOnIoi_rpow_neg`: for `s ≥ 0`, `t ↦ t^{-s}` is completely monotone
  on the open half-line `(0, ∞)`.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012).
-/

public section

open Set
open scoped ContDiff

namespace TauCeti

/-- The falling factorial `(-s)(-s-1)⋯(-s-n+1) = (descPochhammer ℝ n)(-s)` carries the sign
`(-1)ⁿ` when `s ≥ 0`: multiplying it by `(-1)ⁿ` yields the nonnegative rising factorial
`s(s+1)⋯(s+n-1)`. This is the sign bookkeeping behind complete monotonicity of `t ↦ t^{-s}`. -/
private lemma neg_one_pow_mul_descPochhammer_neg_nonneg {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    0 ≤ (-1 : ℝ) ^ n * (descPochhammer ℝ n).eval (-s) := by
  rw [← ascPochhammer_eval_neg_eq_descPochhammer ℝ (-s) n, neg_neg]
  obtain rfl | hs := hs.eq_or_lt
  · by_cases hn : n = 0 <;> simp [hn]
  · exact (ascPochhammer_pos n s hs).le

/-- For `s ≥ 0`, the negative power `t ↦ t^{-s}` is completely monotone on the open half-line
`(0, ∞)`. The case `s = 1` is `t ↦ 1/t`, whose representing measure is (infinite) Lebesgue
measure; the demand for smoothness only on `(0, ∞)` is essential, as `t^{-s}` blows up at the
boundary for `s > 0`. -/
theorem isCompletelyMonotoneOnIoi_rpow_neg {s : ℝ} (hs : 0 ≤ s) :
    IsCompletelyMonotoneOnIoi (fun t => t ^ (-s)) := by
  refine ⟨fun t ht => (Real.contDiffAt_rpow_const_of_ne (mem_Ioi.mp ht).ne').contDiffWithinAt,
    fun n t ht => ?_⟩
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const, ← mul_assoc]
  exact mul_nonneg (neg_one_pow_mul_descPochhammer_neg_nonneg hs n)
    (Real.rpow_pos_of_pos ht _).le

end TauCeti
