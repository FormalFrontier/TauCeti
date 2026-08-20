/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.NonnegCombination

/-!
# The 3-4-1 positivity combination

This file packages the elementary positivity input in the classical `3-4-1` argument for
nonvanishing of Dirichlet series. For a phase `z` on the complex unit circle,

```text
3 + 4 Re(z) + Re(z²) = 2 (1 + Re(z))² ≥ 0.
```

The weights `3`, `4`, and `1` are nonnegative. We record their expression as a finite nonnegative
trigonometric combination and prove the corresponding inequality for logarithms of Euler factors.
These results contain no continuation, nonvanishing, or character-specific hypotheses; downstream
applications provide those analytic inputs separately.

## Main declarations

* `TauCeti.LSeries.isNonnegativeTrigonometricCombination_threeFourOne` packages the frequencies
  `0`, `1`, and `2` with weights `3`, `4`, and `1`.
* `TauCeti.LSeries.threeFourOne_re_neg_log_one_sub_nonneg` is the corresponding inequality for
  logarithms of Euler factors in the open unit disk.

## Provenance

The `3-4-1` argument is classical; see Davenport, *Multiplicative Number Theory*, Chapter 4.
The logarithmic form specializes the private lemma `DirichletCharacter.re_log_comb_nonneg'` in
Mathlib's `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, by Michael Stoll and David Loeffler,
through `TauCeti.sum_re_neg_log_one_sub_nonneg`.
This is Layer 8.2 of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.
-/

public section

namespace TauCeti.LSeries

open Complex

noncomputable section

/-! ### The concrete 3-4-1 combination -/

/-- The three nonnegative weights `3`, `4`, and `1` in the `3-4-1` combination. -/
def threeFourOneWeight : Fin 3 → ℝ := ![3, 4, 1]

/-- The frequencies `0`, `1`, and `2` in the `3-4-1` combination. -/
def threeFourOneFrequency : Fin 3 → ℕ := ![0, 1, 2]

/-- The `3-4-1` trigonometric expression evaluated at a complex phase. -/
def threeFourOneCombination (z : ℂ) : ℝ := 3 + 4 * z.re + (z ^ 2).re

/-- The abstract finite combination with `3-4-1` weights is the usual concrete expression. -/
@[simp]
theorem trigonometricCombination_threeFourOne (z : ℂ) :
    trigonometricCombination Finset.univ threeFourOneWeight threeFourOneFrequency z =
      threeFourOneCombination z := by
  simp only [trigonometricCombination, threeFourOneCombination, threeFourOneWeight,
    threeFourOneFrequency, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, pow_zero, pow_one, one_re, mul_one, one_mul, add_zero]
  ring_nf

/-- On the unit circle the `3-4-1` expression is twice a square. -/
theorem threeFourOneCombination_eq_two_mul_sq {z : ℂ} (hz : ‖z‖ = 1) :
    threeFourOneCombination z = 2 * (z.re + 1) ^ 2 := by
  rw [threeFourOneCombination, pow_two, mul_re, ← sq, ← sq,
    ← Complex.sq_norm_sub_sq_re, hz]
  ring

/-- The `3-4-1` expression is nonnegative on the closed complex unit disk. -/
theorem threeFourOneCombination_nonneg {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ threeFourOneCombination z := by
  have hnorm : ‖z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg z) hz
  rw [threeFourOneCombination, pow_two, mul_re, ← sq, ← sq,
    ← Complex.sq_norm_sub_sq_re]
  nlinarith [sq_nonneg (z.re + 1)]

/-- The weights and frequencies of the `3-4-1` expression form a finite nonnegative
trigonometric combination. -/
theorem isNonnegativeTrigonometricCombination_threeFourOne :
    IsNonnegativeTrigonometricCombination Finset.univ threeFourOneWeight
      threeFourOneFrequency := by
  intro z hz
  rw [trigonometricCombination_threeFourOne]
  exact threeFourOneCombination_nonneg hz

/-! ### Euler-factor form -/

/-- The `3-4-1` inequality for logarithms of three Euler factors in the open unit disk. -/
theorem threeFourOne_re_neg_log_one_sub_nonneg {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re +
      (-log (1 - a * z ^ 2)).re := by
  have h := sum_re_neg_log_one_sub_nonneg
    isNonnegativeTrigonometricCombination_threeFourOne ha₀ ha₁ hz
  simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, threeFourOneWeight,
    threeFourOneFrequency, Matrix.cons_val_zero, Matrix.cons_val_succ, pow_zero, pow_one, mul_one,
    one_mul, add_zero, add_assoc] using h

end

end TauCeti.LSeries
