/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
public import TauCeti.NumberTheory.LSeries.TrigonometricCombination

/-!
# The 3-4-1 positivity combination

This file packages the elementary positivity input in the classical `3-4-1` argument for
nonvanishing of Dirichlet series. For a phase `z` on the complex unit circle,

```text
3 + 4 Re(z) + Re(z²) = 2 (1 + Re(z))² ≥ 0.
```

The coefficients `3`, `4`, and `1` are nonnegative. We record this as a finite nonnegative
trigonometric combination, use it to construct nonnegative coefficient sequences, and prove the
corresponding inequality for logarithms of Euler factors. These results contain no continuation,
nonvanishing, or character-specific hypotheses; downstream applications provide those analytic
inputs separately.

## Main declarations

* `TauCeti.LSeries.isNonnegativeTrigonometricCombination_threeFourOne` packages the frequencies
  `0`, `1`, and `2` with coefficients `3`, `4`, and `1`.
* `TauCeti.LSeries.threeFourOneCoefficients` is the resulting nonnegative coefficient sequence
  obtained from a nonnegative base sequence and unit-modulus phases.
* `TauCeti.LSeries.sum_re_neg_log_one_sub_threeFourOne_nonneg` is the corresponding inequality for
  logarithms of Euler factors in the open unit disk.

## Provenance

The `3-4-1` argument is classical; see Davenport, *Multiplicative Number Theory*, Chapter 4.
This is Layer 8.2 of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.
-/

public section

namespace TauCeti.LSeries

open Complex

noncomputable section

/-! ### The concrete 3-4-1 combination -/

/-- The three nonnegative weights `3`, `4`, and `1` in the `3-4-1` combination. -/
def threeFourOneWeight : Fin 3 → ℝ := ![3, 4, 1]

/-- The zeroth weight in the `3-4-1` combination. -/
@[simp] theorem threeFourOneWeight_zero : threeFourOneWeight 0 = 3 := (rfl)

/-- The first weight in the `3-4-1` combination. -/
@[simp] theorem threeFourOneWeight_one : threeFourOneWeight 1 = 4 := (rfl)

/-- The second weight in the `3-4-1` combination. -/
@[simp] theorem threeFourOneWeight_two : threeFourOneWeight 2 = 1 := (rfl)

/-- The frequencies `0`, `1`, and `2` in the `3-4-1` combination. -/
def threeFourOneFrequency : Fin 3 → ℕ := ![0, 1, 2]

/-- The zeroth frequency in the `3-4-1` combination. -/
@[simp] theorem threeFourOneFrequency_zero : threeFourOneFrequency 0 = 0 := (rfl)

/-- The first frequency in the `3-4-1` combination. -/
@[simp] theorem threeFourOneFrequency_one : threeFourOneFrequency 1 = 1 := (rfl)

/-- The second frequency in the `3-4-1` combination. -/
@[simp] theorem threeFourOneFrequency_two : threeFourOneFrequency 2 = 2 := (rfl)

/-- The `3-4-1` trigonometric expression evaluated at a complex phase. -/
def threeFourOneCombination (z : ℂ) : ℝ := 3 + 4 * z.re + (z ^ 2).re

/-- The defining formula for `threeFourOneCombination`. -/
@[simp]
theorem threeFourOneCombination_def (z : ℂ) :
    threeFourOneCombination z = 3 + 4 * z.re + (z ^ 2).re := (rfl)

/-- The abstract finite combination with `3-4-1` weights is the usual concrete expression. -/
theorem trigonometricCombination_threeFourOne (z : ℂ) :
    trigonometricCombination Finset.univ threeFourOneWeight threeFourOneFrequency z =
      threeFourOneCombination z := by
  simp [trigonometricCombination_def, Fin.sum_univ_succ]
  ring

/-- On the unit circle the `3-4-1` expression is twice a square. -/
theorem threeFourOneCombination_eq_two_mul_sq {z : ℂ} (hz : ‖z‖ = 1) :
    threeFourOneCombination z = 2 * (z.re + 1) ^ 2 := by
  rw [threeFourOneCombination_def, pow_two, mul_re, ← sq, ← sq,
    ← Complex.sq_norm_sub_sq_re, hz]
  ring

/-- The `3-4-1` expression is nonnegative on the complex unit circle. -/
theorem threeFourOneCombination_nonneg {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ threeFourOneCombination z := by
  rw [threeFourOneCombination_eq_two_mul_sq hz]
  positivity

/-- The weights and frequencies of the `3-4-1` expression form a finite nonnegative
trigonometric combination. -/
theorem isNonnegativeTrigonometricCombination_threeFourOne :
    IsNonnegativeTrigonometricCombination Finset.univ threeFourOneWeight
      threeFourOneFrequency := by
  apply IsNonnegativeTrigonometricCombination.mk
  · intro i hi
    fin_cases i <;> norm_num [threeFourOneWeight]
  · intro z hz
    rw [trigonometricCombination_threeFourOne]
    exact threeFourOneCombination_nonneg hz

/-! ### Coefficient and Euler-factor forms -/

/-- Multiply a real coefficient sequence by the `3-4-1` phase combination pointwise. This is the
coefficient sequence to which a positivity theorem such as Landau's theorem is applied. -/
def threeFourOneCoefficients (a : ℕ → ℝ) (z : ℕ → ℂ) (n : ℕ) : ℝ :=
  a n * threeFourOneCombination (z n)

/-- The defining pointwise formula for `threeFourOneCoefficients`. -/
@[simp]
theorem threeFourOneCoefficients_def (a : ℕ → ℝ) (z : ℕ → ℂ) (n : ℕ) :
    threeFourOneCoefficients a z n = a n * threeFourOneCombination (z n) := (rfl)

/-- The exact square formula for the coefficient produced by the `3-4-1` combination. -/
theorem threeFourOneCoefficients_eq_two_mul_sq (a : ℕ → ℝ) (z : ℕ → ℂ)
    (n : ℕ) (hz : ‖z n‖ = 1) :
    threeFourOneCoefficients a z n = 2 * a n * ((z n).re + 1) ^ 2 := by
  rw [threeFourOneCoefficients_def, threeFourOneCombination_eq_two_mul_sq hz]
  ring

/-- Nonnegative base coefficients remain nonnegative after the `3-4-1` phase combination. -/
theorem threeFourOneCoefficients_nonneg {a : ℕ → ℝ} {z : ℕ → ℂ}
    {n : ℕ} (ha : 0 ≤ a n) (hz : ‖z n‖ = 1) :
    0 ≤ threeFourOneCoefficients a z n := by
  rw [threeFourOneCoefficients_eq_two_mul_sq a z n hz]
  exact mul_nonneg (mul_nonneg (by norm_num) ha) (sq_nonneg _)

/-- The `3-4-1` inequality for logarithms of three Euler factors in the open unit disk. -/
theorem sum_re_neg_log_one_sub_threeFourOne_nonneg {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re +
      (-log (1 - a * z ^ 2)).re := by
  have h :=
    isNonnegativeTrigonometricCombination_threeFourOne.sum_re_neg_log_one_sub_nonneg ha₀ ha₁ hz
  simp [Fin.sum_univ_succ] at h
  simp only [neg_re]
  linarith

end

end TauCeti.LSeries
