/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Data.Fin.VecNotation

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

* `TauCeti.LSeries.IsNonnegativeTrigonometricCombination` says that a finite cosine combination
  has nonnegative coefficients and is nonnegative on the unit circle.
* `TauCeti.LSeries.isNonnegativeTrigonometricCombination_threeFourOne` packages the frequencies
  `0`, `1`, and `2` with coefficients `3`, `4`, and `1`.
* `TauCeti.LSeries.threeFourOneCoefficients` is the resulting nonnegative coefficient sequence
  obtained from a nonnegative base sequence and unit-modulus phases.
* `TauCeti.LSeries.IsNonnegativeTrigonometricCombination.sum_re_neg_log_one_sub_nonneg` transfers
  any such finite combination to logarithms of Euler factors in the open unit disk.

## Provenance

The `3-4-1` argument is classical; see Davenport, *Multiplicative Number Theory*, Chapter 4.
The proof of the logarithmic transfer generalizes the private, Dirichlet-character-specific lemma
`DirichletCharacter.re_log_comb_nonneg'` in Mathlib's
`Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, due to Michael Stoll and David Loeffler.

This is Layer 8.2 of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.
-/

public section

namespace TauCeti.LSeries

open Complex

noncomputable section

variable {ι : Type*}

/-- The real trigonometric combination with weights `c` and frequencies `m`, evaluated at a
complex phase `z`. The intended inputs have `‖z‖ = 1`, when `(z ^ k).re` is a cosine. -/
def trigonometricCombination (s : Finset ι) (c : ι → ℝ) (m : ι → ℕ) (z : ℂ) : ℝ :=
  ∑ i ∈ s, c i * (z ^ m i).re

/-- A finite trigonometric combination is nonnegative when its weights are nonnegative and its
value is nonnegative at every complex phase on the unit circle. -/
def IsNonnegativeTrigonometricCombination
    (s : Finset ι) (c : ι → ℝ) (m : ι → ℕ) : Prop :=
  (∀ i ∈ s, 0 ≤ c i) ∧ ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ trigonometricCombination s c m z

namespace IsNonnegativeTrigonometricCombination

variable {s : Finset ι} {c : ι → ℝ} {m : ι → ℕ}

/-- Every weight in a nonnegative trigonometric combination is nonnegative. -/
theorem coeff_nonneg (h : IsNonnegativeTrigonometricCombination s c m) {i : ι} (hi : i ∈ s) :
    0 ≤ c i :=
  h.1 i hi

/-- A nonnegative trigonometric combination is nonnegative on the unit circle. -/
theorem nonneg (h : IsNonnegativeTrigonometricCombination s c m) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ trigonometricCombination s c m z :=
  h.2 z hz

/-- A nonnegative trigonometric combination remains nonnegative after it is applied to the
Taylor series of `-log (1 - z)`. This is the local Euler-factor form of the positivity package. -/
theorem sum_re_neg_log_one_sub_nonneg
    (h : IsNonnegativeTrigonometricCombination s c m) {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ ∑ i ∈ s, c i * (-log (1 - a * z ^ m i)).re := by
  have ha : ‖(a : ℂ)‖ < 1 := by
    simpa only [norm_real, Real.norm_of_nonneg ha₀] using ha₁
  have haz (i : ι) : ‖(a : ℂ) * z ^ m i‖ < 1 := by
    rw [norm_mul, norm_pow, hz, one_pow, mul_one]
    exact ha
  have hsum : HasSum
      (fun n : ℕ ↦ ∑ i ∈ s, c i * ((((a : ℂ) * z ^ m i) ^ n / n).re))
      (∑ i ∈ s, c i * (-log (1 - a * z ^ m i)).re) := by
    exact hasSum_sum fun i _ ↦
      (Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log (haz i))).mul_left (c i)
  rw [← hsum.tsum_eq]
  refine tsum_nonneg fun n ↦ ?_
  have hrewrite :
      (∑ i ∈ s, c i * ((((a : ℂ) * z ^ m i) ^ n / n).re)) =
        (a ^ n / (n : ℝ)) * trigonometricCombination s c m (z ^ n) := by
    simp only [mul_pow, ← ofReal_pow, div_natCast_re, ofReal_re, mul_re, ofReal_im, zero_mul,
      sub_zero, trigonometricCombination, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← pow_mul]
    ring_nf
  rw [hrewrite]
  refine mul_nonneg (div_nonneg (pow_nonneg ha₀ n) (Nat.cast_nonneg n)) ?_
  exact h.nonneg (by simp [norm_pow, hz])

end IsNonnegativeTrigonometricCombination

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
  simp [trigonometricCombination, threeFourOneWeight, threeFourOneFrequency,
    threeFourOneCombination, Fin.sum_univ_succ]
  ring

/-- On the unit circle the `3-4-1` expression is twice a square. -/
theorem threeFourOneCombination_eq_two_mul_sq {z : ℂ} (hz : ‖z‖ = 1) :
    threeFourOneCombination z = 2 * (z.re + 1) ^ 2 := by
  rw [threeFourOneCombination, pow_two, mul_re, ← sq, ← sq,
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
  constructor
  · intro i hi
    fin_cases i <;> norm_num [threeFourOneWeight]
  · intro z hz
    simpa using threeFourOneCombination_nonneg hz

/-! ### Coefficient and Euler-factor forms -/

/-- Multiply a real coefficient sequence by the `3-4-1` phase combination pointwise. This is the
coefficient sequence to which a positivity theorem such as Landau's theorem is applied. -/
def threeFourOneCoefficients (a : ℕ → ℝ) (z : ℕ → ℂ) (n : ℕ) : ℝ :=
  a n * threeFourOneCombination (z n)

/-- The exact square formula for the coefficient produced by the `3-4-1` combination. -/
theorem threeFourOneCoefficients_eq_two_mul_sq (a : ℕ → ℝ) (z : ℕ → ℂ)
    (hz : ∀ n, ‖z n‖ = 1) (n : ℕ) :
    threeFourOneCoefficients a z n = 2 * a n * ((z n).re + 1) ^ 2 := by
  rw [threeFourOneCoefficients, threeFourOneCombination_eq_two_mul_sq (hz n)]
  ring

/-- Nonnegative base coefficients remain nonnegative after the `3-4-1` phase combination. -/
theorem threeFourOneCoefficients_nonneg {a : ℕ → ℝ} {z : ℕ → ℂ}
    (ha : ∀ n, 0 ≤ a n) (hz : ∀ n, ‖z n‖ = 1) (n : ℕ) :
    0 ≤ threeFourOneCoefficients a z n := by
  rw [threeFourOneCoefficients_eq_two_mul_sq a z hz n]
  exact mul_nonneg (mul_nonneg (by norm_num) (ha n)) (sq_nonneg _)

/-- The `3-4-1` inequality for logarithms of three Euler factors in the open unit disk. -/
theorem sum_re_neg_log_one_sub_threeFourOne_nonneg {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re +
      (-log (1 - a * z ^ 2)).re := by
  have h :=
    isNonnegativeTrigonometricCombination_threeFourOne.sum_re_neg_log_one_sub_nonneg ha₀ ha₁ hz
  simp [threeFourOneWeight, threeFourOneFrequency, Fin.sum_univ_succ] at h
  simp only [neg_re]
  linarith

end

end TauCeti.LSeries
