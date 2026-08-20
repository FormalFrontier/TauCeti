/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Nonnegative trigonometric combinations

This file packages finite trigonometric combinations with nonnegative coefficients that are
nonnegative on the complex unit circle. It also transfers their pointwise nonnegativity to the
Taylor series of `-log (1 - z)`, giving a reusable local Euler-factor inequality.

## Main declarations

* `TauCeti.LSeries.trigonometricCombination` is a finite weighted cosine combination.
* `TauCeti.LSeries.IsNonnegativeTrigonometricCombination` records nonnegative coefficients and
  nonnegativity on the unit circle.
* `TauCeti.LSeries.sum_re_neg_log_one_sub_nonneg` transfers unit-circle nonnegativity to
  logarithms of Euler factors in the open unit disk.

## Provenance

The logarithmic transfer generalizes the private, Dirichlet-character-specific lemma
`DirichletCharacter.re_log_comb_nonneg'` in Mathlib's
`Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, due to Michael Stoll and David Loeffler.

This is part of Layer 8.2 of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.
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

/-- The defining finite-sum formula for `trigonometricCombination`. -/
@[simp]
theorem trigonometricCombination_def (s : Finset ι) (c : ι → ℝ) (m : ι → ℕ) (z : ℂ) :
    trigonometricCombination s c m z = ∑ i ∈ s, c i * (z ^ m i).re := (rfl)

/-- A finite trigonometric combination is nonnegative when its weights are nonnegative and its
value is nonnegative at every complex phase on the unit circle. -/
def IsNonnegativeTrigonometricCombination
    (s : Finset ι) (c : ι → ℝ) (m : ι → ℕ) : Prop :=
  (∀ i ∈ s, 0 ≤ c i) ∧ ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ trigonometricCombination s c m z

variable {s : Finset ι} {c : ι → ℝ} {m : ι → ℕ}

/-- Unit-circle nonnegativity of a trigonometric combination transfers to the Taylor series of
`-log (1 - z)`. This is the local Euler-factor form of trigonometric positivity. -/
theorem sum_re_neg_log_one_sub_nonneg
    (h : ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ trigonometricCombination s c m z)
    {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ} (hz : ‖z‖ = 1) :
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
      sub_zero, trigonometricCombination_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← pow_mul]
    ring_nf
  rw [hrewrite]
  refine mul_nonneg (div_nonneg (pow_nonneg ha₀ n) (Nat.cast_nonneg n)) ?_
  exact h (z ^ n) (by simp [norm_pow, hz])

namespace IsNonnegativeTrigonometricCombination

/-- Construct a nonnegative trigonometric combination from nonnegative weights and unit-circle
nonnegativity. -/
theorem mk (hcoeff : ∀ i ∈ s, 0 ≤ c i)
    (h_nonneg : ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ trigonometricCombination s c m z) :
    IsNonnegativeTrigonometricCombination s c m :=
  ⟨hcoeff, h_nonneg⟩

/-- Every weight in a nonnegative trigonometric combination is nonnegative. -/
theorem coeff_nonneg (h : IsNonnegativeTrigonometricCombination s c m) {i : ι} (hi : i ∈ s) :
    0 ≤ c i :=
  h.1 i hi

/-- A nonnegative trigonometric combination is nonnegative on the unit circle. -/
theorem nonneg (h : IsNonnegativeTrigonometricCombination s c m) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ trigonometricCombination s c m z :=
  h.2 z hz

/-- A nonnegative trigonometric combination remains nonnegative after it is applied to the
Taylor series of `-log (1 - z)`. -/
theorem sum_re_neg_log_one_sub_nonneg
    (h : IsNonnegativeTrigonometricCombination s c m) {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ ∑ i ∈ s, c i * (-log (1 - a * z ^ m i)).re :=
  TauCeti.LSeries.sum_re_neg_log_one_sub_nonneg h.2 ha₀ ha₁ hz

end IsNonnegativeTrigonometricCombination

end

end TauCeti.LSeries
