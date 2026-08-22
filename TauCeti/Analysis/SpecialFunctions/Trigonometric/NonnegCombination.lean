/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Complex.AbsMax

/-!
# Nonnegative trigonometric combinations

This file packages finite trigonometric combinations that are nonnegative on the complex unit
circle. It also transfers their pointwise nonnegativity to the closed unit disk and the Taylor
series of `-log (1 - z)`, giving a reusable logarithmic inequality.

## Main declarations

* `TauCeti.trigonometricCombination` is a finite weighted cosine combination.
* `TauCeti.IsNonnegativeTrigonometricCombination` asserts nonnegativity on the unit circle.
* `TauCeti.trigonometricCombination_nonneg_of_boundary` extends this nonnegativity to the closed
  unit disk.
* `TauCeti.sum_re_neg_log_one_sub_nonneg` transfers boundary nonnegativity to logarithms in the
  open unit disk.

## Provenance

The logarithmic transfer generalizes the private lemma `re_log_comb_nonneg'` in the
`DirichletCharacter` namespace of Mathlib's
`Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, due to Michael Stoll and David Loeffler, from
the fixed `3-4-1` weights to an arbitrary finite nonnegative combination.

This is part of Layer 8.2 of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.
-/

public section

namespace TauCeti

open Complex

noncomputable section

variable {ι : Type*}

/-- The real trigonometric combination with weights `c` and frequencies `m`, evaluated at a
complex phase `z`. On the unit circle, `(z ^ k).re` is a cosine. -/
def trigonometricCombination
    (s : Finset ι) (c : ι → ℝ) (m : ι → ℕ) (z : ℂ) : ℝ :=
  ∑ i ∈ s, c i * (z ^ m i).re

/-- The defining finite-sum formula for `trigonometricCombination`. -/
theorem trigonometricCombination_def (s : Finset ι) (c : ι → ℝ) (m : ι → ℕ) (z : ℂ) :
    trigonometricCombination s c m z = ∑ i ∈ s, c i * (z ^ m i).re := (rfl)

/-- The assertion that a finite trigonometric combination is nonnegative at every complex phase
on the unit circle. -/
abbrev IsNonnegativeTrigonometricCombination
    (s : Finset ι) (c : ι → ℝ) (m : ι → ℕ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ trigonometricCombination s c m z

variable {s : Finset ι} {c : ι → ℝ} {m : ι → ℕ}

/-- Nonnegativity of a trigonometric combination on the unit circle extends to the closed unit
disk. -/
theorem trigonometricCombination_nonneg_of_boundary
    (h : IsNonnegativeTrigonometricCombination s c m) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ trigonometricCombination s c m z := by
  let f : ℂ → ℂ := fun w ↦ exp (-∑ i ∈ s, (c i : ℂ) * w ^ m i)
  have hf : Differentiable ℂ f := by
    dsimp [f]
    fun_prop
  have hnorm : ‖f z‖ ≤ 1 := Complex.norm_le_of_forall_mem_frontier_norm_le
      Metric.isBounded_ball hf.diffContOnCl (fun w hw ↦ by
        rw [frontier_ball (0 : ℂ) one_ne_zero, mem_sphere_zero_iff_norm] at hw
        simpa only [f, Complex.norm_exp, neg_re, Complex.re_sum, mul_re, ofReal_re, ofReal_im,
          zero_mul, sub_zero, Real.exp_le_one_iff, neg_nonpos,
          trigonometricCombination_def] using h w hw)
      (by rw [closure_ball (0 : ℂ) one_ne_zero, Metric.mem_closedBall,
        dist_zero_right]; exact hz)
  simpa only [f, Complex.norm_exp, neg_re, Complex.re_sum, mul_re, ofReal_re, ofReal_im,
    zero_mul, sub_zero, Real.exp_le_one_iff, neg_nonpos, trigonometricCombination_def] using hnorm

/-- Unit-circle nonnegativity of a trigonometric combination transfers to the Taylor series of
`-log (1 - z)` throughout the closed unit disk. -/
theorem sum_re_neg_log_one_sub_nonneg
    (h : IsNonnegativeTrigonometricCombination s c m)
    {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ ∑ i ∈ s, c i * (-log (1 - a * z ^ m i)).re := by
  have ha : ‖(a : ℂ)‖ < 1 := by
    simpa only [norm_real, Real.norm_of_nonneg ha₀] using ha₁
  have haz (i : ι) : ‖(a : ℂ) * z ^ m i‖ < 1 := by
    rw [norm_mul, norm_pow]
    calc
      ‖(a : ℂ)‖ * ‖z‖ ^ m i ≤ ‖(a : ℂ)‖ * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg z) hz) (norm_nonneg _)
      _ < 1 := by simpa only [mul_one] using ha
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
    intro i _
    rw [← pow_mul, mul_comm (m i) n]
    ring_nf
  rw [hrewrite]
  refine mul_nonneg (div_nonneg (pow_nonneg ha₀ n) (Nat.cast_nonneg n)) ?_
  exact trigonometricCombination_nonneg_of_boundary h
    (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg z) hz)

end

end TauCeti
