/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Complex.BigOperators
import TauCeti.Analysis.Contour.LogDerivFTC

/-!
# The index integral as a sum of segment logarithm increments

Given a monotone partition `a = s 0 ≤ ⋯ ≤ s N = b` fine enough that on each segment the normalized
ratio `(γ t - w) / (γ (s j) - w)` stays in `Complex.slitPlane`, the logarithmic-derivative integral
splits into a sum of per-segment logarithm increments:

`∫ t in a..b, γ' t / (γ t - w) = ∑ j < N, Complex.log ((γ (s (j+1)) - w) / (γ (s j) - w))`.

Specializing `γ' = deriv γ` and rewriting `γ' t / (γ t - w)` as the winding integrand
`(γ t - w)⁻¹ * deriv γ t` gives the form consumed by the winding-number computation. The per-segment
slit-plane hypothesis is exactly the data the continuous argument-lift partition supplies, so this
evaluation bridges that partition to the winding-number computation: it is the first half of showing
the winding number of a closed curve is an integer, since for a closed curve the real parts of these
increments telescope away and the imaginary parts sum to the total argument change.

## Main results

* `TauCeti.Contour.integral_deriv_div_sub_eq_sum_log` — the partition sum in general
  `γ' t / (γ t - w)` form with an explicit derivative witness.
* `TauCeti.Contour.integral_inv_sub_mul_deriv_eq_sum_log` — its `deriv γ` specialization with the
  winding integrand `(γ t - w)⁻¹ * deriv γ t`.
* `TauCeti.Contour.integral_deriv_div_sub_eq_log_norm_add_I_mul_sum_log_im` — the real/imaginary
  refinement of the partition sum: a real logarithm-of-modulus increment plus `I` times the
  imaginary segment logarithm sum.
* `TauCeti.Contour.integral_inv_sub_mul_deriv_eq_log_norm_add_I_mul_sum_log_im` — its `deriv γ`
  specialization with the winding integrand.

## Provenance

Adapted from `contourIntegral_inv_eq_sum_log_segRatio` in `WindingArgDiff.lean` of the AINTLIB
`LeanModularForms` development, restated for a raw `γ : ℝ → ℂ` on `[a, b]`.
-/

public section

open Complex MeasureTheory Set intervalIntegral

open scoped Interval

namespace TauCeti.Contour

/-- **Index integral as a sum of segment logarithm increments.** For a monotone partition
`a = s 0 ≤ ⋯ ≤ s N = b` of `[a, b]` with `γ` continuous there, differentiable with derivative `γ'`
off a countable set `P`, and with the normalized segment ratio `(γ t - w) / (γ (s j) - w)` in
`Complex.slitPlane` on each `[s j, s (j+1)]`, the integral of `γ' t / (γ t - w)` equals the sum of
the per-segment `Complex.log` increments. -/
theorem integral_deriv_div_sub_eq_sum_log {γ γ' : ℝ → ℂ} {w : ℂ} {a b : ℝ} {P : Set ℝ}
    {N : ℕ} {s : ℕ → ℝ} (hP : P.Countable)
    (hs_zero : s 0 = a) (hs_N : s N = b) (hs_mono : Monotone s)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b \ P, HasDerivAt γ (γ' t) t)
    (h_slit : ∀ j, j < N → ∀ t ∈ Icc (s j) (s (j + 1)),
      (γ t - w) / (γ (s j) - w) ∈ slitPlane)
    (h_int : IntervalIntegrable (fun t ↦ γ' t / (γ t - w)) volume a b) :
    ∫ t in a..b, γ' t / (γ t - w)
      = ∑ j ∈ Finset.range N, Complex.log ((γ (s (j + 1)) - w) / (γ (s j) - w)) := by
  have hab : a ≤ b := by have := hs_mono (Nat.zero_le N); rwa [hs_zero, hs_N] at this
  have hs_in : ∀ j ≤ N, s j ∈ Icc a b := fun j hj ↦
    ⟨by rw [← hs_zero]; exact hs_mono (Nat.zero_le j), by rw [← hs_N]; exact hs_mono hj⟩
  have hmono_seg : ∀ j, s j ≤ s (j + 1) := fun j ↦ hs_mono (Nat.le_succ j)
  have h_int_seg : ∀ k < N,
      IntervalIntegrable (fun t ↦ γ' t / (γ t - w)) volume (s k) (s (k + 1)) := by
    intro k hk
    refine h_int.mono_set ?_
    rw [uIcc_of_le (hmono_seg k), uIcc_of_le hab]
    exact Icc_subset_Icc (hs_in k hk.le).1 (hs_in (k + 1) hk).2
  rw [← hs_zero, ← hs_N, ← sum_integral_adjacent_intervals h_int_seg]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  refine integral_deriv_div_sub_eq_log hP ?_ ?_ ?_ (h_int_seg j hj)
  · rw [uIcc_of_le (hmono_seg j)]
    exact hγ_cont.mono (Icc_subset_Icc (hs_in j hj.le).1 (hs_in (j + 1) hj).2)
  · intro t ht
    rw [min_eq_left (hmono_seg j), max_eq_right (hmono_seg j)] at ht
    refine hγ_diff t ⟨⟨(hs_in j hj.le).1.trans_lt ht.1.1, ?_⟩, ht.2⟩
    exact ht.1.2.trans_le (hs_in (j + 1) hj).2
  · rw [uIcc_of_le (hmono_seg j)]
    exact h_slit j hj

/-- **Winding-integrand form.** The `γ' = deriv γ` specialization of
`integral_deriv_div_sub_eq_sum_log` with the winding integrand `(γ t - w)⁻¹ * deriv γ t`, as
consumed by the winding-number computation. -/
theorem integral_inv_sub_mul_deriv_eq_sum_log {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ} {P : Set ℝ}
    {N : ℕ} {s : ℕ → ℝ} (hP : P.Countable)
    (hs_zero : s 0 = a) (hs_N : s N = b) (hs_mono : Monotone s)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b \ P, DifferentiableAt ℝ γ t)
    (h_slit : ∀ j, j < N → ∀ t ∈ Icc (s j) (s (j + 1)),
      (γ t - w) / (γ (s j) - w) ∈ slitPlane)
    (h_int : IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b) :
    ∫ t in a..b, (γ t - w)⁻¹ * deriv γ t
      = ∑ j ∈ Finset.range N, Complex.log ((γ (s (j + 1)) - w) / (γ (s j) - w)) := by
  simp only [inv_mul_eq_div]
  exact integral_deriv_div_sub_eq_sum_log (γ' := deriv γ) hP hs_zero hs_N hs_mono hγ_cont
    (fun t ht ↦ (hγ_diff t ht).hasDerivAt) h_slit (by simpa only [inv_mul_eq_div] using h_int)

/-- **Real/imaginary decomposition of the index integral (explicit velocity).** Refining
`integral_deriv_div_sub_eq_sum_log`, over the same slit-compatible monotone partition the integral
of `γ' t / (γ t - w)` splits into a real logarithm-of-modulus increment
`Real.log ‖γ b - w‖ - Real.log ‖γ a - w‖` plus `I` times the imaginary part of the segment
logarithm sum. For a closed curve the real increment vanishes, isolating the total argument
change. -/
theorem integral_deriv_div_sub_eq_log_norm_add_I_mul_sum_log_im {γ γ' : ℝ → ℂ} {w : ℂ}
    {a b : ℝ} {P : Set ℝ} {N : ℕ} {s : ℕ → ℝ} (hP : P.Countable)
    (hs_zero : s 0 = a) (hs_N : s N = b) (hs_mono : Monotone s)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b \ P, HasDerivAt γ (γ' t) t)
    (h_slit : ∀ j, j < N → ∀ t ∈ Icc (s j) (s (j + 1)),
      (γ t - w) / (γ (s j) - w) ∈ slitPlane)
    (h_int : IntervalIntegrable (fun t ↦ γ' t / (γ t - w)) volume a b) :
    ∫ t in a..b, γ' t / (γ t - w)
      = ((Real.log ‖γ b - w‖ - Real.log ‖γ a - w‖ : ℝ) : ℂ)
        + Complex.I * ((∑ j ∈ Finset.range N,
            (Complex.log ((γ (s (j + 1)) - w) / (γ (s j) - w))).im : ℝ) : ℂ) := by
  rw [integral_deriv_div_sub_eq_sum_log hP hs_zero hs_N hs_mono hγ_cont hγ_diff h_slit h_int]
  have hmono_seg : ∀ j, s j ≤ s (j + 1) := fun j ↦ hs_mono (Nat.le_succ j)
  have hne : ∀ j, j < N → γ (s j) - w ≠ 0 ∧ γ (s (j + 1)) - w ≠ 0 := fun j hj ↦
    ⟨(div_ne_zero_iff.mp (slitPlane_ne_zero
        (h_slit j hj (s j) (left_mem_Icc.mpr (hmono_seg j))))).1,
      (div_ne_zero_iff.mp (slitPlane_ne_zero
        (h_slit j hj (s (j + 1)) (right_mem_Icc.mpr (hmono_seg j))))).1⟩
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    rw [Complex.re_sum]
    calc ∑ j ∈ Finset.range N, (Complex.log ((γ (s (j + 1)) - w) / (γ (s j) - w))).re
        = ∑ j ∈ Finset.range N, (Real.log ‖γ (s (j + 1)) - w‖ - Real.log ‖γ (s j) - w‖) := by
          refine Finset.sum_congr rfl fun j hj ↦ ?_
          rw [Finset.mem_range] at hj
          rw [Complex.log_re, norm_div,
            Real.log_div (norm_ne_zero_iff.mpr (hne j hj).2) (norm_ne_zero_iff.mpr (hne j hj).1)]
      _ = Real.log ‖γ (s N) - w‖ - Real.log ‖γ (s 0) - w‖ :=
          Finset.sum_range_sub (fun j ↦ Real.log ‖γ (s j) - w‖) N
      _ = Real.log ‖γ b - w‖ - Real.log ‖γ a - w‖ := by rw [hs_N, hs_zero]
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, zero_mul, zero_add, one_mul]
    exact Complex.im_sum _ _

/-- **Winding-integrand form of the index-integral decomposition.** The `γ' = deriv γ`
specialization of `integral_deriv_div_sub_eq_log_norm_add_I_mul_sum_log_im`, stated with the
winding integrand `(γ t - w)⁻¹ * deriv γ t`, as consumed by the closed-curve winding-number
computation. -/
theorem integral_inv_sub_mul_deriv_eq_log_norm_add_I_mul_sum_log_im {γ : ℝ → ℂ} {w : ℂ}
    {a b : ℝ} {P : Set ℝ} {N : ℕ} {s : ℕ → ℝ} (hP : P.Countable)
    (hs_zero : s 0 = a) (hs_N : s N = b) (hs_mono : Monotone s)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b \ P, DifferentiableAt ℝ γ t)
    (h_slit : ∀ j, j < N → ∀ t ∈ Icc (s j) (s (j + 1)),
      (γ t - w) / (γ (s j) - w) ∈ slitPlane)
    (h_int : IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b) :
    ∫ t in a..b, (γ t - w)⁻¹ * deriv γ t
      = ((Real.log ‖γ b - w‖ - Real.log ‖γ a - w‖ : ℝ) : ℂ)
        + Complex.I * ((∑ j ∈ Finset.range N,
            (Complex.log ((γ (s (j + 1)) - w) / (γ (s j) - w))).im : ℝ) : ℂ) := by
  simp only [inv_mul_eq_div]
  exact integral_deriv_div_sub_eq_log_norm_add_I_mul_sum_log_im (γ' := deriv γ) hP hs_zero hs_N
    hs_mono hγ_cont (fun t ht ↦ (hγ_diff t ht).hasDerivAt) h_slit
    (by simpa only [inv_mul_eq_div] using h_int)

end TauCeti.Contour
