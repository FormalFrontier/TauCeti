/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Modular
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic

/-!
# The boundary contour lies in the truncated fundamental domain

The valence-formula contour `fdBoundary H` traces the boundary of the truncated fundamental
domain, so every point of it lies in that domain's closure. This file records that containment
and the four coordinate estimates it rests on — a height bound above and below, a bound on the
real part, and the lower bound on the modulus.

These are statements about the contour's *geometry* alone. They are separated from the winding
theory that first needed them so that consumers wanting only the containment — the excised
integrability criterion, for instance — need not import winding numbers.

## Main results

* `TauCeti.ModularForm.fdBoundary_mem_coe_truncatedFundamentalDomain`: the contour lies in the
  closed truncated fundamental domain.
* `TauCeti.ModularForm.sqrt_three_div_two_lt_one`: the corner height lies below the apex.
* `TauCeti.ModularForm.sqrt_three_div_two_le_im_fdBoundary`, `…im_fdBoundary_le`,
  `…abs_re_fdBoundary_le_half`, `…one_le_norm_fdBoundary`: the four coordinate estimates.

## References

The contour geometry follows the fundamental-domain boundary development of AINTLIB's
`LeanModularForms` (`ForMathlib/FDBoundary.lean`, `FDBoundaryH.lean`, `FDBoundaryPath.lean`),
ported onto the current Mathlib pin; these declarations were first written in Tau Ceti's
`Winding/Basic.lean` and are collected here so that consumers needing only the containment do
not import winding theory.
-/

public section

open Complex Set

open scoped Real

namespace TauCeti

namespace ModularForm

variable {H t : ℝ}


/-- The corner height `√3/2` lies strictly below `1`, the height of the arc's apex. -/
lemma sqrt_three_div_two_lt_one : Real.sqrt 3 / 2 < 1 := by
  nlinarith [Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0), Real.sqrt_nonneg 3]

-- `simpNF` rejects `simp` annotations on the affine coordinate rewrites below: the
-- `@[simp]` branch selectors already rewrite `fdBoundary` applications to the segment
-- functions, so these left-hand sides are not in simp normal form.

/-- Every point of the boundary contour has imaginary part at least `√3/2`, provided the
height parameter clears the corner row. -/
lemma sqrt_three_div_two_le_im_fdBoundary (hH : Real.sqrt 3 / 2 ≤ H)
    (ht : t ∈ Icc (0 : ℝ) 5) : Real.sqrt 3 / 2 ≤ (fdBoundary H t).im := by
  obtain ⟨ht0, ht5⟩ := ht
  rcases le_or_gt t 1 with h1 | h1
  · rw [im_fdBoundary_of_le_one h1]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t)
      (by linarith : (0 : ℝ) ≤ H - Real.sqrt 3 / 2)]
  · rcases le_or_gt t 3 with h3 | h3
    · rw [eqOn_fdBoundary_arc H ⟨h1.le, h3⟩, circleMap_zero_im, one_mul]
      have harc : Real.pi / 3 ≤ (t + 1) * (Real.pi / 6) ∧
          (t + 1) * (Real.pi / 6) ≤ 2 * Real.pi / 3 := by
        constructor <;> nlinarith [Real.pi_pos, h1, h3]
      calc Real.sqrt 3 / 2 = Real.sin (Real.pi / 3) := (Real.sin_pi_div_three).symm
        _ ≤ Real.sin ((t + 1) * (Real.pi / 6)) := by
            rcases le_or_gt ((t + 1) * (Real.pi / 6)) (Real.pi / 2) with hle | hgt
            · exact Real.sin_le_sin_of_le_of_le_pi_div_two
                (by linarith [Real.pi_pos]) hle harc.1
            · nth_rewrite 2 [← Real.sin_pi_sub]
              refine Real.sin_le_sin_of_le_of_le_pi_div_two
                (by linarith [Real.pi_pos]) ?_ ?_ <;> linarith [Real.pi_pos, harc.2, hgt]
    · rcases le_or_gt t 4 with h4 | h4
      · rw [im_fdBoundary_of_le_four h3 h4]
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ t - 3)
          (by linarith : (0 : ℝ) ≤ H - Real.sqrt 3 / 2)]
      · rw [im_fdBoundary_of_gt_four h4]
        exact hH

/-- The contour's real part stays within the fundamental strip. -/
lemma abs_re_fdBoundary_le_half (ht : t ≤ 5) : |(fdBoundary H t).re| ≤ 1 / 2 := by
  rw [abs_le]
  rcases le_or_gt t 1 with h1 | h1
  · rw [re_fdBoundary_of_le_one h1]
    norm_num
  · rcases le_or_gt t 3 with h3 | h3
    · rw [eqOn_fdBoundary_arc H ⟨h1.le, h3⟩, circleMap_zero_re, one_mul]
      have harc : Real.pi / 3 ≤ (t + 1) * (Real.pi / 6) ∧
          (t + 1) * (Real.pi / 6) ≤ 2 * Real.pi / 3 := by
        constructor <;> nlinarith [Real.pi_pos]
      constructor
      · have h23 : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
        calc (-(1 / 2) : ℝ) = Real.cos (2 * Real.pi / 3) := by
              rw [h23, Real.cos_pi_sub, Real.cos_pi_div_three]
          _ ≤ Real.cos ((t + 1) * (Real.pi / 6)) :=
              Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
                (by linarith [Real.pi_pos]) harc.2
      · calc Real.cos ((t + 1) * (Real.pi / 6)) ≤ Real.cos (Real.pi / 3) :=
              Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
                (by linarith [Real.pi_pos]) harc.1
          _ = 1 / 2 := Real.cos_pi_div_three
    · rcases le_or_gt t 4 with h4 | h4
      · rw [re_fdBoundary_of_le_four h3 h4]
        norm_num
      · rw [re_fdBoundary_of_gt_four h4]
        constructor <;> nlinarith

/-- The contour stays at or below its height parameter. -/
lemma im_fdBoundary_le (hH : 1 ≤ H) (ht : t ∈ Icc (0 : ℝ) 5) :
    (fdBoundary H t).im ≤ H := by
  obtain ⟨ht0, ht5⟩ := ht
  have h32 : Real.sqrt 3 / 2 ≤ 1 := sqrt_three_div_two_lt_one.le
  rcases le_or_gt t 1 with h1 | h1
  · rw [im_fdBoundary_of_le_one h1]
    nlinarith [mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ H - Real.sqrt 3 / 2)]
  · rcases le_or_gt t 3 with h3 | h3
    · rw [eqOn_fdBoundary_arc H ⟨h1.le, h3⟩, circleMap_zero_im, one_mul]
      exact (Real.sin_le_one _).trans hH
    · rcases le_or_gt t 4 with h4 | h4
      · rw [im_fdBoundary_of_le_four h3 h4]
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 4 - t)
          (by linarith : (0 : ℝ) ≤ H - Real.sqrt 3 / 2)]
      · rw [im_fdBoundary_of_gt_four h4]

/-- The boundary contour stays outside the open unit disc: the verticals and the ceiling
clear it by height and offset, and the arc lies on the unit circle. -/
lemma one_le_norm_fdBoundary (hH : 1 ≤ H) (ht : t ∈ Icc (0 : ℝ) 5) :
    1 ≤ ‖fdBoundary H t‖ := by
  obtain ⟨ht0, ht5⟩ := ht
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h32 : Real.sqrt 3 / 2 ≤ 1 := sqrt_three_div_two_lt_one.le
  have him := sqrt_three_div_two_le_im_fdBoundary (h32.trans hH) ⟨ht0, ht5⟩
  have hnn := norm_nonneg (fdBoundary H t)
  rcases le_or_gt t 1 with h1 | h1
  · have h1' : 1 ≤ ‖fdBoundary H t‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, re_fdBoundary_of_le_one h1]
      nlinarith [Real.sqrt_nonneg 3]
    nlinarith
  · rcases le_or_gt t 3 with h3 | h3
    · exact (norm_fdBoundary_arc h1.le h3).ge
    · rcases le_or_gt t 4 with h4 | h4
      · have h1' : 1 ≤ ‖fdBoundary H t‖ ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply, re_fdBoundary_of_le_four h3 h4]
          nlinarith [Real.sqrt_nonneg 3]
        nlinarith
      · calc (1 : ℝ) ≤ H := hH
          _ = (fdBoundary H t).im := (im_fdBoundary_of_gt_four h4).symm
          _ ≤ |(fdBoundary H t).im| := le_abs_self _
          _ ≤ ‖fdBoundary H t‖ := Complex.abs_im_le_norm _
/-- The boundary contour lies in the closed truncated fundamental domain. -/
lemma fdBoundary_mem_coe_truncatedFundamentalDomain (hH : 1 ≤ H) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 5) :
    fdBoundary H t ∈ UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H := by
  have h32 : Real.sqrt 3 / 2 ≤ 1 := sqrt_three_div_two_lt_one.le
  rw [ModularGroup.coe_truncatedFundamentalDomain, Set.mem_ofPred_eq]
  refine ⟨?_, im_fdBoundary_le hH ht, abs_re_fdBoundary_le_half ht.2,
    one_le_norm_fdBoundary hH ht⟩
  have := sqrt_three_div_two_le_im_fdBoundary (h32.trans hH) ht
  nlinarith [Real.sqrt_nonneg 3]

end ModularForm

end TauCeti
