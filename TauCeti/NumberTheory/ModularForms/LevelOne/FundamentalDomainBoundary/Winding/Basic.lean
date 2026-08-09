/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.Modular
public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic

import Mathlib.Analysis.Complex.Convex
import TauCeti.Analysis.Contour.Winding.UnboundedComponent

/-!
# Winding of the fundamental-domain boundary: the exterior

Every point off the closed truncated fundamental domain lies in one of five regions —
below the corner height, right or left of the fundamental strip, above the ceiling, or in
the open unit disc under the arc — and each region sits in the unbounded connected
component of the contour's complement, where the winding number vanishes. Together the
five determinations package as null-homology of the boundary contour in the truncated
fundamental domain, the exterior input to the valence-formula residue count.

## Main declarations

* `TauCeti.ModularForm.sqrt_three_div_two_le_im_fdBoundary`: the image height bound.
* `TauCeti.ModularForm.windingNumber_fdBoundary_eq_zero_of_im_lt`: points below the
  corner height wind zero, with the analogous determinations on the other sides
  (`_of_half_lt_re`, `_of_re_lt_neg_half`, `_of_lt_im`) and in the unit disc
  (`_of_norm_lt_one`).
* `TauCeti.ModularForm.isNullHomologous_fdBoundary`: the packaged null-homology.

## References

The truncated-contour strategy follows the fundamental-domain boundary development of
AINTLIB's `LeanModularForms` (`ForMathlib/FDBoundary.lean`, `FDBoundaryH.lean`,
`FDBoundaryPath.lean`); the winding transport is Tau Ceti's Hungerbühler–Wasem machinery.
-/

public noncomputable section

open Complex Set UpperHalfPlane TauCeti.Contour

open scoped Real

namespace TauCeti

namespace ModularForm

variable {H t : ℝ}

/-- The corner height `√3/2` lies below `1`, the height of the arc's apex. -/
private lemma sqrt_three_div_two_le_one : Real.sqrt 3 / 2 ≤ 1 := by
  rw [div_le_one (by norm_num)]
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
  have h32 : Real.sqrt 3 / 2 ≤ 1 := sqrt_three_div_two_le_one
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
  have h32 : Real.sqrt 3 / 2 ≤ 1 := sqrt_three_div_two_le_one
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

/-- Winding transport through an unbounded preconnected region avoiding the contour: the
region lies in one connected component of the complement, which reaches points far away
where the winding number vanishes. -/
private lemma windingNumber_fdBoundary_eq_zero_of_mem_preconnected {S : Set ℂ}
    (hconn : IsPreconnected S) (hdisj : S ⊆ (fdBoundary H '' uIcc (0 : ℝ) 5)ᶜ)
    (hunb : ∀ R : ℝ, ∃ z ∈ S, R < ‖z‖) {w : ℂ} (hw : w ∈ S) :
    windingNumber (fdBoundary H) 0 5 w = 0 := by
  refine (isPiecewiseC1On_fdBoundary H).windingNumber_eq_zero_of_unbounded_component
    (fdBoundary_closed H).symm fun hbdd => ?_
  obtain ⟨r, hr⟩ := hbdd.subset_closedBall 0
  obtain ⟨z, hzS, hzr⟩ := hunb r
  have hz_comp : z ∈ connectedComponentIn ((fdBoundary H '' uIcc (0 : ℝ) 5)ᶜ) w :=
    hconn.subset_connectedComponentIn hw hdisj hzS
  have := hr hz_comp
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith

/-- Every point strictly below the contour's height winds zero. -/
@[simp]
theorem windingNumber_fdBoundary_eq_zero_of_im_lt (hH : Real.sqrt 3 / 2 ≤ H) {w : ℂ}
    (hw : w.im < Real.sqrt 3 / 2) : windingNumber (fdBoundary H) 0 5 w = 0 := by
  refine windingNumber_fdBoundary_eq_zero_of_mem_preconnected
    (convex_halfSpace_im_lt _).isPreconnected
    ?_ (fun R ↦ ⟨((-(max R 0 + 1) : ℝ) : ℂ) * Complex.I, ?_, ?_⟩) hw
  · rintro z hz ⟨t, ht, rfl⟩
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at ht
    exact absurd hz (not_lt.mpr (sqrt_three_div_two_le_im_fdBoundary hH ht))
  · rw [Set.mem_ofPred_eq, Complex.mul_I_im, Complex.ofReal_re]
    nlinarith [le_max_right R 0, Real.sqrt_nonneg 3]
  · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonpos (by nlinarith [le_max_right R 0])]
    nlinarith [le_max_left R 0]

/-- Every point strictly right of the fundamental strip winds zero. The bound is stated
in simp-normal form so the lemma can participate in simplification. -/
@[simp]
theorem windingNumber_fdBoundary_eq_zero_of_half_lt_re {w : ℂ}
    (hw : 2⁻¹ < w.re) : windingNumber (fdBoundary H) 0 5 w = 0 := by
  refine windingNumber_fdBoundary_eq_zero_of_mem_preconnected
    (convex_halfSpace_re_gt _).isPreconnected
    ?_ (fun R ↦ ⟨((max R 0 + 1 : ℝ) : ℂ), ?_, ?_⟩) hw
  · rintro z hz ⟨t, ht, rfl⟩
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at ht
    have := (abs_le.mp (abs_re_fdBoundary_le_half (H := H) ht.2)).2
    rw [Set.mem_ofPred_eq] at hz
    linarith
  · rw [Set.mem_ofPred_eq, Complex.ofReal_re]
    nlinarith [le_max_right R 0]
  · rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    linarith [le_max_left R 0]

/-- Every point strictly left of the fundamental strip winds zero. -/
@[simp]
theorem windingNumber_fdBoundary_eq_zero_of_re_lt_neg_half {w : ℂ}
    (hw : w.re < -2⁻¹) : windingNumber (fdBoundary H) 0 5 w = 0 := by
  refine windingNumber_fdBoundary_eq_zero_of_mem_preconnected
    (convex_halfSpace_re_lt _).isPreconnected
    ?_ (fun R ↦ ⟨((-(max R 0 + 1) : ℝ) : ℂ), ?_, ?_⟩) hw
  · rintro z hz ⟨t, ht, rfl⟩
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at ht
    have := (abs_le.mp (abs_re_fdBoundary_le_half (H := H) ht.2)).1
    rw [Set.mem_ofPred_eq] at hz
    linarith
  · rw [Set.mem_ofPred_eq, Complex.ofReal_re]
    nlinarith [le_max_right R 0]
  · rw [Complex.norm_real, Real.norm_of_nonpos (by nlinarith [le_max_right R 0])]
    nlinarith [le_max_left R 0]

/-- Every point strictly above the contour's height winds zero. -/
@[simp]
theorem windingNumber_fdBoundary_eq_zero_of_lt_im (hH : 1 ≤ H) {w : ℂ}
    (hw : H < w.im) : windingNumber (fdBoundary H) 0 5 w = 0 := by
  refine windingNumber_fdBoundary_eq_zero_of_mem_preconnected
    (convex_halfSpace_im_gt _).isPreconnected
    ?_ (fun R ↦ ⟨((H + max R 0 + 1 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩) hw
  · rintro z hz ⟨t, ht, rfl⟩
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at ht
    have := im_fdBoundary_le hH ht
    rw [Set.mem_ofPred_eq] at hz
    linarith
  · rw [Set.mem_ofPred_eq]
    have : (((H + max R 0 + 1 : ℝ) : ℂ) * Complex.I).im = H + max R 0 + 1 := by simp
    rw [this]
    nlinarith [le_max_right R 0]
  · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by nlinarith [le_max_right R 0])]
    nlinarith [le_max_left R 0]

/-- Every point of the open unit disc winds zero: the disc sits under the arc, inside the
contour's complement, and connects through the origin to the region below the corner
height. Together with the four half-plane determinations this covers every point off the
closed truncated fundamental domain. -/
@[simp]
theorem windingNumber_fdBoundary_eq_zero_of_norm_lt_one (hH : 1 ≤ H) {w : ℂ}
    (hw : ‖w‖ < 1) : windingNumber (fdBoundary H) 0 5 w = 0 := by
  have hconn : IsPreconnected
      (Metric.ball (0 : ℂ) 1 ∪ {z : ℂ | z.im < Real.sqrt 3 / 2}) := by
    refine IsPreconnected.union 0 (Metric.mem_ball_self one_pos) ?_
      (convex_ball 0 1).isPreconnected (convex_halfSpace_im_lt _).isPreconnected
    rw [Set.mem_ofPred_eq, Complex.zero_im]
    positivity
  have h32 : Real.sqrt 3 / 2 ≤ 1 := sqrt_three_div_two_le_one
  refine windingNumber_fdBoundary_eq_zero_of_mem_preconnected hconn ?_
    (fun R ↦ ⟨((-(max R 0 + 1) : ℝ) : ℂ) * Complex.I, Or.inr ?_, ?_⟩)
    (Or.inl (by rwa [Metric.mem_ball, dist_zero_right]))
  · rintro z (hz | hz) ⟨t, ht, rfl⟩ <;>
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at ht
    · rw [Metric.mem_ball, dist_zero_right] at hz
      exact absurd hz (not_lt.mpr (one_le_norm_fdBoundary hH ht))
    · exact absurd hz (not_lt.mpr (sqrt_three_div_two_le_im_fdBoundary (h32.trans hH) ht))
  · rw [Set.mem_ofPred_eq, Complex.mul_I_im, Complex.ofReal_re]
    nlinarith [le_max_right R 0, Real.sqrt_nonneg 3]
  · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonpos (by nlinarith [le_max_right R 0])]
    nlinarith [le_max_left R 0]

/-- The boundary contour is null-homologous in the truncated fundamental domain: every
point off the closed truncated domain lies in one of the five exterior regions, where the
winding number vanishes. -/
theorem isNullHomologous_fdBoundary (hH : 1 ≤ H) :
    IsNullHomologous (fdBoundary H) 0 5
      (UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H) := by
  have h32 : Real.sqrt 3 / 2 ≤ 1 := sqrt_three_div_two_le_one
  rw [isNullHomologous_iff]
  intro z hz
  rw [ModularGroup.coe_truncatedFundamentalDomain, Set.mem_ofPred_eq, not_and_or, not_and_or,
    not_and_or, not_le, not_le, not_le, not_le] at hz
  rcases hz with him | hzH | hre | hnorm
  · exact windingNumber_fdBoundary_eq_zero_of_im_lt (h32.trans hH)
      (him.trans_le (by positivity))
  · exact windingNumber_fdBoundary_eq_zero_of_lt_im hH hzH
  · rcases lt_abs.mp hre with h | h
    · exact windingNumber_fdBoundary_eq_zero_of_half_lt_re (by simpa using h)
    · refine windingNumber_fdBoundary_eq_zero_of_re_lt_neg_half ?_
      norm_num at h ⊢
      linarith
  · exact windingNumber_fdBoundary_eq_zero_of_norm_lt_one hH hnorm

/-- The boundary contour lies in the closed truncated fundamental domain. -/
lemma fdBoundary_mem_coe_truncatedFundamentalDomain (hH : 1 ≤ H) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 5) :
    fdBoundary H t ∈ UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H := by
  have h32 : Real.sqrt 3 / 2 ≤ 1 := sqrt_three_div_two_le_one
  rw [ModularGroup.coe_truncatedFundamentalDomain, Set.mem_ofPred_eq]
  refine ⟨?_, im_fdBoundary_le hH ht, abs_re_fdBoundary_le_half ht.2,
    one_le_norm_fdBoundary hH ht⟩
  have := sqrt_three_div_two_le_im_fdBoundary (h32.trans hH) ht
  nlinarith [Real.sqrt_nonneg 3]

end ModularForm

end TauCeti

end
