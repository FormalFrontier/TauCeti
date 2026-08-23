/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Containment
public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic

import Mathlib.Analysis.Complex.Convex
import TauCeti.Analysis.Contour.Winding.Integer
import TauCeti.Analysis.Contour.Winding.LocallyConstant
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Decomposition
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.PieceLog

/-!
# The boundary contour winds `-1` above the corner row

For a point of the open strip `|re| < 1/2` strictly between height `1` and the ceiling
height `H`, the boundary contour winds exactly `-1`: the contour is traversed clockwise
around its interior. The four piece values are principal logarithms whose arguments each
lie in `(-π, 0)`, so their sum lies in `(-4π, 0)`; integrality of the winding number then
pins the value to `-1`.

Points of the truncated fundamental domain below height `1` are reached from this strip by
winding transport: the vertical lift of an interior point into the strip, together with the
open strip box, is one preconnected region avoiding the contour, so the value transports.

## Main declarations

* `TauCeti.ModularForm.windingNumber_fdBoundary_eq_neg_one_of_interior`.

## References

The interior determination follows the fundamental-domain boundary development of AINTLIB's
`LeanModularForms` (`ForMathlib/FDBoundary.lean`, `FDBoundaryH.lean`, `FDBoundaryPath.lean`),
adapted to the raw-path winding machinery: the piece decomposition and logarithm values are
summed and pinned by integrality rather than evaluated termwise.
-/

public section

open Set TauCeti.Contour UpperHalfPlane

namespace TauCeti

namespace ModularForm

variable {H : ℝ} {w : ℂ}

/-- Off-curve avoidance for interior points: each piece is separated from `w` in one
coordinate, the arc by the norm. -/
theorem fdBoundary_ne_of_abs_re_lt_half_of_one_lt_norm_of_im_lt (hre : |w.re| < 1 / 2)
    (hnorm : 1 < ‖w‖) (him : w.im < H) : ∀ t ∈ Icc (0 : ℝ) 5, fdBoundary H t ≠ w := by
  obtain ⟨hx₁, hx₂⟩ := abs_lt.mp hre
  intro t ht h_eq
  rcases le_or_gt t 1 with h1 | h1
  · have := re_fdBoundarySegment1 H ⟨ht.1, h1⟩
    rw [h_eq] at this
    linarith
  · rcases le_or_gt t 3 with h3 | h3
    · have : ‖fdBoundary H t‖ = 1 := by
        rw [eqOn_fdBoundary_arc H ⟨h1.le, h3⟩, norm_circleMap_zero, abs_one]
      rw [h_eq] at this
      linarith
    · rcases le_or_gt t 4 with h4 | h4
      · have := re_fdBoundarySegment4 H ⟨h3.le, h4⟩
        rw [h_eq] at this
        linarith
      · have := im_fdBoundarySegment5 H ⟨h4.le, ht.2⟩
        rw [h_eq] at this
        linarith

/-- The endpoint ratio of a piece has negative argument when its junction chord turns
clockwise as seen from `w`; the four instances below feed the pinning argument. -/
private lemma arg_div_neg {z₁ z₂ : ℂ} (hnum : z₂.im * z₁.re - z₂.re * z₁.im < 0) :
    (z₂ / z₁).arg < 0 := by
  -- a vanishing denominator would make the chord determinant `0`, contradicting `hnum`
  have hz₁ : z₁ ≠ 0 := by rintro rfl; simp at hnum
  rw [Complex.arg_neg_iff, Complex.div_im, div_sub_div_same]
  exact div_neg_of_neg_of_pos hnum (Complex.normSq_pos.mpr hz₁)

/-- The winding number of the boundary contour about a point of the open strip is the
normalized sum of the four pieces' principal logarithms. -/
private theorem windingNumber_fdBoundary_eq_two_pi_I_inv_mul_sum_log (hx : |w.re| < 1 / 2)
    (hy1 : 1 < w.im) (hyH : w.im < H) :
    windingNumber (fdBoundary H) 0 5 w = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (Complex.log (((ρ : ℂ) + 1 - w) / (1 / 2 + H * Complex.I - w)) +
        Complex.log (((ρ : ℂ) - w) / ((ρ : ℂ) + 1 - w)) +
        Complex.log ((-1 / 2 + H * Complex.I - w) / ((ρ : ℂ) - w)) +
        Complex.log ((1 / 2 + H * Complex.I - w) / (-1 / 2 + H * Complex.I - w))) := by
  obtain ⟨hx₁, hx₂⟩ := abs_lt.mp hx
  have hnorm : 1 < ‖w‖ := hy1.trans_le (Complex.im_le_norm w)
  rw [windingNumber_fdBoundary_eq_sum_pieces
      (fdBoundary_ne_of_abs_re_lt_half_of_one_lt_norm_of_im_lt hx hnorm hyH),
    windingNumber_fdBoundarySegment1_eq_log hx₂, windingNumber_fdBoundary_arc_eq_log hy1,
    windingNumber_fdBoundarySegment4_eq_log hx₁, windingNumber_fdBoundarySegment5_eq_log hyH]
  ring

/-- If the winding number of the boundary contour about a point of the open strip equals the
integer `n`, then `2 * π * n` is the sum of the arguments of the four piece ratios. -/
private theorem two_pi_mul_int_eq_sum_arg_of_windingNumber_fdBoundary_eq
    (hx : |w.re| < 1 / 2) (hy1 : 1 < w.im)
    (hyH : w.im < H) {n : ℤ} (hn : windingNumber (fdBoundary H) 0 5 w = n) :
    2 * Real.pi * (n : ℝ) = (((ρ : ℂ) + 1 - w) / (1 / 2 + H * Complex.I - w)).arg +
      (((ρ : ℂ) - w) / ((ρ : ℂ) + 1 - w)).arg +
      ((-1 / 2 + H * Complex.I - w) / ((ρ : ℂ) - w)).arg +
      ((1 / 2 + H * Complex.I - w) / (-1 / 2 + H * Complex.I - w)).arg := by
  -- clear the `(2πI)⁻¹`, then read off the imaginary part: each `log`'s is its argument
  have hmul := (inv_mul_eq_iff_eq_mul₀ Complex.two_pi_I_ne_zero).mp
    ((windingNumber_fdBoundary_eq_two_pi_I_inv_mul_sum_log hx hy1 hyH).symm.trans hn)
  simpa [Complex.log_im, Complex.add_im, Complex.mul_im] using congrArg Complex.im hmul.symm

/-- The winding number of the boundary contour is `-1` on the open strip above the corner
row: the region `|re w| < 1/2`, `1 < im w < H`. -/
private theorem windingNumber_fdBoundary_eq_neg_one_of_one_lt_im (hx : |w.re| < 1 / 2)
    (hy1 : 1 < w.im) (hyH : w.im < H) : windingNumber (fdBoundary H) 0 5 w = -1 := by
  obtain ⟨hx₁, hx₂⟩ := abs_lt.mp hx
  have h32 : Real.sqrt 3 / 2 ≤ 1 := sqrt_three_div_two_lt_one.le
  have hnorm : 1 < ‖w‖ := hy1.trans_le (Complex.im_le_norm w)
  obtain ⟨n, hn⟩ := (isPiecewiseC1On_fdBoundary H).exists_int_windingNumber
    (fdBoundary_closed H).symm
    (by rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
        exact fdBoundary_ne_of_abs_re_lt_half_of_one_lt_norm_of_im_lt hx hnorm hyH)
  have hIm := two_pi_mul_int_eq_sum_arg_of_windingNumber_fdBoundary_eq hx hy1 hyH hn
  -- the four endpoint differences turn clockwise, so each argument lies in `(-π, 0)`; the
  -- sum is then in `(-4π, 0)`, which pins the integer to `-1`
  have ha₁ : (((ρ : ℂ) + 1 - w) / (1 / 2 + H * Complex.I - w)).arg < 0 :=
    arg_div_neg <| by norm_num [ρ]; nlinarith
  have ha₂ : (((ρ : ℂ) - w) / ((ρ : ℂ) + 1 - w)).arg < 0 :=
    arg_div_neg <| by norm_num [ρ]; nlinarith
  have ha₃ : ((-1 / 2 + H * Complex.I - w) / ((ρ : ℂ) - w)).arg < 0 :=
    arg_div_neg <| by norm_num [ρ]; nlinarith
  have ha₄ : ((1 / 2 + H * Complex.I - w) / (-1 / 2 + H * Complex.I - w)).arg < 0 :=
    arg_div_neg <| by norm_num [ρ]; nlinarith
  have hb₁ := Complex.neg_pi_lt_arg (((ρ : ℂ) + 1 - w) / (1 / 2 + H * Complex.I - w))
  have hb₂ := Complex.neg_pi_lt_arg (((ρ : ℂ) - w) / ((ρ : ℂ) + 1 - w))
  have hb₃ := Complex.neg_pi_lt_arg ((-1 / 2 + H * Complex.I - w) / ((ρ : ℂ) - w))
  have hb₄ := Complex.neg_pi_lt_arg ((1 / 2 + H * Complex.I - w) / (-1 / 2 + H * Complex.I - w))
  -- the bound is real-valued: `hIm` reads `2 * π * n` against the four argument bounds, and
  -- `Real.pi`'s own bounds are facts about `ℝ`, so `n` is pinned there and then cast back
  have hn2R : (-2 : ℝ) < (n : ℝ) := by nlinarith
  have hn0R : (n : ℝ) < 0 := by nlinarith
  have hn2 : (-2 : ℤ) < n := by exact_mod_cast hn2R
  have hn0 : n < 0 := by exact_mod_cast hn0R
  have hneg : n = -1 := by lia
  simp [hn, hneg]

/-- Points of the lifted segment and of the strip box satisfy the interior avoidance
facts: strip-bounded real part, norm above the circle, height below the ceiling. -/
private lemma interior_avoiding_facts (hH : 1 < H) {w : ℂ} (hnorm : 1 < ‖w‖)
    (hre : |w.re| < 1 / 2) (him : w.im < H) (hpos : 0 < w.im) {z : ℂ}
    (hz : z ∈ segment ℝ w ((w.re : ℂ) + (((max w.im 1 + H) / 2 : ℝ) : ℂ) * Complex.I) ∪
      {z : ℂ | |z.re| < 1 / 2 ∧ 1 < z.im ∧ z.im < H}) :
    |z.re| < 1 / 2 ∧ 1 < ‖z‖ ∧ z.im < H := by
  set y : ℝ := (max w.im 1 + H) / 2 with hy_def
  have htop_re : ((w.re : ℂ) + (y : ℝ) * Complex.I).re = w.re := by simp
  have htop_im : ((w.re : ℂ) + (y : ℝ) * Complex.I).im = y := by simp
  have hyw : w.im ≤ y := by
    rw [hy_def]
    nlinarith [le_max_left w.im 1, him]
  have hyH : y < H := by
    rw [hy_def]
    rcases max_cases w.im 1 with ⟨heq, -⟩ | ⟨heq, -⟩ <;> rw [heq] <;> nlinarith
  rcases hz with hz | hz
  · obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    have hre' : (a • w + b • ((w.re : ℂ) + (y : ℝ) * Complex.I)).re = w.re := by
      rw [Complex.add_re, Complex.smul_re, Complex.smul_re, htop_re]
      linear_combination w.re * hab
    have him' : (a • w + b • ((w.re : ℂ) + (y : ℝ) * Complex.I)).im = a * w.im + b * y := by
      rw [Complex.add_im, Complex.smul_im, Complex.smul_im, htop_im, smul_eq_mul, smul_eq_mul]
    have hs_lb : w.im ≤ a * w.im + b * y := by nlinarith [mul_nonneg hb (sub_nonneg.mpr hyw)]
    refine ⟨by rw [hre']; exact hre, ?_, by rw [him']; nlinarith⟩
    have hw2 : 1 < w.re * w.re + w.im * w.im := by
      have hsq := Complex.sq_norm w
      rw [Complex.normSq_apply] at hsq
      nlinarith [norm_nonneg w]
    have himsq : w.im * w.im ≤ (a * w.im + b * y) * (a * w.im + b * y) :=
      mul_self_le_mul_self hpos.le hs_lb
    have hzsq : 1 < ‖a • w + b • ((w.re : ℂ) + (y : ℝ) * Complex.I)‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hre', him']
      nlinarith
    nlinarith [norm_nonneg (a • w + b • ((w.re : ℂ) + (y : ℝ) * Complex.I))]
  · exact ⟨hz.1, hz.2.1.trans_le (Complex.im_le_norm z),
      hz.2.2⟩

/-- **The boundary contour winds `-1` about every point of the open truncated fundamental
domain**: the region `1 < ‖w‖`, `|re w| < 1/2`, `0 < im w < H`. -/
theorem windingNumber_fdBoundary_eq_neg_one_of_interior (hH : 1 < H) {w : ℂ}
    (hnorm : 1 < ‖w‖) (hre : |w.re| < 1 / 2) (hpos : 0 < w.im) (him : w.im < H) :
    windingNumber (fdBoundary H) 0 5 w = -1 := by
  set y : ℝ := (max w.im 1 + H) / 2 with hy_def
  have hy1 : 1 < y := by
    rw [hy_def]
    nlinarith [le_max_right w.im 1]
  have hyH : y < H := by
    rw [hy_def]
    rcases max_cases w.im 1 with ⟨heq, -⟩ | ⟨heq, -⟩ <;> rw [heq] <;> nlinarith
  have htop_mem_box : ((w.re : ℂ) + (y : ℝ) * Complex.I) ∈
      {z : ℂ | |z.re| < 1 / 2 ∧ 1 < z.im ∧ z.im < H} :=
    ⟨by simpa using hre, by simpa using hy1, by simpa using hyH⟩
  have hbox_convex : Convex ℝ {z : ℂ | |z.re| < 1 / 2 ∧ 1 < z.im ∧ z.im < H} := by
    have hset : {z : ℂ | |z.re| < 1 / 2 ∧ 1 < z.im ∧ z.im < H} =
        ({z : ℂ | z.re < 1 / 2} ∩ {z : ℂ | -(1 / 2) < z.re}) ∩
          ({z : ℂ | 1 < z.im} ∩ {z : ℂ | z.im < H}) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, abs_lt]
      tauto
    rw [hset]
    exact ((convex_halfSpace_re_lt _).inter (convex_halfSpace_re_gt _)).inter
      ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _))
  have hconn : IsPreconnected (segment ℝ w ((w.re : ℂ) + (y : ℝ) * Complex.I) ∪
      {z : ℂ | |z.re| < 1 / 2 ∧ 1 < z.im ∧ z.im < H}) :=
    IsPreconnected.union ((w.re : ℂ) + (y : ℝ) * Complex.I)
      (right_mem_segment ℝ w _) htop_mem_box
      (convex_segment w _).isPreconnected hbox_convex.isPreconnected
  have hdisj : (segment ℝ w ((w.re : ℂ) + (y : ℝ) * Complex.I) ∪
      {z : ℂ | |z.re| < 1 / 2 ∧ 1 < z.im ∧ z.im < H}) ⊆
        (fdBoundary H '' uIcc (0 : ℝ) 5)ᶜ := by
    rintro z hz ⟨t, ht, h_eq⟩
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at ht
    obtain ⟨hz_re, hz_norm, hz_im⟩ := interior_avoiding_facts hH hnorm hre him hpos hz
    exact fdBoundary_ne_of_abs_re_lt_half_of_one_lt_norm_of_im_lt hz_re hz_norm hz_im t ht h_eq
  rw [(isPiecewiseC1On_fdBoundary H).windingNumber_eq_of_mem_connectedComponentIn
      (fdBoundary_closed H).symm
      (hconn.subset_connectedComponentIn (Or.inr htop_mem_box) hdisj
        (Or.inl (left_mem_segment ℝ w _))),
    windingNumber_fdBoundary_eq_neg_one_of_one_lt_im (by simpa using hre)
      (by simpa using hy1) (by simpa using hyH)]

end ModularForm

end TauCeti

end
