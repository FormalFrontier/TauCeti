/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Modular
public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Containment

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

The file also carries the arc-excision geometry shared by the corner winding computations
at `i`, at `ρ` and at `ρ + 1`. Each excises a parameter window around its corner and needs
that window's chord to be exactly the excision radius `ε`. The half-width realising this for
a radius below the corner chord `2·sin(π/12)` is stated once here rather than three times.

## Main declarations

* `TauCeti.ModularForm.windingNumber_fdBoundary_eq_zero_of_im_lt`: points below the
  corner height wind zero, with the analogous determinations on the other sides
  (`_of_half_lt_re`, `_of_re_lt_neg_half`, `_of_lt_im`) and in the unit disc
  (`_of_norm_lt_one`).
* `TauCeti.ModularForm.isNullHomologous_fdBoundary`: the packaged null-homology.
* `TauCeti.ModularForm.fdBoundaryArcExcisionHalfWidth`: the parameter half-width whose
  chord along the arc is a prescribed `ε` below the corner chord, characterised under that
  bound by `TauCeti.ModularForm.fdBoundaryArcExcisionHalfWidth_pos_and_lt_one_and_two_mul_sin_eq`.

## References

The truncated-contour strategy follows the fundamental-domain boundary development of
AINTLIB's `LeanModularForms` (`ForMathlib/FDBoundary.lean`, `FDBoundaryH.lean`,
`FDBoundaryPath.lean`); the winding transport is Tau Ceti's Hungerbühler–Wasem machinery.

The arc-excision geometry is not from those files: it is extracted from the same project's
winding-value development (`ForMathlib/ValenceFormula/WindingWeights/I.lean`, `Rho.lean` and
`RhoPlusOne.lean`), where each corner computation built its own chord-matched half-width.
It is stated once here so the three share it.
-/

public noncomputable section

open Complex Set UpperHalfPlane TauCeti.Contour

open scoped Real

namespace TauCeti

namespace ModularForm

variable {H t : ℝ}

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
  have h32 : Real.sqrt 3 / 2 ≤ 1 := sqrt_three_div_two_lt_one.le
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
  have h32 : Real.sqrt 3 / 2 ≤ 1 := sqrt_three_div_two_lt_one.le
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



/-- **The chord-matched excision half-width.** The parameter half-width whose chord along
the unit-circle arc is the excision radius `ε`.

The chord identity `2·sin(δ·π/12) = ε` holds throughout `|ε| ≤ 2`, the range on which
`Real.arcsin` inverts the sine, and fails beyond it because `Real.arcsin` saturates.
`fdBoundaryArcExcisionHalfWidth_pos_and_lt_one_and_two_mul_sin_eq` nonetheless assumes the narrower
`0 < ε < 2·sin(π/12)`: that is the range the excision arguments need, because it also places
the half-width strictly between `0` and `1`, inside the corner's own arc window. -/
noncomputable def fdBoundaryArcExcisionHalfWidth (ε : ℝ) : ℝ := 12 / Real.pi * Real.arcsin (ε / 2)

/-- The chord-matched excision half-width, unfolded. -/
@[simp] lemma fdBoundaryArcExcisionHalfWidth_def (ε : ℝ) :
    fdBoundaryArcExcisionHalfWidth ε = 12 / Real.pi * Real.arcsin (ε / 2) := (rfl)

/-- **The chord-matched excision half-width does what it is for.** For an excision radius `ε`
below the corner chord `2·sin(π/12)`, the half-width lies strictly between `0` and `1` and
reproduces `ε` as its own chord: `2·sin(δ·π/12) = ε`.

This is the trigonometric content shared by the excision constructions at `i`, at `ρ` and at
`ρ + 1`; it needs no upper bound on `ε` beyond the chord bound. -/
lemma fdBoundaryArcExcisionHalfWidth_pos_and_lt_one_and_two_mul_sin_eq {ε : ℝ} (hε : 0 < ε)
    (hε₃ : ε < 2 * Real.sin (Real.pi / 12)) :
    0 < fdBoundaryArcExcisionHalfWidth ε ∧ fdBoundaryArcExcisionHalfWidth ε < 1 ∧
      2 * Real.sin (fdBoundaryArcExcisionHalfWidth ε * (Real.pi / 12)) = ε := by
  rw [fdBoundaryArcExcisionHalfWidth_def]
  have hπ := Real.pi_pos
  have hsin1 : Real.sin (Real.pi / 12) ≤ 1 := Real.sin_le_one _
  have harc_pos : 0 < Real.arcsin (ε / 2) := Real.arcsin_pos.mpr (by linarith)
  have harc_lt : Real.arcsin (ε / 2) < Real.pi / 12 := by
    have h1 : Real.arcsin (ε / 2) < Real.arcsin (Real.sin (Real.pi / 12)) :=
      Real.arcsin_lt_arcsin (by linarith) (by linarith) hsin1
    rwa [Real.arcsin_sin (by linarith) (by linarith)] at h1
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_lt_one hπ]
    linarith
  · have hδπ : 12 / Real.pi * Real.arcsin (ε / 2) * (Real.pi / 12) = Real.arcsin (ε / 2) := by
      field_simp
    rw [hδπ, Real.sin_arcsin (by linarith) (by linarith)]
    ring


end ModularForm
end TauCeti

end
