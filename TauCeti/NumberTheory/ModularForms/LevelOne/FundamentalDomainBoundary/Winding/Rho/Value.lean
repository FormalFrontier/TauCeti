/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Basic
public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.Rho.Geometry

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.Basic
import TauCeti.Analysis.Contour.LogDerivFTC
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv

/-!
# The winding number of the boundary contour at `ρ`

The generalized winding number of the truncated-fundamental-domain boundary about the
corner `ρ` is `-1/6`. Over the corner-excised parameter ranges the logarithmic integral of
the shifted contour `t ↦ fdBoundary H t - ρ` telescopes piece by piece through the
boundary-tolerant logarithmic fundamental theorem, and the `ε`-excision of the principal
value collapses to exactly those ranges with asymmetric half-widths — chord-matched
`δ_L(ε) = 12/π·arcsin(ε/2)` on the arc side and linear `δ_R(ε) = ε/(H - √3/2)` on the
vertical side. Both endpoint distances are then exactly `ε`, the log-norm parts cancel, and
only the corner angle defect `π/3` survives to the limit.

## Main declarations

* `TauCeti.ModularForm.hasCauchyPVAt_fdBoundary_rho` (the principal value `-πi/3`).
* `TauCeti.ModularForm.windingNumber_fdBoundary_rho` (the winding number `-1/6`).

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/WindingWeights/Rho.lean`) this file ports onto
  the current Mathlib pin.
* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized
  Residue Theorem*, arXiv:1808.00997.
-/

public section

open Complex Filter MeasureTheory Set Topology

namespace TauCeti

open Contour

namespace ModularForm


variable {H δL δR : ℝ}


/-- The right-vertical piece `[0, 1]` of the telescope at `ρ`. -/
private lemma telescope_rho_piece_right_vertical (H : ℝ) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
        (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)))
      volume 0 1 ∧
    ∫ t in (0 : ℝ)..1,
        deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
          (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)) =
      Complex.log (fdBoundary H 1 - (UpperHalfPlane.ρ : ℂ)) -
        Complex.log (fdBoundary H 0 - (UpperHalfPlane.ρ : ℂ)) := by
  have heval : ∀ s ∈ Icc (0 : ℝ) 1, fdBoundary H s = fdBoundarySegment1 H s := fun s hs ↦
    fdBoundary_of_le_one hs.2
  have hd : deriv (fun s ↦ fdBoundarySegment1 H s - (UpperHalfPlane.ρ : ℂ)) =
      fun _ ↦ (UpperHalfPlane.ρ : ℂ) + 1 - (1 / 2 + H * Complex.I) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundarySegment1]
  exact intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_mem_slitPlane_of_le
    (g := fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ))
    (h := fun s ↦ fdBoundarySegment1 H s - (UpperHalfPlane.ρ : ℂ)) (by norm_num)
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundarySegment1 H s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundarySegment1 H t).differentiableAt.sub_const _)
    (by rw [hd]; exact continuousOn_const)
    (fun t ht ↦ heval t ht ▸ fdBoundary_sub_rho_mem_slitPlane_of_le_one H ht)
    (fun t ht ↦ congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval 0 (left_mem_Icc.mpr (by norm_num))))
    (congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval 1 (right_mem_Icc.mpr (by norm_num))))

/-- The first arc piece `[1, 2]` of the telescope at `ρ`. -/
private lemma telescope_rho_piece_arc_first (H : ℝ) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
        (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)))
      volume 1 2 ∧
    ∫ t in (1 : ℝ)..2,
        deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
          (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)) =
      Complex.log (fdBoundary H 2 - (UpperHalfPlane.ρ : ℂ)) -
        Complex.log (fdBoundary H 1 - (UpperHalfPlane.ρ : ℂ)) := by
  have heval : ∀ s ∈ Icc (1 : ℝ) 2, fdBoundary H s = fdBoundarySegment2 s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h1 | h1
    · rw [← h1, fdBoundary_apply_one, fdBoundarySegment2_apply_one]
    · exact fdBoundary_of_le_two h1 hs.2
  have hd : deriv (fun s ↦ fdBoundarySegment2 s - (UpperHalfPlane.ρ : ℂ)) = fun s ↦
      (Real.pi / 2 - Real.pi / 3) •
        (circleMap 0 1 (Real.pi / 3 + (s - 1) * (Real.pi / 2 - Real.pi / 3)) * Complex.I) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundarySegment2]
  have hθc : Continuous fun s : ℝ ↦ Real.pi / 3 + (s - 1) * (Real.pi / 2 - Real.pi / 3) := by
    fun_prop
  exact intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_mem_slitPlane_of_le
    (g := fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ))
    (h := fun s ↦ fdBoundarySegment2 s - (UpperHalfPlane.ρ : ℂ)) (by norm_num)
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundarySegment2 s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundarySegment2 t).differentiableAt.sub_const _)
    (by
      rw [hd]
      exact (Continuous.const_smul
        (((continuous_circleMap 0 1).comp hθc).mul continuous_const)
        (Real.pi / 2 - Real.pi / 3)).continuousOn)
    (fun t ht ↦ heval t ht ▸
      fdBoundary_sub_rho_arc_mem_slitPlane_of_lt_three H ht.1 (by linarith [ht.2]))
    (fun t ht ↦ congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval 1 (left_mem_Icc.mpr (by norm_num))))
    (congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval 2 (right_mem_Icc.mpr (by norm_num))))

/-- The second arc piece `[2, 3-δ_L]` of the telescope at `ρ`, stopping short of the
corner. -/
private lemma telescope_rho_piece_arc_second (H : ℝ) (hδL : 0 < δL) (hδL1 : δL < 1) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
        (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)))
      volume 2 (3 - δL) ∧
    ∫ t in (2 : ℝ)..(3 - δL),
        deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
          (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)) =
      Complex.log (fdBoundary H (3 - δL) - (UpperHalfPlane.ρ : ℂ)) -
        Complex.log (fdBoundary H 2 - (UpperHalfPlane.ρ : ℂ)) := by
  have hab : (2 : ℝ) ≤ 3 - δL := by linarith
  have heval : ∀ s ∈ Icc (2 : ℝ) (3 - δL), fdBoundary H s = fdBoundarySegment3 s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h2 | h2
    · rw [← h2, fdBoundary_apply_two, fdBoundarySegment3_apply_two]
    · exact fdBoundary_of_le_three h2 (by linarith [hs.2])
  have hd : deriv (fun s ↦ fdBoundarySegment3 s - (UpperHalfPlane.ρ : ℂ)) = fun s ↦
      (2 * Real.pi / 3 - Real.pi / 2) •
        (circleMap 0 1 (Real.pi / 2 + (s - 2) * (2 * Real.pi / 3 - Real.pi / 2)) *
          Complex.I) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundarySegment3]
  have hθc : Continuous fun s : ℝ ↦
      Real.pi / 2 + (s - 2) * (2 * Real.pi / 3 - Real.pi / 2) := by
    fun_prop
  exact intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_mem_slitPlane_of_le
    (g := fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ))
    (h := fun s ↦ fdBoundarySegment3 s - (UpperHalfPlane.ρ : ℂ)) hab
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundarySegment3 s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundarySegment3 t).differentiableAt.sub_const _)
    (by
      rw [hd]
      exact (Continuous.const_smul
        (((continuous_circleMap 0 1).comp hθc).mul continuous_const)
        (2 * Real.pi / 3 - Real.pi / 2)).continuousOn)
    (fun t ht ↦ heval t ht ▸
      fdBoundary_sub_rho_arc_mem_slitPlane_of_lt_three H (by linarith [ht.1])
        (by linarith [ht.2]))
    (fun t ht ↦ congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval 2 (left_mem_Icc.mpr hab)))
    (congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval (3 - δL) (right_mem_Icc.mpr hab)))

/-- The left-vertical piece `[3+δ_R, 4]` of the telescope at `ρ`, starting past the
corner. -/
private lemma telescope_rho_piece_left_vertical (hH : Real.sqrt 3 / 2 < H) (hδR : 0 < δR)
    (hδR1 : δR ≤ 1) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
        (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)))
      volume (3 + δR) 4 ∧
    ∫ t in (3 + δR : ℝ)..4,
        deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
          (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)) =
      Complex.log (fdBoundary H 4 - (UpperHalfPlane.ρ : ℂ)) -
        Complex.log (fdBoundary H (3 + δR) - (UpperHalfPlane.ρ : ℂ)) := by
  have hab : (3 + δR : ℝ) ≤ 4 := by linarith
  have heval : ∀ s ∈ Icc (3 + δR : ℝ) 4, fdBoundary H s = fdBoundarySegment4 H s :=
    fun s hs ↦ fdBoundary_of_le_four (by linarith [hs.1]) hs.2
  have hd : deriv (fun s ↦ fdBoundarySegment4 H s - (UpperHalfPlane.ρ : ℂ)) =
      fun _ ↦ -1 / 2 + H * Complex.I - (UpperHalfPlane.ρ : ℂ) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundarySegment4]
  exact intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_mem_slitPlane_of_le
    (g := fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ))
    (h := fun s ↦ fdBoundarySegment4 H s - (UpperHalfPlane.ρ : ℂ)) hab
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundarySegment4 H s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundarySegment4 H t).differentiableAt.sub_const _)
    (by rw [hd]; exact continuousOn_const)
    (fun t ht ↦ heval t ht ▸
      fdBoundary_sub_rho_mem_slitPlane_of_three_lt hH (by linarith [ht.1]) ht.2)
    (fun t ht ↦ congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval (3 + δR) (left_mem_Icc.mpr hab)))
    (congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval 4 (right_mem_Icc.mpr hab)))

/-- The ceiling piece `[4, 5]` of the telescope at `ρ`. -/
private lemma telescope_rho_piece_ceiling (hH : Real.sqrt 3 / 2 < H) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
        (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)))
      volume 4 5 ∧
    ∫ t in (4 : ℝ)..5,
        deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
          (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)) =
      Complex.log (fdBoundary H 5 - (UpperHalfPlane.ρ : ℂ)) -
        Complex.log (fdBoundary H 4 - (UpperHalfPlane.ρ : ℂ)) := by
  have heval : ∀ s ∈ Icc (4 : ℝ) 5, fdBoundary H s = fdBoundarySegment5 H s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h4 | h4
    · rw [← h4, fdBoundary_apply_four, fdBoundarySegment5_apply_four]
    · exact fdBoundary_of_gt_four h4
  have hd : deriv (fun s ↦ fdBoundarySegment5 H s - (UpperHalfPlane.ρ : ℂ)) =
      fun _ ↦ (1 : ℂ) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundarySegment5]
  exact intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_mem_slitPlane_of_le
    (g := fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ))
    (h := fun s ↦ fdBoundarySegment5 H s - (UpperHalfPlane.ρ : ℂ)) (by norm_num)
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundarySegment5 H s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundarySegment5 H t).differentiableAt.sub_const _)
    (by rw [hd]; exact continuousOn_const)
    (fun t ht ↦ heval t ht ▸ fdBoundary_sub_rho_mem_slitPlane_of_mem_Icc_four_five hH ht)
    (fun t ht ↦ congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval 4 (left_mem_Icc.mpr (by norm_num))))
    (congrArg (· - (UpperHalfPlane.ρ : ℂ)) (heval 5 (right_mem_Icc.mpr (by norm_num))))

/-- **The logarithmic telescope at `ρ`**: over the corner-excluded ranges the
logarithmic integral of the shifted contour is integrable and evaluates to the
difference of the endpoint logarithms beside the corner — no branch crossing occurs. -/
private theorem ftc_logDeriv_telescope_rho (H : ℝ) (hH : Real.sqrt 3 / 2 < H) {δL δR : ℝ}
    (hδL : 0 < δL) (hδL1 : δL < 1) (hδR : 0 < δR) (hδR1 : δR ≤ 1) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
        (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)))
      volume 0 (3 - δL) ∧
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
        (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)))
      volume (3 + δR) 5 ∧
    (∫ t in (0 : ℝ)..(3 - δL),
        deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
          (fdBoundary H t - (UpperHalfPlane.ρ : ℂ))) +
      (∫ t in (3 + δR : ℝ)..5,
        deriv (fun s ↦ fdBoundary H s - (UpperHalfPlane.ρ : ℂ)) t /
          (fdBoundary H t - (UpperHalfPlane.ρ : ℂ))) =
      Complex.log (fdBoundary H (3 - δL) - (UpperHalfPlane.ρ : ℂ)) -
        Complex.log (fdBoundary H (3 + δR) - (UpperHalfPlane.ρ : ℂ)) := by
  obtain ⟨hi01, he01⟩ := telescope_rho_piece_right_vertical H
  obtain ⟨hi12, he12⟩ := telescope_rho_piece_arc_first H
  obtain ⟨hi23, he23⟩ := telescope_rho_piece_arc_second H hδL hδL1
  obtain ⟨hi34, he34⟩ := telescope_rho_piece_left_vertical hH hδR hδR1
  obtain ⟨hi45, he45⟩ := telescope_rho_piece_ceiling hH
  have hint02 := hi01.trans hi12
  refine ⟨hint02.trans hi23, hi34.trans hi45, ?_⟩
  have hlog50 : Complex.log (fdBoundary H 5 - (UpperHalfPlane.ρ : ℂ)) =
      Complex.log (fdBoundary H 0 - (UpperHalfPlane.ρ : ℂ)) := by
    rw [fdBoundary_apply_five, fdBoundary_apply_zero]
  rw [← intervalIntegral.integral_add_adjacent_intervals hint02 hi23,
    ← intervalIntegral.integral_add_adjacent_intervals hi01 hi12,
    ← intervalIntegral.integral_add_adjacent_intervals hi34 hi45,
    he01, he12, he23, he34, he45, hlog50]
  ring


variable {H ε δ t : ℝ}

/-- Far from the corner along the arc, the chord distance strictly exceeds the excision
chord. -/
private lemma lt_norm_fdBoundary_sub_rho_arc_of_far (harc : t ∈ Icc (1 : ℝ) 3)
    (hd : 0 < δ) (hd1 : δ < 1) (hfar : δ < |t - 3|) :
    2 * Real.sin (δ * (Real.pi / 12)) < ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ := by
  have habs2 : |t - 3| ≤ 2 := abs_le.mpr ⟨by linarith [harc.1], by linarith [harc.2]⟩
  rw [norm_fdBoundary_sub_rho_arc H harc,
    Real.abs_sin_eq_sin_abs_of_abs_le_pi (by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 12)]
      nlinarith [Real.pi_pos, habs2]),
    abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 12)]
  have hmono : Real.sin (δ * (Real.pi / 12)) < Real.sin (|t - 3| * (Real.pi / 12)) := by
    refine Real.strictMonoOn_sin ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
      ⟨by nlinarith [Real.pi_pos, abs_nonneg (t - 3)], by nlinarith [Real.pi_pos]⟩ ?_
    exact mul_lt_mul_of_pos_right hfar (by positivity)
  linarith

/-- Near the corner along the arc, the chord distance is at most the excision chord. -/
private lemma norm_fdBoundary_sub_rho_arc_le_of_near (harc : t ∈ Icc (1 : ℝ) 3)
    (hd1 : δ < 1) (hnear : |t - 3| ≤ δ) :
    ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ ≤ 2 * Real.sin (δ * (Real.pi / 12)) := by
  have habs1 : |t - 3| ≤ 1 := hnear.trans hd1.le
  have hd0 : 0 ≤ δ := (abs_nonneg _).trans hnear
  rw [norm_fdBoundary_sub_rho_arc H harc,
    Real.abs_sin_eq_sin_abs_of_abs_le_pi (by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 12)]
      nlinarith [Real.pi_pos, habs1]),
    abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 12)]
  have hmono : Real.sin (|t - 3| * (Real.pi / 12)) ≤ Real.sin (δ * (Real.pi / 12)) := by
    refine Real.strictMonoOn_sin.monotoneOn
      ⟨by nlinarith [Real.pi_pos, abs_nonneg (t - 3)], by nlinarith [Real.pi_pos]⟩
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩ ?_
    exact mul_le_mul_of_nonneg_right hnear (by positivity)
  linarith

/-- Left of the excised corner, the contour keeps distance more than `ε` from `ρ`. -/
private lemma lt_norm_of_far_left_rho (hε₁ : ε < 1) (hd : 0 < δ) (hd1 : δ < 1)
    (h2sin : 2 * Real.sin (δ * (Real.pi / 12)) = ε) (ht : t ∈ Ico (0 : ℝ) (3 - δ)) :
    ε < ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ := by
  rcases le_or_gt t 1 with ht1 | ht1
  · calc ε < 1 := hε₁
      _ ≤ ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ :=
        norm_fdBoundary_sub_rho_segment1 H ⟨ht.1, ht1⟩
  · rw [← h2sin]
    refine lt_norm_fdBoundary_sub_rho_arc_of_far ⟨ht1.le, by linarith [ht.2]⟩ hd hd1 ?_
    rw [abs_sub_comm, abs_of_pos (by linarith [ht.2] : (0 : ℝ) < 3 - t)]
    linarith [ht.2]

/-- Right of the excised corner, the contour keeps distance more than `ε` from `ρ`. -/
private lemma lt_norm_of_far_right_rho (hH : Real.sqrt 3 / 2 < H) (hεH : ε < H - Real.sqrt 3 / 2)
    (hd : 0 < δ) (hlin : δ * (H - Real.sqrt 3 / 2) = ε) (ht : t ∈ Ioc (3 + δ : ℝ) 5) :
    ε < ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ := by
  rcases le_or_gt t 4 with ht4 | ht4
  · rw [fdBoundary_sub_rho_of_mem_Icc_three_four H ⟨by linarith [ht.1], ht4⟩, ← hlin,
      norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by nlinarith [ht.1] : (0 : ℝ) ≤ (t - 3) * (H - Real.sqrt 3 / 2))]
    have := mul_lt_mul_of_pos_right (by linarith [ht.1] : δ < t - 3) (by linarith :
      (0 : ℝ) < H - Real.sqrt 3 / 2)
    linarith
  · calc ε < H - Real.sqrt 3 / 2 := hεH
      _ ≤ ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ :=
        (le_abs_self _).trans (norm_fdBoundary_sub_rho_segment5 (H := H) ⟨ht4.le, ht.2⟩)

/-- Over the excised corner, the contour stays within distance `ε` of `ρ`. -/
private lemma norm_le_of_near_rho {δL δR : ℝ} (hH : Real.sqrt 3 / 2 < H) (hδL : 0 ≤ δL)
    (hδL1 : δL < 1) (h2sin : 2 * Real.sin (δL * (Real.pi / 12)) = ε)
    (hδR1 : δR ≤ 1) (hlin : δR * (H - Real.sqrt 3 / 2) = ε)
    (ht : t ∈ Icc (3 - δL : ℝ) (3 + δR)) :
    ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ ≤ ε := by
  rcases le_or_gt t 3 with h3 | h3
  · rw [← h2sin]
    refine norm_fdBoundary_sub_rho_arc_le_of_near ⟨by linarith [ht.1], h3⟩ hδL1
      (abs_le.mpr ⟨by linarith [ht.1], by linarith⟩)
  · rw [fdBoundary_sub_rho_of_mem_Icc_three_four H ⟨h3.le, by linarith [ht.2]⟩,
      norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by nlinarith [h3] : (0 : ℝ) ≤ (t - 3) * (H - Real.sqrt 3 / 2)), ← hlin]
    exact mul_le_mul_of_nonneg_right (by linarith [ht.2]) (by linarith)

/-- **The excision collapse at `ρ`**: for small `ε`, the `ε`-excised index integrand of
the boundary contour about `ρ` is interval integrable, and its integral is exactly
`-πi/3 - arcsin(ε/2)·i` — the telescope value at the matched asymmetric half-widths. -/
private lemma truncated_integral_spec_rho (hH : Real.sqrt 3 / 2 < H) (hε : 0 < ε)
    (hε₁ : ε < 1) (hεH : ε < H - Real.sqrt 3 / 2)
    (hε₃ : ε < 2 * Real.sin (Real.pi / 12)) :
    IntervalIntegrable (fun t ↦ if ε < ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖
        then (fdBoundary H t - (UpperHalfPlane.ρ : ℂ))⁻¹ * deriv (fdBoundary H) t else 0)
      volume 0 5 ∧
    ∫ t in (0 : ℝ)..5, (if ε < ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖
        then (fdBoundary H t - (UpperHalfPlane.ρ : ℂ))⁻¹ * deriv (fdBoundary H) t else 0) =
      -((Real.pi : ℂ) / 3) * Complex.I - ((Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I := by
  obtain ⟨hδL_pos, hδL_lt, h2sin⟩ :=
    fdBoundaryArcExcisionHalfWidth_pos_and_lt_one_and_two_mul_sin_eq hε hε₃
  set δL := fdBoundaryArcExcisionHalfWidth ε with hδL_def
  have hHpos : (0 : ℝ) < H - Real.sqrt 3 / 2 := by linarith
  set δR := ε / (H - Real.sqrt 3 / 2) with hδR_def
  have hδR_pos : 0 < δR := div_pos hε hHpos
  have hδR_le : δR ≤ 1 := (div_le_one hHpos).2 hεH.le
  have hlin : δR * (H - Real.sqrt 3 / 2) = ε := div_mul_cancel₀ ε hHpos.ne'
  obtain ⟨hi_left, hi_right, hval⟩ :=
    ftc_logDeriv_telescope_rho H hH hδL_pos hδL_lt hδR_pos hδR_le
  have hae_left := Contour.ae_logDeriv_sub_eq_truncated (γ := fdBoundary H)
    (z₀ := (UpperHalfPlane.ρ : ℂ)) (a := (0 : ℝ)) (b := 3 - δL) (by linarith)
    fun s hs ↦ lt_norm_of_far_left_rho hε₁ hδL_pos hδL_lt h2sin ⟨hs.1.le, hs.2⟩
  have hae_right := Contour.ae_logDeriv_sub_eq_truncated (γ := fdBoundary H)
    (z₀ := (UpperHalfPlane.ρ : ℂ)) (a := (3 + δR : ℝ)) (b := 5) (by linarith)
    fun s hs ↦ lt_norm_of_far_right_rho hH hεH hδR_pos hlin ⟨hs.1, hs.2.le⟩
  obtain ⟨himid, hmid0⟩ :=
    Contour.intervalIntegrable_truncated_and_integral_truncated_eq_zero_of_norm_le
      (Filter.Eventually.of_forall fun s hs =>
        norm_le_of_near_rho hH hδL_pos.le hδL_lt h2sin hδR_le hlin
        (Set.Ioc_subset_Icc_self
          (by rwa [Set.uIoc_of_le (by linarith : (3 - δL : ℝ) ≤ 3 + δR)] at hs)))
  have hi02 := hi_left.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr hae_left)
  have hi25 := hi_right.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr hae_right)
  refine ⟨(hi02.trans himid).trans hi25, ?_⟩
  have hδ12 : δL * (Real.pi / 12) = Real.arcsin (ε / 2) := by
    simp only [hδL_def, fdBoundaryArcExcisionHalfWidth_def]
    field_simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi02.trans himid) hi25,
    ← intervalIntegral.integral_add_adjacent_intervals hi02 himid,
    hmid0, add_zero,
    ← intervalIntegral.integral_congr_ae hae_left,
    ← intervalIntegral.integral_congr_ae hae_right,
    hval, log_fdBoundary_three_sub_sub_rho H hδL_pos (hδL_lt.le.trans one_le_two),
    log_fdBoundary_three_add_sub_rho hH hδR_pos hδR_le, h2sin, hlin, hδ12]
  push_cast
  ring

/-- **The principal value at `ρ`**: the Cauchy principal value of the index integrand of
the boundary contour about the corner `ρ` is `-πi/3` — the corner's angle defect. -/
theorem hasCauchyPVAt_fdBoundary_rho (hH : Real.sqrt 3 / 2 < H) :
    Contour.HasCauchyPVAt (fdBoundary H) 0 5
      (fun z ↦ (z - (UpperHalfPlane.ρ : ℂ))⁻¹) (UpperHalfPlane.ρ : ℂ)
      (-((Real.pi : ℂ) / 3) * Complex.I) := by
  have hsin12 : 0 < 2 * Real.sin (Real.pi / 12) := by
    have := Real.sin_pos_of_pos_of_lt_pi (x := Real.pi / 12) (by positivity)
      (by linarith [Real.pi_pos])
    linarith
  have hε₀ : 0 < min (min (1 : ℝ) (H - Real.sqrt 3 / 2)) (2 * Real.sin (Real.pi / 12)) :=
    lt_min (lt_min (by norm_num) (by linarith)) hsin12
  have hIoo : Ioo (0 : ℝ)
      (min (min (1 : ℝ) (H - Real.sqrt 3 / 2)) (2 * Real.sin (Real.pi / 12))) ∈
      𝓝[>] (0 : ℝ) := by
    rw [← Ioi_inter_Iio]
    exact inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hε₀))
  have hspec : ∀ ε ∈ Ioo (0 : ℝ)
      (min (min (1 : ℝ) (H - Real.sqrt 3 / 2)) (2 * Real.sin (Real.pi / 12))),
      IntervalIntegrable (fun t ↦ if ε < ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖
          then (fdBoundary H t - (UpperHalfPlane.ρ : ℂ))⁻¹ * deriv (fdBoundary H) t
          else 0)
        volume 0 5 ∧
      ∫ t in (0 : ℝ)..5, (if ε < ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖
          then (fdBoundary H t - (UpperHalfPlane.ρ : ℂ))⁻¹ * deriv (fdBoundary H) t
          else 0) =
        -((Real.pi : ℂ) / 3) * Complex.I - ((Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I :=
    fun ε hε ↦ truncated_integral_spec_rho hH hε.1
      (hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
      (hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
      (hε.2.trans_le (min_le_right _ _))
  have hcont : Tendsto (fun ε : ℝ ↦ -((Real.pi : ℂ) / 3) * Complex.I -
      ((Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I) (𝓝[>] 0)
      (𝓝 (-((Real.pi : ℂ) / 3) * Complex.I)) := by
    have hc : Continuous fun ε : ℝ ↦ -((Real.pi : ℂ) / 3) * Complex.I -
        ((Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I := by
      refine continuous_const.sub ((Complex.continuous_ofReal.comp ?_).mul continuous_const)
      exact Real.continuous_arcsin.comp (continuous_id.div_const 2)
    simpa [Real.arcsin_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine Contour.hasCauchyPVAt_iff.mpr ⟨?_, ?_⟩
  · filter_upwards [hIoo] with ε hε
    exact (hspec ε hε).1
  · refine Tendsto.congr' ?_ hcont
    filter_upwards [hIoo] with ε hε
    exact ((hspec ε hε).2).symm

/-- **The winding number of the boundary contour at `ρ` is `-1/6`**: the corner `ρ`
sits on the contour with interior angle `π/3`, and the principal-value normalization
sees exactly that angle as a clockwise turn, giving `-(π/3) / (2π) = -1/6`. -/
@[simp]
theorem windingNumber_fdBoundary_rho (hH : Real.sqrt 3 / 2 < H) :
    Contour.windingNumber (fdBoundary H) 0 5 (UpperHalfPlane.ρ : ℂ) = -(1 / 6 : ℂ) := by
  rw [Contour.windingNumber_eq_of_hasCauchyPVAt (hasCauchyPVAt_fdBoundary_rho hH)]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

end ModularForm

end TauCeti

end
