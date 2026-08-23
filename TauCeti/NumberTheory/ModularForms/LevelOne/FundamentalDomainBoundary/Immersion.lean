/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.PwC1ImmersionOn
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv

/-!
# The boundary contour is a piecewise-`C¹` immersion

Away from the three genuine corners every piece of the boundary contour has a nonvanishing
tangent: the verticals and the horizontal move with constant nonzero chords (the height
differing from the corner row keeps the verticals nondegenerate), and the unified arc moves at
constant speed `π/6`. This is the regularity that feeds the principal-value existence of
the winding decomposition and the residue sum along the contour.

## Main declarations

* `TauCeti.ModularForm.isPwC1ImmersionOn_fdBoundary`.

## References

The immersion condition is the regularity requirement of N. Hungerbühler and M. Wasem,
*Non-integer valued winding numbers and a generalized Residue Theorem*, arXiv:1808.00997
(2018); the truncated-contour strategy follows the fundamental-domain boundary development
of AINTLIB's `LeanModularForms` (`ForMathlib/FDBoundary.lean`, `FDBoundaryH.lean`,
`FDBoundaryPath.lean`).
-/

public noncomputable section

open Complex Set UpperHalfPlane TauCeti.Contour

open scoped Real

namespace TauCeti

namespace ModularForm

variable {H t c d : ℝ}

/-- The segment-1 chord is nonzero when the height differs from the corner row. -/
private lemma segment1_chord_ne_zero (hH : H ≠ Real.sqrt 3 / 2) :
    (ρ : ℂ) + 1 - (1 / 2 + H * Complex.I) ≠ 0 := by
  intro h0
  apply hH
  have him := segment1_chord_im (H := H)
  rw [h0, Complex.zero_im] at him
  linarith

private lemma arc_deriv_ne_zero (t : ℝ) :
    (Real.pi / 6) • (circleMap 0 1 ((t + 1) * (Real.pi / 6)) * Complex.I) ≠ 0 := by
  refine smul_ne_zero (by positivity) (mul_ne_zero ?_ Complex.I_ne_zero)
  exact circleMap_ne_center one_ne_zero

/-- The boundary contour is a piecewise-`C¹` immersion: every corner-free piece is `C¹`
with nonvanishing tangent. -/
theorem isPwC1ImmersionOn_fdBoundary (hH : H ≠ Real.sqrt 3 / 2) :
    IsPwC1ImmersionOn (fdBoundary H) 0 5 := by
  refine IsPwC1ImmersionOn.of_breakpoints (continuous_fdBoundary H).continuousOn
    fdBoundaryCorners ?_ ?_
  · intro x hx
    rw [Finset.mem_coe, mem_fdBoundaryCorners] at hx
    rw [min_eq_left (by norm_num : (0 : ℝ) ≤ 5), max_eq_right (by norm_num : (0 : ℝ) ≤ 5)]
    rcases hx with rfl | rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩
  · intro c d hlt hsub hdis
    have hsub' : Icc c d ⊆ Icc (0 : ℝ) 5 := by
      rwa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at hsub
    refine ⟨contDiffOn_fdBoundary H hsub' hdis, fun t ht ↦ ?_⟩
    have h_uniq : UniqueDiffWithinAt ℝ (Icc c d) t := uniqueDiffOn_Icc hlt t ht
    rcases subset_piece_of_disjoint_corners hsub' hdis with h | h | h | h
    · rw [derivWithin_congr (fun s hs ↦ eqOn_fdBoundarySegment1 H (h hs))
        (eqOn_fdBoundarySegment1 H (h ht)),
        (hasDerivAt_fdBoundarySegment1 H t).hasDerivWithinAt.derivWithin h_uniq]
      exact segment1_chord_ne_zero hH
    · rw [(hasDerivWithinAt_fdBoundary_arc (h ⟨le_rfl, hlt.le⟩).1
        (h ⟨hlt.le, le_rfl⟩).2 ht).derivWithin h_uniq]
      exact arc_deriv_ne_zero t
    · have hchord : (-1 / 2 : ℂ) + H * Complex.I - (ρ : ℂ) =
          -((ρ : ℂ) + 1 - (1 / 2 + H * Complex.I)) := by ring
      rw [derivWithin_congr (fun s hs ↦ eqOn_fdBoundarySegment4 H (h hs))
        (eqOn_fdBoundarySegment4 H (h ht)),
        (hasDerivAt_fdBoundarySegment4 H t).hasDerivWithinAt.derivWithin h_uniq, hchord]
      exact neg_ne_zero.mpr (segment1_chord_ne_zero hH)
    · rw [derivWithin_congr (fun s hs ↦ eqOn_fdBoundarySegment5 H (h hs))
        (eqOn_fdBoundarySegment5 H (h ht)),
        (hasDerivAt_fdBoundarySegment5 H t).hasDerivWithinAt.derivWithin h_uniq]
      exact one_ne_zero

end ModularForm

end TauCeti

end
