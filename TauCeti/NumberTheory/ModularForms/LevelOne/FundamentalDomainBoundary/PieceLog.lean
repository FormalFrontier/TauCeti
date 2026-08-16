/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic

import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.Contour.LogDerivFTC
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv

/-!
# The winding number of each boundary piece is a principal logarithm

Each smooth piece of the boundary contour of the truncated fundamental domain is confined
to an axis-aligned half-plane: the verticals have constant real part `±1/2`, the arc stays
below height `1`, and the truncation ceiling has constant height `H`. About a point `w` on
the far side of the corresponding line, the chord ratios of the piece therefore lie in the
slit plane, so its index integral is a principal logarithm of the endpoint ratio and the
winding number of the piece is `(2πi)⁻¹` times that logarithm.

Summing the four values over the piece decomposition and pinning with integrality is how
the interior winding number `-1` of the contour is computed.

## Main declarations

* `TauCeti.ModularForm.windingNumber_fdBoundarySegment1_eq_log`,
  `TauCeti.ModularForm.windingNumber_fdBoundary_arc_eq_log`,
  `TauCeti.ModularForm.windingNumber_fdBoundarySegment4_eq_log` and
  `TauCeti.ModularForm.windingNumber_fdBoundarySegment5_eq_log` — the four logarithm values.

## References

The piece-logarithm evaluation follows the fundamental-domain boundary development of
AINTLIB's `LeanModularForms` (`ForMathlib/FDBoundary.lean`, `FDBoundaryH.lean`,
`FDBoundaryPath.lean`); the logarithm FTC and the slit-plane criteria are Tau Ceti's.
-/

public section

open Set TauCeti.Contour UpperHalfPlane

namespace TauCeti

namespace ModularForm

variable {H t : ℝ} {w : ℂ}

/-- The shared piece-evaluation skeleton: on a subinterval where the boundary path avoids
`w` and its chord ratios stay in the slit plane, the winding number is the principal
logarithm of the endpoint ratio. -/
private lemma windingNumber_fdBoundary_eq_log_of_slit {a b : ℝ} (hab : a ≤ b)
    (hsub : Icc a b ⊆ Icc (0 : ℝ) 5)
    (h_diff : ∀ s ∈ Ioo a b, DifferentiableAt ℝ (fdBoundary H) s)
    (h_avoid : ∀ t ∈ uIcc a b, fdBoundary H t ≠ w)
    (h_slit : ∀ t ∈ uIcc a b,
      (fdBoundary H t - w) / (fdBoundary H a - w) ∈ Complex.slitPlane) :
    windingNumber (fdBoundary H) a b w =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        Complex.log ((fdBoundary H b - w) / (fdBoundary H a - w)) := by
  have h_int := intervalIntegrable_inv_sub_mul_deriv (continuous_fdBoundary H).continuousOn
    h_avoid ((isPiecewiseC1On_fdBoundary H).intervalIntegrable_deriv.mono_set
      (by rw [uIcc_of_le hab, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]; exact hsub))
  have h_diff' : ∀ s ∈ Ioo (min a b) (max a b) \ (∅ : Set ℝ),
      DifferentiableAt ℝ (fdBoundary H) s := by
    intro s hs
    rw [sdiff_empty, min_eq_left hab, max_eq_right hab] at hs
    exact h_diff s hs
  rw [windingNumber_eq_integral_of_avoidance (continuous_fdBoundary H).continuousOn
      h_avoid h_int,
    integral_inv_sub_mul_deriv_eq_log countable_empty (continuous_fdBoundary H).continuousOn
      h_diff' h_slit h_int]

/-- The winding number of the right vertical about a point strictly to its left is the
principal logarithm of the endpoint ratio. -/
theorem windingNumber_fdBoundarySegment1_eq_log (hw : w.re < 1 / 2) :
    windingNumber (fdBoundary H) 0 1 w =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        Complex.log (((ρ : ℂ) + 1 - w) / (1 / 2 + H * Complex.I - w)) := by
  have h01 : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le (by norm_num)
  have hre : ∀ t ∈ uIcc (0 : ℝ) 1, 0 < (fdBoundary H t - w).re := fun t ht => by
    rw [Complex.sub_re, re_fdBoundarySegment1 H (h01 ▸ ht)]
    linarith
  rw [windingNumber_fdBoundary_eq_log_of_slit (by norm_num)
      (by rw [← h01]; exact h01 ▸ Icc_subset_Icc le_rfl (by norm_num))
      (fun s hs => (hasDerivAt_fdBoundary_of_lt_one hs.2).differentiableAt)
      (fun t ht h_eq => absurd (hre t ht) (by simp [h_eq]))
      (fun t ht => div_mem_slitPlane_of_re_pos (hre 0 left_mem_uIcc) (hre t ht)),
    fdBoundary_apply_one, fdBoundary_apply_zero]

/-- The winding number of the arc about a point strictly above height `1` is the principal
logarithm of the endpoint ratio. -/
theorem windingNumber_fdBoundary_arc_eq_log (hw : 1 < w.im) :
    windingNumber (fdBoundary H) 1 3 w =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        Complex.log (((ρ : ℂ) - w) / ((ρ : ℂ) + 1 - w)) := by
  have h13 : uIcc (1 : ℝ) 3 = Icc 1 3 := uIcc_of_le (by norm_num)
  have him : ∀ t ∈ uIcc (1 : ℝ) 3, (fdBoundary H t - w).im < 0 := fun t ht => by
    have := im_fdBoundary_arc_le H (h13 ▸ ht)
    rw [Complex.sub_im]
    linarith
  rw [windingNumber_fdBoundary_eq_log_of_slit (by norm_num)
      (Icc_subset_Icc (by norm_num) (by norm_num))
      (fun s hs => (hasDerivAt_fdBoundary_of_mem_Ioo_one_three hs).differentiableAt)
      (fun t ht h_eq => absurd (him t ht) (by simp [h_eq]))
      (fun t ht => div_mem_slitPlane_of_im_neg (him 1 left_mem_uIcc) (him t ht)),
    fdBoundary_apply_three, fdBoundary_apply_one]

/-- The winding number of the left vertical about a point strictly to its right is the
principal logarithm of the endpoint ratio. -/
theorem windingNumber_fdBoundarySegment4_eq_log (hw : -(1 / 2) < w.re) :
    windingNumber (fdBoundary H) 3 4 w =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        Complex.log ((-1 / 2 + H * Complex.I - w) / ((ρ : ℂ) - w)) := by
  have h34 : uIcc (3 : ℝ) 4 = Icc 3 4 := uIcc_of_le (by norm_num)
  have hre : ∀ t ∈ uIcc (3 : ℝ) 4, (fdBoundary H t - w).re < 0 := fun t ht => by
    rw [Complex.sub_re, re_fdBoundarySegment4 H (h34 ▸ ht)]
    linarith
  rw [windingNumber_fdBoundary_eq_log_of_slit (by norm_num)
      (Icc_subset_Icc (by norm_num) (by norm_num))
      (fun s hs => (hasDerivAt_fdBoundary_of_mem_Ioo_three_four hs).differentiableAt)
      (fun t ht h_eq => absurd (hre t ht) (by simp [h_eq]))
      (fun t ht => div_mem_slitPlane_of_re_neg (hre 3 left_mem_uIcc) (hre t ht)),
    fdBoundary_apply_four, fdBoundary_apply_three]

/-- The winding number of the truncation ceiling about a point strictly below height `H` is
the principal logarithm of the endpoint ratio. -/
theorem windingNumber_fdBoundarySegment5_eq_log (hw : w.im < H) :
    windingNumber (fdBoundary H) 4 5 w =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        Complex.log ((1 / 2 + H * Complex.I - w) / (-1 / 2 + H * Complex.I - w)) := by
  have h45 : uIcc (4 : ℝ) 5 = Icc 4 5 := uIcc_of_le (by norm_num)
  have him : ∀ t ∈ uIcc (4 : ℝ) 5, 0 < (fdBoundary H t - w).im := fun t ht => by
    rw [Complex.sub_im, im_fdBoundarySegment5 H (h45 ▸ ht)]
    linarith
  rw [windingNumber_fdBoundary_eq_log_of_slit (by norm_num)
      (Icc_subset_Icc (by norm_num) le_rfl)
      (fun s hs => (hasDerivAt_fdBoundary_of_gt_four hs.1).differentiableAt)
      (fun t ht h_eq => absurd (him t ht) (by simp [h_eq]))
      (fun t ht => div_mem_slitPlane_of_im_pos (him 4 left_mem_uIcc) (him t ht)),
    fdBoundary_apply_five, fdBoundary_apply_four]

end ModularForm

end TauCeti

end
