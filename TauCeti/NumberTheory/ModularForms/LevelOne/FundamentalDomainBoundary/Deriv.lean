/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic

import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Derivatives of the fundamental-domain boundary contour

Each segment of `fdBoundary` differentiates in closed form — the verticals and the
horizontal to their constant chords, the arcs to the arc speed times the rotated tangent —
and away from the segment-junction parameters the contour itself differentiates like its
active segment. These are the `γ'` factors of the valence-formula contour integrals.

## Main declarations

* `TauCeti.ModularForm.hasDerivAt_fdBoundary_segment1` … `_segment5`: the closed-form
  segment derivatives.
* `TauCeti.ModularForm.hasDerivAt_fdBoundary_of_lt_one` … `_of_gt_four`: the contour
  differentiates like its active segment between the breakpoints, with the two arcs
  unified across their smooth junction (`hasDerivAt_fdBoundary_of_mem_Ioo_one_three`).

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development this file ports onto the current Mathlib pin.
-/

public noncomputable section

open Complex UpperHalfPlane

open scoped Real

namespace TauCeti

namespace ModularForm

section Segments

/-- Segment 1 differentiates to its constant chord. -/
lemma hasDerivAt_fdBoundary_segment1 (H t : ℝ) :
    HasDerivAt (fdBoundary_segment1 H) ((ρ : ℂ) + 1 - (1 / 2 + H * Complex.I)) t :=
  (AffineMap.hasDerivAt_lineMap).congr_of_eventuallyEq <|
    Filter.Eventually.of_forall fun s ↦ by rw [fdBoundary_segment1_apply]

/-- Segment 2 differentiates to the arc speed times the rotated tangent. -/
lemma hasDerivAt_fdBoundary_segment2 (t : ℝ) :
    HasDerivAt fdBoundary_segment2
      ((Real.pi / 2 - Real.pi / 3) •
        (circleMap 0 1 (Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * Complex.I))
      t := by
  have hθ : HasDerivAt (fun s : ℝ ↦ Real.pi / 3 + (s - 1) * (Real.pi / 2 - Real.pi / 3))
      (Real.pi / 2 - Real.pi / 3) t := by
    simpa using
      (((hasDerivAt_id t).sub_const 1).mul_const (Real.pi / 2 - Real.pi / 3)).const_add
        (Real.pi / 3)
  exact (HasDerivAt.scomp_of_eq (x := t)
    (hg := hasDerivAt_circleMap 0 1 (Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)))
    (hh := hθ) (hy := rfl)).congr_of_eventuallyEq <|
    Filter.Eventually.of_forall fun s ↦ by rw [fdBoundary_segment2_apply]; rfl

/-- Segment 3 differentiates to the arc speed times the rotated tangent. -/
lemma hasDerivAt_fdBoundary_segment3 (t : ℝ) :
    HasDerivAt fdBoundary_segment3
      ((2 * Real.pi / 3 - Real.pi / 2) •
        (circleMap 0 1 (Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) *
          Complex.I)) t := by
  have hθ : HasDerivAt (fun s : ℝ ↦ Real.pi / 2 + (s - 2) * (2 * Real.pi / 3 - Real.pi / 2))
      (2 * Real.pi / 3 - Real.pi / 2) t := by
    simpa using
      (((hasDerivAt_id t).sub_const 2).mul_const (2 * Real.pi / 3 - Real.pi / 2)).const_add
        (Real.pi / 2)
  exact (HasDerivAt.scomp_of_eq (x := t)
    (hg := hasDerivAt_circleMap 0 1 (Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)))
    (hh := hθ) (hy := rfl)).congr_of_eventuallyEq <|
    Filter.Eventually.of_forall fun s ↦ by rw [fdBoundary_segment3_apply]; rfl

/-- Segment 4 differentiates to its constant chord. -/
lemma hasDerivAt_fdBoundary_segment4 (H t : ℝ) :
    HasDerivAt (fdBoundary_segment4 H) (-1 / 2 + H * Complex.I - (ρ : ℂ)) t := by
  have h := HasDerivAt.scomp_of_eq (x := t)
    (hg := AffineMap.hasDerivAt_lineMap (a := (ρ : ℂ)) (b := -1 / 2 + H * Complex.I))
    (hh := (hasDerivAt_id t).sub_const 3) (hy := rfl)
  simp only [one_smul] at h
  exact h.congr_of_eventuallyEq <| Filter.Eventually.of_forall fun s ↦ by
    rw [fdBoundary_segment4_apply]
    rfl

/-- Segment 5 differentiates to its constant chord, the unit horizontal. -/
lemma hasDerivAt_fdBoundary_segment5 (H t : ℝ) :
    HasDerivAt (fdBoundary_segment5 H) (1 : ℂ) t := by
  have h := HasDerivAt.scomp_of_eq (x := t)
    (hg := AffineMap.hasDerivAt_lineMap (a := (-1 / 2 + H * Complex.I : ℂ))
      (b := 1 / 2 + H * Complex.I))
    (hh := (hasDerivAt_id t).sub_const 4) (hy := rfl)
  simp only [one_smul] at h
  have hchord : (1 / 2 + H * Complex.I : ℂ) - (-1 / 2 + H * Complex.I) = 1 := by ring
  rw [hchord] at h
  exact h.congr_of_eventuallyEq <| Filter.Eventually.of_forall fun s ↦ by
    rw [fdBoundary_segment5_apply]
    rfl

end Segments

section SegmentDerivRewrites

/-- Segment 1's derivative, in rewrite form. -/
@[simp]
lemma deriv_fdBoundary_segment1 (H t : ℝ) :
    deriv (fdBoundary_segment1 H) t = (ρ : ℂ) + 1 - (1 / 2 + H * Complex.I) :=
  (hasDerivAt_fdBoundary_segment1 H t).deriv

/-- Segment 2's derivative, in rewrite form. -/
@[simp]
lemma deriv_fdBoundary_segment2 (t : ℝ) :
    deriv fdBoundary_segment2 t =
      (Real.pi / 2 - Real.pi / 3) •
        (circleMap 0 1 (Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * Complex.I) :=
  (hasDerivAt_fdBoundary_segment2 t).deriv

/-- Segment 3's derivative, in rewrite form. -/
@[simp]
lemma deriv_fdBoundary_segment3 (t : ℝ) :
    deriv fdBoundary_segment3 t =
      (2 * Real.pi / 3 - Real.pi / 2) •
        (circleMap 0 1 (Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) *
          Complex.I) :=
  (hasDerivAt_fdBoundary_segment3 t).deriv

/-- Segment 4's derivative, in rewrite form. -/
@[simp]
lemma deriv_fdBoundary_segment4 (H t : ℝ) :
    deriv (fdBoundary_segment4 H) t = -1 / 2 + H * Complex.I - (ρ : ℂ) :=
  (hasDerivAt_fdBoundary_segment4 H t).deriv

/-- Segment 5's derivative, in rewrite form. -/
@[simp]
lemma deriv_fdBoundary_segment5 (H t : ℝ) : deriv (fdBoundary_segment5 H) t = 1 :=
  (hasDerivAt_fdBoundary_segment5 H t).deriv

end SegmentDerivRewrites

section Contour

variable {H t : ℝ}

/-- Below the first breakpoint the contour differentiates like segment 1. -/
lemma hasDerivAt_fdBoundary_of_lt_one (ht : t < 1) :
    HasDerivAt (fdBoundary H) ((ρ : ℂ) + 1 - (1 / 2 + H * Complex.I)) t :=
  (hasDerivAt_fdBoundary_segment1 H t).congr_of_eventuallyEq <| by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact fdBoundary_of_le_one hs.le

/-- Strictly between the first and third breakpoints — across the smooth junction at
`t = 2`, where the two arc segments continue the same circle parameterization — the
contour differentiates like the unified arc of angle `(t + 1)·π/6`. -/
lemma hasDerivAt_fdBoundary_of_mem_Ioo_one_three (ht : t ∈ Set.Ioo (1 : ℝ) 3) :
    HasDerivAt (fdBoundary H)
      ((Real.pi / 6) • (circleMap 0 1 ((t + 1) * (Real.pi / 6)) * Complex.I)) t := by
  have hθ : HasDerivAt (fun s : ℝ ↦ (s + 1) * (Real.pi / 6)) (Real.pi / 6) t := by
    simpa using ((hasDerivAt_id t).add_const 1).mul_const (Real.pi / 6)
  have h_arc := HasDerivAt.scomp_of_eq (x := t)
    (hg := hasDerivAt_circleMap 0 1 ((t + 1) * (Real.pi / 6))) (hh := hθ) (hy := rfl)
  refine h_arc.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact eqOn_fdBoundary_arc H ⟨hs.1.le, hs.2.le⟩

/-- Strictly between the third and fourth breakpoints the contour differentiates like
segment 4. -/
lemma hasDerivAt_fdBoundary_of_mem_Ioo_three_four (ht : t ∈ Set.Ioo (3 : ℝ) 4) :
    HasDerivAt (fdBoundary H) (-1 / 2 + H * Complex.I - (ρ : ℂ)) t :=
  (hasDerivAt_fdBoundary_segment4 H t).congr_of_eventuallyEq <| by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact fdBoundary_of_le_four hs.1 hs.2.le

/-- Above the fourth breakpoint the contour differentiates like segment 5. -/
lemma hasDerivAt_fdBoundary_of_gt_four (ht : 4 < t) :
    HasDerivAt (fdBoundary H) (1 : ℂ) t :=
  (hasDerivAt_fdBoundary_segment5 H t).congr_of_eventuallyEq <| by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact fdBoundary_of_gt_four hs

end Contour

section DerivRewrites

/-- The derivative below the first breakpoint, in rewrite form. -/
@[simp]
lemma deriv_fdBoundary_of_lt_one (ht : t < 1) :
    deriv (fdBoundary H) t = (ρ : ℂ) + 1 - (1 / 2 + H * Complex.I) :=
  (hasDerivAt_fdBoundary_of_lt_one ht).deriv

/-- The derivative on the unified arc, in rewrite form. -/
@[simp]
lemma deriv_fdBoundary_of_mem_Ioo_one_three (ht : t ∈ Set.Ioo (1 : ℝ) 3) :
    deriv (fdBoundary H) t =
      (Real.pi / 6) • (circleMap 0 1 ((t + 1) * (Real.pi / 6)) * Complex.I) :=
  (hasDerivAt_fdBoundary_of_mem_Ioo_one_three ht).deriv

/-- The derivative on the left vertical, in rewrite form. -/
@[simp]
lemma deriv_fdBoundary_of_mem_Ioo_three_four (ht : t ∈ Set.Ioo (3 : ℝ) 4) :
    deriv (fdBoundary H) t = -1 / 2 + H * Complex.I - (ρ : ℂ) :=
  (hasDerivAt_fdBoundary_of_mem_Ioo_three_four ht).deriv

/-- The derivative above the fourth breakpoint, in rewrite form. -/
@[simp]
lemma deriv_fdBoundary_of_gt_four (ht : 4 < t) : deriv (fdBoundary H) t = 1 :=
  (hasDerivAt_fdBoundary_of_gt_four ht).deriv

end DerivRewrites


end ModularForm

end TauCeti

end
