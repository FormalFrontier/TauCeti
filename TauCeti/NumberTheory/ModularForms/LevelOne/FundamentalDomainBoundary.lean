/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# The boundary contour of the standard fundamental domain

The raw five-segment path family `fdBoundary H`, parameterized over `[0, 5]` at a height
parameter `H`: the right vertical from `1/2 + H·i` through `ρ + 1`, the unit-circle arcs
from `ρ + 1` to `i` and from `i` to `ρ`, the left vertical from `ρ` through `-1/2 + H·i`,
and the closing top horizontal. For `1 < H` — so that the horizontal sits above the arc,
whose highest point is `i` — this is the boundary of the standard fundamental domain
truncated at height `H`; the definitions carry no hypothesis, and the boundary reading is
invoked with that bound downstream. The corner values and closedness recorded here are the
anchors of the valence-formula contour.

## Main declarations

* `TauCeti.ModularForm.fdBoundary` (with the segments `fdBoundary_segment1` … `fdBoundary_segment5`,
  built from `AffineMap.lineMap` and `circleMap`).
* `TauCeti.ModularForm.fdBoundary_apply_three`: the parameter `3` lands on `ρ`.
* `TauCeti.ModularForm.fdBoundary_closed`: the contour is closed.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development this file ports onto the current Mathlib pin.
-/

public noncomputable section

open Complex UpperHalfPlane

open scoped Real

namespace TauCeti

namespace ModularForm

/-- Segment 1: the right vertical from `1/2 + H·i` through `ρ + 1`, over `t ∈ [0, 1]`. -/
def fdBoundary_segment1 (H : ℝ) : ℝ → ℂ := fun t ↦
  AffineMap.lineMap (1 / 2 + H * Complex.I) ((ρ : ℂ) + 1) t

/-- Segment 2: the unit-circle arc from `ρ + 1` to `i` (angle `π/3 → π/2`), over
`t ∈ [1, 2]`. -/
def fdBoundary_segment2 : ℝ → ℂ := fun t ↦
  circleMap 0 1 (Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3))

/-- Segment 3: the unit-circle arc from `i` to `ρ` (angle `π/2 → 2π/3`), over
`t ∈ [2, 3]`. -/
def fdBoundary_segment3 : ℝ → ℂ := fun t ↦
  circleMap 0 1 (Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2))

/-- Segment 4: the left vertical from `ρ` through `-1/2 + H·i`, over `t ∈ [3, 4]`. -/
def fdBoundary_segment4 (H : ℝ) : ℝ → ℂ := fun t ↦
  AffineMap.lineMap (ρ : ℂ) (-1 / 2 + H * Complex.I) (t - 3)

/-- Segment 5: the top horizontal from `-1/2 + H·i` to `1/2 + H·i`, over `t ∈ [4, 5]`. -/
def fdBoundary_segment5 (H : ℝ) : ℝ → ℂ := fun t ↦
  AffineMap.lineMap (-1 / 2 + H * Complex.I) (1 / 2 + H * Complex.I) (t - 4)



section SegmentApply

/-!
The five characteristic evaluation lemmas: the segment definitions are sealed by the module
system, and these equations are the supported cross-module rewrites. They are deliberately
not `@[simp]`: the endpoint values `fdBoundary_segment*_apply_*` below are the `simp` normal
forms, and a general unfolding rule would reduce their left-hand sides past them (the arc
endpoints do not `simp`-evaluate from `circleMap`).
-/

/-- Segment 1 evaluated: the line from `1/2 + H·i` to `ρ + 1`. -/
lemma fdBoundary_segment1_apply (H t : ℝ) :
    fdBoundary_segment1 H t = AffineMap.lineMap (1 / 2 + H * Complex.I) ((ρ : ℂ) + 1) t := by
  unfold fdBoundary_segment1
  rfl

/-- Segment 2 evaluated: the unit-circle arc at angle `π/3 + (t - 1)·(π/2 - π/3)`. -/
lemma fdBoundary_segment2_apply (t : ℝ) :
    fdBoundary_segment2 t =
      circleMap 0 1 (Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) := by
  unfold fdBoundary_segment2
  rfl

/-- Segment 3 evaluated: the unit-circle arc at angle `π/2 + (t - 2)·(2π/3 - π/2)`. -/
lemma fdBoundary_segment3_apply (t : ℝ) :
    fdBoundary_segment3 t =
      circleMap 0 1 (Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) := by
  unfold fdBoundary_segment3
  rfl

/-- Segment 4 evaluated: the line from `ρ` to `-1/2 + H·i` at parameter `t - 3`. -/
lemma fdBoundary_segment4_apply (H t : ℝ) :
    fdBoundary_segment4 H t = AffineMap.lineMap (ρ : ℂ) (-1 / 2 + H * Complex.I) (t - 3) := by
  unfold fdBoundary_segment4
  rfl

/-- Segment 5 evaluated: the line from `-1/2 + H·i` to `1/2 + H·i` at parameter `t - 4`. -/
lemma fdBoundary_segment5_apply (H t : ℝ) :
    fdBoundary_segment5 H t =
      AffineMap.lineMap (-1 / 2 + H * Complex.I) (1 / 2 + H * Complex.I) (t - 4) := by
  unfold fdBoundary_segment5
  rfl

end SegmentApply

section SegmentEndpoints

/-- Segment 1 starts at the top right corner `1/2 + H·i`. -/
@[simp]
lemma fdBoundary_segment1_apply_zero (H : ℝ) : fdBoundary_segment1 H 0 = 1 / 2 + H * Complex.I := by
  rw [fdBoundary_segment1_apply, AffineMap.lineMap_apply_zero]

/-- Segment 1 ends at the corner `ρ + 1`. -/
@[simp]
lemma fdBoundary_segment1_apply_one (H : ℝ) : fdBoundary_segment1 H 1 = (ρ : ℂ) + 1 := by
  rw [fdBoundary_segment1_apply, AffineMap.lineMap_apply_one]

/-- Segment 2 starts at the corner `ρ + 1`. -/
@[simp]
lemma fdBoundary_segment2_apply_one : fdBoundary_segment2 1 = (ρ : ℂ) + 1 := by
  have hangle : Real.pi / 3 + ((1 : ℝ) - 1) * (Real.pi / 2 - Real.pi / 3) = Real.pi / 3 := by
    ring
  rw [fdBoundary_segment2_apply, hangle]
  refine Complex.ext ?_ ?_
  · rw [circleMap_zero_re, Real.cos_pi_div_three]
    simp [ρ]
    norm_num
  · rw [circleMap_zero_im, Real.sin_pi_div_three]
    simp [ρ]

/-- Segment 2 ends at `i`. -/
@[simp]
lemma fdBoundary_segment2_apply_two : fdBoundary_segment2 2 = Complex.I := by
  have hangle : Real.pi / 3 + ((2 : ℝ) - 1) * (Real.pi / 2 - Real.pi / 3) = Real.pi / 2 := by
    ring
  rw [fdBoundary_segment2_apply, hangle, circleMap_pi_div_two]
  simp

/-- Segment 3 starts at `i`. -/
@[simp]
lemma fdBoundary_segment3_apply_two : fdBoundary_segment3 2 = Complex.I := by
  have hangle : Real.pi / 2 + ((2 : ℝ) - 2) * (2 * Real.pi / 3 - Real.pi / 2) = Real.pi / 2 := by
    ring
  rw [fdBoundary_segment3_apply, hangle, circleMap_pi_div_two]
  simp

/-- Segment 3 ends at the elliptic corner `ρ`. -/
@[simp]
lemma fdBoundary_segment3_apply_three : fdBoundary_segment3 3 = (ρ : ℂ) := by
  have hangle : Real.pi / 2 + ((3 : ℝ) - 2) * (2 * Real.pi / 3 - Real.pi / 2) =
      Real.pi - Real.pi / 3 := by ring
  rw [fdBoundary_segment3_apply, hangle]
  refine Complex.ext ?_ ?_
  · rw [circleMap_zero_re, Real.cos_pi_sub, Real.cos_pi_div_three]
    simp [ρ]
    norm_num
  · rw [circleMap_zero_im, Real.sin_pi_sub, Real.sin_pi_div_three]
    simp [ρ]

/-- Segment 4 starts at the elliptic corner `ρ`. -/
@[simp]
lemma fdBoundary_segment4_apply_three (H : ℝ) : fdBoundary_segment4 H 3 = (ρ : ℂ) := by
  have hpar : (3 : ℝ) - 3 = 0 := by norm_num
  rw [fdBoundary_segment4_apply, hpar, AffineMap.lineMap_apply_zero]

/-- Segment 4 ends at the top left corner `-1/2 + H·i`. -/
@[simp]
lemma fdBoundary_segment4_apply_four (H : ℝ) :
    fdBoundary_segment4 H 4 = -1 / 2 + H * Complex.I := by
  have hpar : (4 : ℝ) - 3 = 1 := by norm_num
  rw [fdBoundary_segment4_apply, hpar, AffineMap.lineMap_apply_one]

/-- Segment 5 starts at the top left corner `-1/2 + H·i`. -/
@[simp]
lemma fdBoundary_segment5_apply_four (H : ℝ) :
    fdBoundary_segment5 H 4 = -1 / 2 + H * Complex.I := by
  have hpar : (4 : ℝ) - 4 = 0 := by norm_num
  rw [fdBoundary_segment5_apply, hpar, AffineMap.lineMap_apply_zero]

/-- Segment 5 ends at the top right corner `1/2 + H·i`. -/
@[simp]
lemma fdBoundary_segment5_apply_five (H : ℝ) : fdBoundary_segment5 H 5 = 1 / 2 + H * Complex.I := by
  have hpar : (5 : ℝ) - 4 = 1 := by norm_num
  rw [fdBoundary_segment5_apply, hpar, AffineMap.lineMap_apply_one]

end SegmentEndpoints

/-- The raw five-segment path at height parameter `H`, parameterized over `[0, 5]` and
closed for every `H`. For `1 < H` it is the boundary of the standard fundamental domain
truncated at height `H`. -/
def fdBoundary (H : ℝ) : ℝ → ℂ := fun t ↦
  if t ≤ 1 then fdBoundary_segment1 H t
  else if t ≤ 2 then fdBoundary_segment2 t
  else if t ≤ 3 then fdBoundary_segment3 t
  else if t ≤ 4 then fdBoundary_segment4 H t
  else fdBoundary_segment5 H t

/-- The interior breakpoints of the five-segment parameterization. -/
def fdBoundaryBreakpoints : Finset ℝ := {1, 2, 3, 4}

/-- Membership in the breakpoints is being one of the four interior corners. -/
@[simp]
lemma mem_fdBoundaryBreakpoints {t : ℝ} :
    t ∈ fdBoundaryBreakpoints ↔ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by
  unfold fdBoundaryBreakpoints
  simp

section Branches

/-!
The `simp` normal form: the five branch selectors together with the segment-endpoint
values form the simp set, so `fdBoundary H t` at a corner numeral reduces in two steps —
branch selection, then the endpoint value (`fdBoundary H 1` to `fdBoundary_segment1 H 1` to
`↑ρ + 1`). The `fdBoundary_apply_*` corner lemmas below restate the composites for `rw`
ergonomics; they are deliberately not `@[simp]`, since the two-step chain already
reduces their left-hand sides (`simp`-normal-form confluence).
-/

variable {H t : ℝ}

/-- On `t ≤ 1` the path follows segment 1. -/
@[simp]
lemma fdBoundary_of_le_one (ht : t ≤ 1) : fdBoundary H t = fdBoundary_segment1 H t := by
  unfold fdBoundary
  rw [if_pos ht]

/-- On `1 < t ≤ 2` the path follows segment 2. -/
@[simp]
lemma fdBoundary_of_le_two (h1 : 1 < t) (h2 : t ≤ 2) : fdBoundary H t = fdBoundary_segment2 t := by
  unfold fdBoundary
  rw [if_neg (not_le.mpr h1), if_pos h2]

/-- On `2 < t ≤ 3` the path follows segment 3. -/
@[simp]
lemma fdBoundary_of_le_three (h2 : 2 < t) (h3 : t ≤ 3) :
    fdBoundary H t = fdBoundary_segment3 t := by
  unfold fdBoundary
  rw [if_neg (by linarith : ¬t ≤ 1), if_neg (not_le.mpr h2), if_pos h3]

/-- On `3 < t ≤ 4` the path follows segment 4. -/
@[simp]
lemma fdBoundary_of_le_four (h3 : 3 < t) (h4 : t ≤ 4) :
    fdBoundary H t = fdBoundary_segment4 H t := by
  unfold fdBoundary
  rw [if_neg (by linarith : ¬t ≤ 1), if_neg (by linarith : ¬t ≤ 2),
    if_neg (not_le.mpr h3), if_pos h4]

/-- On `4 < t` the path follows segment 5. -/
@[simp]
lemma fdBoundary_of_gt_four (h4 : 4 < t) : fdBoundary H t = fdBoundary_segment5 H t := by
  unfold fdBoundary
  rw [if_neg (by linarith : ¬t ≤ 1), if_neg (by linarith : ¬t ≤ 2),
    if_neg (by linarith : ¬t ≤ 3), if_neg (not_le.mpr h4)]

end Branches

/-- The path starts at the top right corner `1/2 + H·i`. -/
lemma fdBoundary_apply_zero (H : ℝ) : fdBoundary H 0 = 1 / 2 + H * Complex.I := by simp

/-- The parameter `1` lands on the corner `ρ + 1`. -/
lemma fdBoundary_apply_one (H : ℝ) : fdBoundary H 1 = (ρ : ℂ) + 1 := by simp

/-- The parameter `2` lands on `i`. -/
lemma fdBoundary_apply_two (H : ℝ) : fdBoundary H 2 = Complex.I := by simp

/-- The parameter `3` lands on the elliptic corner `ρ`. -/
lemma fdBoundary_apply_three (H : ℝ) : fdBoundary H 3 = (ρ : ℂ) := by norm_num

/-- The parameter `4` lands on the top left corner `-1/2 + H·i`. -/
lemma fdBoundary_apply_four (H : ℝ) : fdBoundary H 4 = -1 / 2 + H * Complex.I := by norm_num

/-- The path ends where it starts, at `1/2 + H·i`. -/
lemma fdBoundary_apply_five (H : ℝ) : fdBoundary H 5 = 1 / 2 + H * Complex.I := by norm_num

/-- The boundary contour is closed. -/
lemma fdBoundary_closed (H : ℝ) : fdBoundary H 5 = fdBoundary H 0 := by
  rw [fdBoundary_apply_five, fdBoundary_apply_zero]

end ModularForm

end TauCeti

end
