/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import TauCeti.Analysis.Contour.PiecewiseC1On

import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.MeasureTheory.Integral.CircleIntegral

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

* `TauCeti.ModularForm.fdBoundary` (with the segments `fdBoundarySegment1` … `fdBoundarySegment5`,
  built from `AffineMap.lineMap` and `circleMap`).
* `TauCeti.ModularForm.rho_im`: the corner `ρ` sits on the row `Im = √3/2`.
* `TauCeti.ModularForm.segment1_chord_im`: the right vertical's chord spans the height
  difference `√3/2 - H`.
* `TauCeti.ModularForm.fdBoundary_apply_three`: the parameter `3` lands on `ρ`.
* `TauCeti.ModularForm.fdBoundary_closed`: the contour is closed.
* `TauCeti.ModularForm.continuous_fdBoundary`: the contour is (globally) continuous.
* `TauCeti.ModularForm.isPiecewiseC1On_fdBoundary`: the contour is piecewise `C¹`
  (`contDiffOn_fdBoundary` certifies `fdBoundaryCorners` as a breakpoint witness).
* `TauCeti.ModularForm.injOn_fdBoundary_arc`: the arc is traversed injectively — it covers less
  than a full turn of the unit circle.
* `TauCeti.ModularForm.fdBoundary_four_sub_vertical`, `…_four_sub_arc`: the reflection
  `t ↦ 4 - t` identifies the verticals through `z ↦ z - 1` and the arc with its own
  reversal through `z ↦ -1/z` — the boundary identifications driving the cancellations
  in the valence-formula contour integral.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development this file ports onto the current Mathlib pin.
-/

public noncomputable section

open Complex UpperHalfPlane

open scoped Real

namespace TauCeti

namespace ModularForm

/-- **The corner `ρ` sits on the row `Im = √3/2`**, the height at which the two vertical
edges of `𝒟` meet the unit circle.

Not `@[simp]`, tested: Mathlib's `UpperHalfPlane.coe_im` is already `@[simp]` and rewrites the
left-hand side `(↑ρ).im` to `ρ.im` — the `ℍ`-valued imaginary part — so this statement is not in
simp-normal form and `simpNF` rejects the attribute. The lemma is a `rw` target for goals that
arrive in the complex form, which is how `Complex.sub_im` and friends leave them. -/
theorem rho_im : (UpperHalfPlane.ρ : ℂ).im = Real.sqrt 3 / 2 := by
  norm_num [UpperHalfPlane.ρ]

/-- Segment 1: the right vertical from `1/2 + H·i` through `ρ + 1`, over `t ∈ [0, 1]`. -/
def fdBoundarySegment1 (H : ℝ) : ℝ → ℂ := fun t ↦
  AffineMap.lineMap (1 / 2 + H * Complex.I) ((ρ : ℂ) + 1) t

/-- Segment 2: the unit-circle arc from `ρ + 1` to `i` (angle `π/3 → π/2`), over
`t ∈ [1, 2]`. -/
def fdBoundarySegment2 : ℝ → ℂ := fun t ↦
  circleMap 0 1 (Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3))

/-- Segment 3: the unit-circle arc from `i` to `ρ` (angle `π/2 → 2π/3`), over
`t ∈ [2, 3]`. -/
def fdBoundarySegment3 : ℝ → ℂ := fun t ↦
  circleMap 0 1 (Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2))

/-- Segment 4: the left vertical from `ρ` through `-1/2 + H·i`, over `t ∈ [3, 4]`. -/
def fdBoundarySegment4 (H : ℝ) : ℝ → ℂ := fun t ↦
  AffineMap.lineMap (ρ : ℂ) (-1 / 2 + H * Complex.I) (t - 3)

/-- Segment 5: the top horizontal from `-1/2 + H·i` to `1/2 + H·i`, over `t ∈ [4, 5]`. -/
def fdBoundarySegment5 (H : ℝ) : ℝ → ℂ := fun t ↦
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
lemma fdBoundarySegment1_apply (H t : ℝ) :
    fdBoundarySegment1 H t = AffineMap.lineMap (1 / 2 + H * Complex.I) ((ρ : ℂ) + 1) t := by
  unfold fdBoundarySegment1
  rfl

/-- Segment 2 evaluated: the unit-circle arc at angle `π/3 + (t - 1)·(π/2 - π/3)`. -/
lemma fdBoundarySegment2_apply (t : ℝ) :
    fdBoundarySegment2 t =
      circleMap 0 1 (Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) := by
  unfold fdBoundarySegment2
  rfl

/-- Segment 3 evaluated: the unit-circle arc at angle `π/2 + (t - 2)·(2π/3 - π/2)`. -/
lemma fdBoundarySegment3_apply (t : ℝ) :
    fdBoundarySegment3 t =
      circleMap 0 1 (Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) := by
  unfold fdBoundarySegment3
  rfl

/-- Segment 4 evaluated: the line from `ρ` to `-1/2 + H·i` at parameter `t - 3`. -/
lemma fdBoundarySegment4_apply (H t : ℝ) :
    fdBoundarySegment4 H t = AffineMap.lineMap (ρ : ℂ) (-1 / 2 + H * Complex.I) (t - 3) := by
  unfold fdBoundarySegment4
  rfl

/-- Segment 5 evaluated: the line from `-1/2 + H·i` to `1/2 + H·i` at parameter `t - 4`. -/
lemma fdBoundarySegment5_apply (H t : ℝ) :
    fdBoundarySegment5 H t =
      AffineMap.lineMap (-1 / 2 + H * Complex.I) (1 / 2 + H * Complex.I) (t - 4) := by
  unfold fdBoundarySegment5
  rfl

end SegmentApply

section SegmentEndpoints

/-- Segment 1 starts at the top right corner `1/2 + H·i`. -/
@[simp]
lemma fdBoundarySegment1_apply_zero (H : ℝ) : fdBoundarySegment1 H 0 = 1 / 2 + H * Complex.I := by
  rw [fdBoundarySegment1_apply, AffineMap.lineMap_apply_zero]

/-- Segment 1 ends at the corner `ρ + 1`. -/
@[simp]
lemma fdBoundarySegment1_apply_one (H : ℝ) : fdBoundarySegment1 H 1 = (ρ : ℂ) + 1 := by
  rw [fdBoundarySegment1_apply, AffineMap.lineMap_apply_one]

/-- Segment 2 starts at the corner `ρ + 1`. -/
@[simp]
lemma fdBoundarySegment2_apply_one : fdBoundarySegment2 1 = (ρ : ℂ) + 1 := by
  have hangle : Real.pi / 3 + ((1 : ℝ) - 1) * (Real.pi / 2 - Real.pi / 3) = Real.pi / 3 := by
    ring
  rw [fdBoundarySegment2_apply, hangle]
  refine Complex.ext ?_ ?_
  · rw [circleMap_zero_re, Real.cos_pi_div_three]
    simp [ρ]
    norm_num
  · rw [circleMap_zero_im, Real.sin_pi_div_three]
    simp [ρ]

/-- Segment 2 ends at `i`. -/
@[simp]
lemma fdBoundarySegment2_apply_two : fdBoundarySegment2 2 = Complex.I := by
  have hangle : Real.pi / 3 + ((2 : ℝ) - 1) * (Real.pi / 2 - Real.pi / 3) = Real.pi / 2 := by
    ring
  rw [fdBoundarySegment2_apply, hangle, circleMap_pi_div_two]
  simp

/-- Segment 3 starts at `i`. -/
@[simp]
lemma fdBoundarySegment3_apply_two : fdBoundarySegment3 2 = Complex.I := by
  have hangle : Real.pi / 2 + ((2 : ℝ) - 2) * (2 * Real.pi / 3 - Real.pi / 2) = Real.pi / 2 := by
    ring
  rw [fdBoundarySegment3_apply, hangle, circleMap_pi_div_two]
  simp

/-- Segment 3 ends at the elliptic corner `ρ`. -/
@[simp]
lemma fdBoundarySegment3_apply_three : fdBoundarySegment3 3 = (ρ : ℂ) := by
  have hangle : Real.pi / 2 + ((3 : ℝ) - 2) * (2 * Real.pi / 3 - Real.pi / 2) =
      Real.pi - Real.pi / 3 := by ring
  rw [fdBoundarySegment3_apply, hangle]
  refine Complex.ext ?_ ?_
  · rw [circleMap_zero_re, Real.cos_pi_sub, Real.cos_pi_div_three]
    simp [ρ]
    norm_num
  · rw [circleMap_zero_im, Real.sin_pi_sub, Real.sin_pi_div_three]
    simp [ρ]

/-- Segment 4 starts at the elliptic corner `ρ`. -/
@[simp]
lemma fdBoundarySegment4_apply_three (H : ℝ) : fdBoundarySegment4 H 3 = (ρ : ℂ) := by
  have hpar : (3 : ℝ) - 3 = 0 := by norm_num
  rw [fdBoundarySegment4_apply, hpar, AffineMap.lineMap_apply_zero]

/-- Segment 4 ends at the top left corner `-1/2 + H·i`. -/
@[simp]
lemma fdBoundarySegment4_apply_four (H : ℝ) :
    fdBoundarySegment4 H 4 = -1 / 2 + H * Complex.I := by
  have hpar : (4 : ℝ) - 3 = 1 := by norm_num
  rw [fdBoundarySegment4_apply, hpar, AffineMap.lineMap_apply_one]

/-- Segment 5 starts at the top left corner `-1/2 + H·i`. -/
@[simp]
lemma fdBoundarySegment5_apply_four (H : ℝ) :
    fdBoundarySegment5 H 4 = -1 / 2 + H * Complex.I := by
  have hpar : (4 : ℝ) - 4 = 0 := by norm_num
  rw [fdBoundarySegment5_apply, hpar, AffineMap.lineMap_apply_zero]

/-- Segment 5 ends at the top right corner `1/2 + H·i`. -/
@[simp]
lemma fdBoundarySegment5_apply_five (H : ℝ) : fdBoundarySegment5 H 5 = 1 / 2 + H * Complex.I := by
  have hpar : (5 : ℝ) - 4 = 1 := by norm_num
  rw [fdBoundarySegment5_apply, hpar, AffineMap.lineMap_apply_one]

end SegmentEndpoints

/-- The raw five-segment path at height parameter `H`, parameterized over `[0, 5]` and
closed for every `H`. For `1 < H` it is the boundary of the standard fundamental domain
truncated at height `H`. -/
def fdBoundary (H : ℝ) : ℝ → ℂ := fun t ↦
  if t ≤ 1 then fdBoundarySegment1 H t
  else if t ≤ 2 then fdBoundarySegment2 t
  else if t ≤ 3 then fdBoundarySegment3 t
  else if t ≤ 4 then fdBoundarySegment4 H t
  else fdBoundarySegment5 H t

/-- The four interior subdivision parameters of the five-segment parameterization; the
junction at `2` is smooth, so only `fdBoundaryCorners` are genuine corners. -/
def fdBoundaryBreakpoints : Finset ℝ := {1, 2, 3, 4}

/-- Membership in the four subdivision parameters. -/
@[simp]
lemma mem_fdBoundaryBreakpoints {t : ℝ} :
    t ∈ fdBoundaryBreakpoints ↔ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by
  unfold fdBoundaryBreakpoints
  simp

section Branches

/-!
The `simp` normal form: the five branch selectors together with the segment-endpoint
values form the simp set, so `fdBoundary H t` at a corner numeral reduces in two steps —
branch selection, then the endpoint value (`fdBoundary H 1` to `fdBoundarySegment1 H 1` to
`↑ρ + 1`). The `fdBoundary_apply_*` corner lemmas below restate the composites for `rw`
ergonomics; they are deliberately not `@[simp]`, since the two-step chain already
reduces their left-hand sides (`simp`-normal-form confluence).
-/

variable {H t : ℝ}

/-- On `t ≤ 1` the path follows segment 1. -/
@[simp]
lemma fdBoundary_of_le_one (ht : t ≤ 1) : fdBoundary H t = fdBoundarySegment1 H t := by
  unfold fdBoundary
  rw [ite_eq_left ht]

/-- On `1 < t ≤ 2` the path follows segment 2. -/
@[simp]
lemma fdBoundary_of_le_two (h1 : 1 < t) (h2 : t ≤ 2) : fdBoundary H t = fdBoundarySegment2 t := by
  unfold fdBoundary
  rw [ite_eq_right (not_le.mpr h1), ite_eq_left h2]

/-- On `2 < t ≤ 3` the path follows segment 3. -/
@[simp]
lemma fdBoundary_of_le_three (h2 : 2 < t) (h3 : t ≤ 3) :
    fdBoundary H t = fdBoundarySegment3 t := by
  unfold fdBoundary
  rw [ite_eq_right (by linarith : ¬t ≤ 1), ite_eq_right (not_le.mpr h2), ite_eq_left h3]

/-- On `3 < t ≤ 4` the path follows segment 4. -/
@[simp]
lemma fdBoundary_of_le_four (h3 : 3 < t) (h4 : t ≤ 4) :
    fdBoundary H t = fdBoundarySegment4 H t := by
  unfold fdBoundary
  rw [ite_eq_right (by linarith : ¬t ≤ 1), ite_eq_right (by linarith : ¬t ≤ 2),
    ite_eq_right (not_le.mpr h3), ite_eq_left h4]

/-- On `4 < t` the path follows segment 5. -/
@[simp]
lemma fdBoundary_of_gt_four (h4 : 4 < t) : fdBoundary H t = fdBoundarySegment5 H t := by
  unfold fdBoundary
  rw [ite_eq_right (by linarith : ¬t ≤ 1), ite_eq_right (by linarith : ¬t ≤ 2),
    ite_eq_right (by linarith : ¬t ≤ 3), ite_eq_right (not_le.mpr h4)]

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

section Regularity

open Set

open scoped ContDiff

variable {n : WithTop ℕ∞}

/-- Segment 1 is smooth. -/
lemma contDiff_fdBoundarySegment1 (H : ℝ) : ContDiff ℝ n (fdBoundarySegment1 H) :=
  AffineMap.contDiff_lineMap _ _

/-- Segment 2 is smooth. -/
lemma contDiff_fdBoundarySegment2 : ContDiff ℝ n fdBoundarySegment2 :=
  (contDiff_circleMap _ _).comp (by fun_prop)

/-- Segment 3 is smooth. -/
lemma contDiff_fdBoundarySegment3 : ContDiff ℝ n fdBoundarySegment3 :=
  (contDiff_circleMap _ _).comp (by fun_prop)

/-- Segment 4 is smooth. -/
lemma contDiff_fdBoundarySegment4 (H : ℝ) : ContDiff ℝ n (fdBoundarySegment4 H) :=
  (AffineMap.contDiff_lineMap _ _).comp (contDiff_id.sub contDiff_const)

/-- Segment 5 is smooth. -/
lemma contDiff_fdBoundarySegment5 (H : ℝ) : ContDiff ℝ n (fdBoundarySegment5 H) :=
  (AffineMap.contDiff_lineMap _ _).comp (contDiff_id.sub contDiff_const)

/-- On `[0, 1]` the path agrees with segment 1. -/
lemma eqOn_fdBoundarySegment1 (H : ℝ) : EqOn (fdBoundary H) (fdBoundarySegment1 H) (Icc 0 1) :=
  fun _ ht ↦ fdBoundary_of_le_one ht.2

/-- On `[1, 2]` the path agrees with segment 2. -/
lemma eqOn_fdBoundarySegment2 (H : ℝ) : EqOn (fdBoundary H) fdBoundarySegment2 (Icc 1 2) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h1 | h1
  · rw [← h1, fdBoundary_apply_one, fdBoundarySegment2_apply_one]
  · exact fdBoundary_of_le_two h1 ht.2

/-- On `[2, 3]` the path agrees with segment 3. -/
lemma eqOn_fdBoundarySegment3 (H : ℝ) : EqOn (fdBoundary H) fdBoundarySegment3 (Icc 2 3) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h2 | h2
  · rw [← h2, fdBoundary_apply_two, fdBoundarySegment3_apply_two]
  · exact fdBoundary_of_le_three h2 ht.2

/-- On `[3, 4]` the path agrees with segment 4. -/
lemma eqOn_fdBoundarySegment4 (H : ℝ) : EqOn (fdBoundary H) (fdBoundarySegment4 H) (Icc 3 4) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h3 | h3
  · rw [← h3, fdBoundary_apply_three, fdBoundarySegment4_apply_three]
  · exact fdBoundary_of_le_four h3 ht.2

/-- On `[4, 5]` the path agrees with segment 5. -/
lemma eqOn_fdBoundarySegment5 (H : ℝ) : EqOn (fdBoundary H) (fdBoundarySegment5 H) (Icc 4 5) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h4 | h4
  · rw [← h4, fdBoundary_apply_four, fdBoundarySegment5_apply_four]
  · exact fdBoundary_of_gt_four h4

private lemma fdBoundary_piece1 (H : ℝ) : ContDiffOn ℝ n (fdBoundary H) (Icc 0 1) :=
  (contDiff_fdBoundarySegment1 H).contDiffOn.congr (eqOn_fdBoundarySegment1 H)

/-- On `[1, 3]` the path agrees with the unified unit-circle arc of angle `(t + 1)·π/6`:
the two arc segments continue one smooth circle parameterization. -/
lemma eqOn_fdBoundary_arc (H : ℝ) :
    EqOn (fdBoundary H) (fun s : ℝ ↦ circleMap 0 1 ((s + 1) * (Real.pi / 6))) (Icc 1 3) := by
  intro t ht
  rcases le_or_gt t 2 with h2 | h2
  · rcases eq_or_lt_of_le ht.1 with h1 | h1
    · rw [← h1, fdBoundary_apply_one, ← fdBoundarySegment2_apply_one,
        fdBoundarySegment2_apply]
      congr 1
      ring
    · rw [fdBoundary_of_le_two h1 h2, fdBoundarySegment2_apply]
      congr 1
      ring
  · rw [fdBoundary_of_le_three h2 ht.2, fdBoundarySegment3_apply]
    congr 1
    ring

private lemma fdBoundary_piece13 (H : ℝ) : ContDiffOn ℝ n (fdBoundary H) (Icc 1 3) :=
  (((contDiff_circleMap 0 1).comp (by fun_prop)).contDiffOn).congr (eqOn_fdBoundary_arc H)

private lemma fdBoundary_piece4 (H : ℝ) : ContDiffOn ℝ n (fdBoundary H) (Icc 3 4) :=
  (contDiff_fdBoundarySegment4 H).contDiffOn.congr (eqOn_fdBoundarySegment4 H)

private lemma fdBoundary_piece5 (H : ℝ) : ContDiffOn ℝ n (fdBoundary H) (Icc 4 5) :=
  (contDiff_fdBoundarySegment5 H).contDiffOn.congr (eqOn_fdBoundarySegment5 H)


/-- **The arc is traversed injectively.** On `[1, 3]` the boundary runs through the angles
`[π/3, 2π/3]` of the unit circle — less than one full turn — so `circleMap` is injective there
and distinct parameters give distinct points. -/
theorem injOn_fdBoundary_arc (H : ℝ) : InjOn (fdBoundary H) (Icc 1 3) := by
  have hpi := Real.pi_pos
  have hcm : InjOn (circleMap 0 1) (Ioc 0 (2 * Real.pi)) := by
    rw [← uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    exact injOn_circleMap_of_abs_sub_le one_ne_zero
      (by rw [zero_sub, abs_neg, abs_of_pos (by positivity)])
  have hmem : ∀ {t : ℝ}, t ∈ Icc (1 : ℝ) 3 → (t + 1) * (Real.pi / 6) ∈ Ioc 0 (2 * Real.pi) :=
    fun ht => ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  intro t₁ h₁ t₂ h₂ heq
  rw [eqOn_fdBoundary_arc H h₁, eqOn_fdBoundary_arc H h₂] at heq
  nlinarith [hcm (hmem h₁) (hmem h₂) heq]

/-- The genuinely nonsmooth junctions of the boundary contour: the two arcs continue one
smooth circle parameterization through `t = 2`, so only `1`, `3`, and `4` are corners. -/
def fdBoundaryCorners : Finset ℝ := {1, 3, 4}

/-- Membership in the corner parameters. -/
@[simp]
lemma mem_fdBoundaryCorners {t : ℝ} : t ∈ fdBoundaryCorners ↔ t = 1 ∨ t = 3 ∨ t = 4 := by
  unfold fdBoundaryCorners
  simp

/-- The boundary path is continuous: consecutive segments agree at the junctions. -/
lemma continuous_fdBoundary (H : ℝ) : Continuous (fdBoundary H) := by
  unfold fdBoundary
  refine Continuous.if_le (contDiff_fdBoundarySegment1 (n := 1) H).continuous
    (Continuous.if_le (contDiff_fdBoundarySegment2 (n := 1)).continuous
      (Continuous.if_le (contDiff_fdBoundarySegment3 (n := 1)).continuous
        (Continuous.if_le (contDiff_fdBoundarySegment4 (n := 1) H).continuous
          (contDiff_fdBoundarySegment5 (n := 1) H).continuous continuous_id continuous_const
          fun t ht ↦ ?_)
        continuous_id continuous_const fun t ht ↦ ?_)
      continuous_id continuous_const fun t ht ↦ ?_)
    continuous_id continuous_const fun t ht ↦ ?_
  all_goals subst ht
  all_goals norm_num

/-- The boundary path is continuous on the parameter interval `[0, 5]`. -/
lemma continuousOn_fdBoundary (H : ℝ) : ContinuousOn (fdBoundary H) (Icc 0 5) :=
  (continuous_fdBoundary H).continuousOn

/-- A corner-free closed subinterval of `[0, 5]` lies inside one smooth piece — the
classification certificate shared by the smoothness and immersion witnesses. -/
theorem subset_piece_of_disjoint_corners {c d : ℝ} (hcd : Icc c d ⊆ Icc (0 : ℝ) 5)
    (hdis : Disjoint (fdBoundaryCorners : Set ℝ) (Ioo c d)) :
    Icc c d ⊆ Icc (0 : ℝ) 1 ∨ Icc c d ⊆ Icc (1 : ℝ) 3 ∨ Icc c d ⊆ Icc (3 : ℝ) 4 ∨
      Icc c d ⊆ Icc (4 : ℝ) 5 := by
  have hbp : ∀ m : ℝ, m ∈ fdBoundaryCorners → m ∉ Ioo c d := fun m hm ↦
    Set.disjoint_left.mp hdis (Finset.mem_coe.mpr hm)
  rcases le_or_gt d 1 with hd1 | hd1
  · exact Or.inl fun x hx ↦ ⟨(hcd hx).1, hx.2.trans hd1⟩
  · have hc1 : 1 ≤ c := le_of_not_gt fun hlt ↦ hbp 1 (by simp) ⟨hlt, hd1⟩
    rcases le_or_gt d 3 with hd3 | hd3
    · exact Or.inr (Or.inl fun x hx ↦ ⟨hc1.trans hx.1, hx.2.trans hd3⟩)
    · have hc3 : 3 ≤ c := le_of_not_gt fun hlt ↦ hbp 3 (by simp) ⟨hlt, hd3⟩
      rcases le_or_gt d 4 with hd4 | hd4
      · exact Or.inr (Or.inr (Or.inl fun x hx ↦ ⟨hc3.trans hx.1, hx.2.trans hd4⟩))
      · have hc4 : 4 ≤ c := le_of_not_gt fun hlt ↦ hbp 4 (by simp) ⟨hlt, hd4⟩
        exact Or.inr (Or.inr (Or.inr fun x hx ↦ ⟨hc4.trans hx.1, (hcd hx).2⟩))

/-- On every closed subinterval of `[0, 5]` whose interior avoids the three genuine
corners, the contour is smooth at every order — the certificate that `fdBoundaryCorners`
is a valid breakpoint witness for `isPiecewiseC1On_fdBoundary`. The two arcs continue one
smooth circle map through `t = 2`, so no hypothesis excludes it. -/
lemma contDiffOn_fdBoundary (H : ℝ) {c d : ℝ}
    (hcd : Icc c d ⊆ Icc 0 5) (hdis : Disjoint (fdBoundaryCorners : Set ℝ) (Ioo c d)) :
    ContDiffOn ℝ n (fdBoundary H) (Icc c d) := by
  rcases subset_piece_of_disjoint_corners hcd hdis with h | h | h | h
  · exact (fdBoundary_piece1 H).mono h
  · exact (fdBoundary_piece13 H).mono h
  · exact (fdBoundary_piece4 H).mono h
  · exact (fdBoundary_piece5 H).mono h

/-- The left vertical ascends affinely from the corner row to the ceiling. -/
lemma im_fdBoundary_of_le_four (h3 : 3 < t) (h4 : t ≤ 4) :
    (fdBoundary H t).im = Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2) := by
  rw [fdBoundary_of_le_four h3 h4, fdBoundarySegment4_apply, AffineMap.lineMap_apply_module']
  have hchord : ((-1 / 2 + H * Complex.I : ℂ) - (ρ : ℂ)).im = H - Real.sqrt 3 / 2 := by
    simp [ρ]
  rw [Complex.add_im, Complex.smul_im, hchord, rho_im, smul_eq_mul, add_comm]

/-- The right vertical has constant real part `1/2`. -/
theorem re_fdBoundarySegment1 (H : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (fdBoundary H t).re = 1 / 2 := by
  rw [eqOn_fdBoundarySegment1 H ht, fdBoundarySegment1_apply, AffineMap.lineMap_apply]
  simp [ρ, Complex.real_smul]
  norm_num

/-- The arc stays at height at most `1`. -/
theorem im_fdBoundary_arc_le (H : ℝ) {t : ℝ} (ht : t ∈ Icc (1 : ℝ) 3) :
    (fdBoundary H t).im ≤ 1 := by
  rw [eqOn_fdBoundary_arc H ht, circleMap_zero_im]
  simpa using Real.sin_le_one ((t + 1) * (Real.pi / 6))

/-- The arc stays in the open upper half-plane. -/
theorem im_fdBoundary_arc_pos (H : ℝ) {t : ℝ} (ht : t ∈ Icc (1 : ℝ) 3) :
    0 < (fdBoundary H t).im := by
  rw [eqOn_fdBoundary_arc H ht, circleMap_zero_im, one_mul]
  have h5 : (0 : ℝ) < 5 - t := by linarith [ht.2]
  exact Real.sin_pos_of_pos_of_lt_pi (mul_pos (by linarith [ht.1]) (by positivity))
    (by nlinarith [mul_pos Real.pi_pos h5])

/-- The left vertical has constant real part `-1/2`. -/
theorem re_fdBoundarySegment4 (H : ℝ) {t : ℝ} (ht : t ∈ Icc (3 : ℝ) 4) :
    (fdBoundary H t).re = -(1 / 2) := by
  rw [eqOn_fdBoundarySegment4 H ht, fdBoundarySegment4_apply, AffineMap.lineMap_apply]
  simp [ρ, Complex.real_smul]
  norm_num

/-- The truncation ceiling has constant height `H`. -/
theorem im_fdBoundarySegment5 (H : ℝ) {t : ℝ} (ht : t ∈ Icc (4 : ℝ) 5) :
    (fdBoundary H t).im = H := by
  rw [eqOn_fdBoundarySegment5 H ht, fdBoundarySegment5_apply, AffineMap.lineMap_apply]
  simp [Complex.real_smul]

/-- The fundamental-domain boundary contour is piecewise `C¹` on `[0, 5]`;
`contDiffOn_fdBoundary` certifies the three genuine corners as a breakpoint witness. -/
theorem isPiecewiseC1On_fdBoundary (H : ℝ) : Contour.IsPiecewiseC1On (fdBoundary H) 0 5 := by
  refine Contour.IsPiecewiseC1On.of_breakpoints ?_ fdBoundaryCorners ?_ ?_
  · rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
    exact continuousOn_fdBoundary H
  · intro x hx
    rw [Finset.mem_coe, mem_fdBoundaryCorners] at hx
    rw [min_eq_left (by norm_num : (0 : ℝ) ≤ 5), max_eq_right (by norm_num : (0 : ℝ) ≤ 5)]
    rcases hx with rfl | rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩
  · intro c d hcd hdis
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at hcd
    exact contDiffOn_fdBoundary H hcd hdis

/-- The reflection `t ↦ 4 - t` of the parameter interval carries the right vertical onto
the left vertical through the translation `z ↦ z - 1`: the two verticals of the
fundamental-domain boundary are identified by `T⁻¹`. -/
@[simp]
theorem fdBoundary_four_sub_vertical (H : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    fdBoundary H (4 - t) = fdBoundary H t - 1 := by
  rw [eqOn_fdBoundarySegment4 H ⟨by linarith [ht.2], by linarith [ht.1]⟩,
    eqOn_fdBoundarySegment1 H ht, fdBoundarySegment4_apply, fdBoundarySegment1_apply,
    AffineMap.lineMap_apply, AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
  push_cast
  ring

/-- The reflection `t ↦ 4 - t` of the parameter interval carries the unit-circle arc onto
itself, reversed, through the inversion `z ↦ -1/z`: the two halves of the arc of the
fundamental-domain boundary are identified by `S`. -/
@[simp]
theorem fdBoundary_four_sub_arc (H : ℝ) {t : ℝ} (ht : t ∈ Icc (1 : ℝ) 3) :
    fdBoundary H (4 - t) = -1 / fdBoundary H t := by
  have hangle : (4 - t + 1) * (Real.pi / 6) + (t + 1) * (Real.pi / 6) = Real.pi := by ring
  rw [eqOn_fdBoundary_arc H ⟨by linarith [ht.2], by linarith [ht.1]⟩,
    eqOn_fdBoundary_arc H ht, eq_div_iff (circleMap_ne_center one_ne_zero),
    circleMap_zero_mul, hangle]
  simp [circleMap_zero, Complex.exp_pi_mul_I]

end Regularity

/-! ## Coordinates of the segments

The real part, imaginary part and norm of the contour, segment by segment: elementary
computations from the segment formulas, needed wherever a point of the boundary has to be
located. They say nothing about winding, and are used by the principal-value and capture
arguments as much as by the winding ones.
-/

section Coordinates

open Set

variable {H t : ℝ}

/-- The right vertical has constant real part `1/2`. -/
lemma re_fdBoundary_of_le_one (h1 : t ≤ 1) : (fdBoundary H t).re = 1 / 2 := by
  rw [fdBoundary_of_le_one h1, fdBoundarySegment1_apply, AffineMap.lineMap_apply_module']
  have hchord : ((ρ : ℂ) + 1 - (1 / 2 + H * Complex.I)).re = 0 := by
    simp [ρ]
    norm_num
  rw [Complex.add_re, Complex.smul_re, hchord, smul_eq_mul, mul_zero, zero_add]
  simp

/-- **The segment-1 chord spans the height difference**: the right vertical runs from the ceiling
`H` to the corner row `√3/2`, so its chord has imaginary part `√3/2 - H`.

Not `@[simp]`, for the same reason as `rho_im`: `UpperHalfPlane.coe_im` normalises `(↑ρ).im` away
before this could fire, so the left-hand side is not in simp-normal form. -/
theorem segment1_chord_im :
    ((ρ : ℂ) + 1 - (1 / 2 + H * Complex.I)).im = Real.sqrt 3 / 2 - H := by
  rw [Complex.sub_im, Complex.add_im, rho_im]
  simp

/-- The right vertical runs affinely in height from the ceiling `H` to the corner row `√3/2`,
descending when the ceiling is above that row and ascending when it is below. -/
lemma im_fdBoundary_of_le_one (h1 : t ≤ 1) :
    (fdBoundary H t).im = H + t * (Real.sqrt 3 / 2 - H) := by
  rw [fdBoundary_of_le_one h1, fdBoundarySegment1_apply, AffineMap.lineMap_apply_module']
  have him : (1 / 2 + H * Complex.I : ℂ).im = H := by simp
  rw [Complex.add_im, Complex.smul_im, segment1_chord_im, him, smul_eq_mul, add_comm]

/-- The left vertical has constant real part `-1/2`. -/
lemma re_fdBoundary_of_le_four (h3 : 3 < t) (h4 : t ≤ 4) :
    (fdBoundary H t).re = -(1 / 2) := by
  rw [fdBoundary_of_le_four h3 h4, fdBoundarySegment4_apply, AffineMap.lineMap_apply_module']
  have hchord : ((-1 / 2 + H * Complex.I : ℂ) - (ρ : ℂ)).re = 0 := by
    simp [ρ]
  rw [Complex.add_re, Complex.smul_re, hchord, smul_eq_mul, mul_zero, zero_add]
  simp [ρ]
  norm_num

/-- The truncation ceiling runs affinely from the left corner to the right. -/
lemma re_fdBoundary_of_gt_four (h4 : 4 < t) :
    (fdBoundary H t).re = -(1 / 2) + (t - 4) := by
  rw [fdBoundary_of_gt_four h4, fdBoundarySegment5_apply, AffineMap.lineMap_apply_module']
  have hchord : ((1 / 2 + H * Complex.I : ℂ) - (-1 / 2 + H * Complex.I)).re = 1 := by
    simp
    norm_num
  have hre : (-1 / 2 + H * Complex.I : ℂ).re = -(1 / 2) := by
    simp
    norm_num
  rw [Complex.add_re, Complex.smul_re, hchord, hre, smul_eq_mul, mul_one, add_comm]

/-- The truncation ceiling has constant height `H`. -/
lemma im_fdBoundary_of_gt_four (h4 : 4 < t) : (fdBoundary H t).im = H := by
  rw [fdBoundary_of_gt_four h4, fdBoundarySegment5_apply, AffineMap.lineMap_apply_module']
  have h5 : ((1 / 2 + H * Complex.I : ℂ) - (-1 / 2 + H * Complex.I)).im = 0 := by
    simp
  rw [Complex.add_im, Complex.smul_im, h5, smul_eq_mul, mul_zero, zero_add]
  simp

/-- The arc lies on the unit circle. -/
@[simp]
lemma norm_fdBoundary_arc (h1 : 1 ≤ t) (h3 : t ≤ 3) : ‖fdBoundary H t‖ = 1 := by
  rw [eqOn_fdBoundary_arc H ⟨h1, h3⟩, norm_circleMap_zero, abs_one]

end Coordinates

end ModularForm

end TauCeti

end
