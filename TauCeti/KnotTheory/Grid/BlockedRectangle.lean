/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.ZMod.Basic
public import TauCeti.KnotTheory.Grid.Rectangle.Basic
import TauCeti.KnotTheory.Grid.Rectangle.Count
import TauCeti.KnotTheory.Grid.Rectangle.Swap

/-!
# Fully blocked empty rectangles in grid diagrams

This file packages the finite rectangle counts used by the fully blocked grid differential.
For grid states `x` and `y`, the already-defined `GridRectangleBetween x y` records an
oriented toroidal rectangle from `x` to `y`. Here we filter the generic empty-rectangle
enumeration to rectangles whose interiors avoid all `O` and `X` markings of a grid diagram.

The final count is valued in `ZMod 2`, matching the first coefficient system used in the grid
homology roadmap.

## Main definitions

* `TauCeti.GridDiagram.fullyBlockedRectangles`: empty rectangles avoiding all markings.
* `TauCeti.GridDiagram.fullyBlockedRectangleCount`: the corresponding count in `ZMod 2`.
* `TauCeti.GridDiagram.card_fullyBlockedRectangles_le_two`: at most two fully blocked rectangles
  contribute to each matrix coefficient.

## Main results

* `TauCeti.GridDiagram.fullyBlockedRectangleCount_transpose`: the count is invariant under the
  diagonal reflection of a grid diagram and its two states.
* `TauCeti.GridDiagram.fullyBlockedRectangleCount_rotate`: the count is invariant under the
  half-turn rotation of a grid diagram and its two states.
* `TauCeti.GridDiagram.fullyBlockedRectangles_swapMarkings` and
  `TauCeti.GridDiagram.fullyBlockedRectangleCount_swapMarkings`: the rectangle set and its count
  are unchanged by swapping the `O` and `X` markings.

## References

This supplies a prerequisite for the Tau Ceti Heegaard Floer roadmap,
`HeegaardFloer/README.md` in TauCetiRoadmap, Lane G.3, "The complexes and `∂² = 0`",
where the fully blocked grid complex over `𝔽₂` counts rectangles avoiding all markings. The
objects and terminology follow Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Chapter 3.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (x y : GridState n)

/-- The finite set of fully blocked empty rectangles from `x` to `y` in a grid diagram.

"Fully blocked" means that the rectangle is empty for the source grid state and its interior
avoids every `O` and `X` marking. This is the rectangle set whose parity gives the coefficient
of `y` in the fully blocked grid differential applied to `x`. -/
@[expose] noncomputable def fullyBlockedRectangles : Finset (GridRectangleBetween x y) := by
  classical
  exact (GridRectangleBetween.emptyRectangles x y).filter fun R => R.AvoidsMarkings G

/-- Membership in the fully blocked rectangle set is emptiness together with marking
avoidance. -/
@[simp]
theorem mem_fullyBlockedRectangles (R : GridRectangleBetween x y) :
    R ∈ G.fullyBlockedRectangles x y ↔ R.IsEmpty ∧ R.AvoidsMarkings G := by
  classical
  simp [fullyBlockedRectangles]

/-- Every fully blocked rectangle is empty. -/
theorem isEmpty_of_mem_fullyBlockedRectangles {R : GridRectangleBetween x y}
    (hR : R ∈ G.fullyBlockedRectangles x y) : R.IsEmpty :=
  (G.mem_fullyBlockedRectangles x y R).mp hR |>.1

/-- Every fully blocked rectangle avoids the `O` and `X` markings. -/
theorem avoidsMarkings_of_mem_fullyBlockedRectangles {R : GridRectangleBetween x y}
    (hR : R ∈ G.fullyBlockedRectangles x y) : R.AvoidsMarkings G :=
  (G.mem_fullyBlockedRectangles x y R).mp hR |>.2

/-- Fully blocked rectangles are a subset of the empty rectangles between the same states. -/
theorem fullyBlockedRectangles_subset_emptyRectangles :
    G.fullyBlockedRectangles x y ⊆ GridRectangleBetween.emptyRectangles x y := by
  classical
  intro R hR
  exact (GridRectangleBetween.mem_emptyRectangles R).mpr
    ((G.mem_fullyBlockedRectangles x y R).mp hR |>.1)

/-- Fully blocked rectangles are a subset of all rectangles between the same states. -/
theorem fullyBlockedRectangles_subset_all :
    G.fullyBlockedRectangles x y ⊆ GridRectangleBetween.all x y :=
  G.fullyBlockedRectangles_subset_emptyRectangles x y |>.trans
    (GridRectangleBetween.emptyRectangles_subset_all x y)

/-- There are at most two fully blocked rectangles in each matrix coefficient of the fully
blocked differential. -/
theorem card_fullyBlockedRectangles_le_two : (G.fullyBlockedRectangles x y).card ≤ 2 :=
  GridRectangleBetween.card_le_two (G.fullyBlockedRectangles x y)

/-- The number of fully blocked empty rectangles from `x` to `y`, reduced modulo `2`. -/
@[expose] noncomputable def fullyBlockedRectangleCount : ZMod 2 :=
  (G.fullyBlockedRectangles x y).card

/-- The fully blocked rectangle count is the cardinality of `fullyBlockedRectangles`, coerced
to `ZMod 2`. -/
theorem fullyBlockedRectangleCount_def :
    G.fullyBlockedRectangleCount x y = ((G.fullyBlockedRectangles x y).card : ZMod 2) :=
  rfl

/-- A nonzero fully blocked rectangle count forces the target state to be a column transposition
of the source state: a nonzero count means there is a fully blocked rectangle, hence an oriented
rectangle, between the two states. -/
theorem exists_swapColumns_of_fullyBlockedRectangleCount_ne_zero
    (h : G.fullyBlockedRectangleCount x y ≠ 0) :
    ∃ a b : Fin n, a ≠ b ∧ y = x.swapColumns a b := by
  rw [fullyBlockedRectangleCount_def] at h
  have hcard : (G.fullyBlockedRectangles x y).card ≠ 0 := by
    intro hc
    rw [hc] at h
    simp at h
  obtain ⟨R, hR⟩ := Finset.card_ne_zero.mp hcard
  exact ⟨R.left, R.right, R.left_ne_right, R.target_eq_swapColumns⟩

/-- The set of fully blocked rectangles from a grid state to itself is empty. -/
@[simp]
theorem fullyBlockedRectangles_self (x : GridState n) : G.fullyBlockedRectangles x x = ∅ := by
  classical
  simp [fullyBlockedRectangles]

/-- The fully blocked rectangle count from a grid state to itself is zero. -/
@[simp]
theorem fullyBlockedRectangleCount_self (x : GridState n) :
    G.fullyBlockedRectangleCount x x = 0 := by
  simp [fullyBlockedRectangleCount]

/-- The diagonal reflection of a fully blocked rectangle is a fully blocked rectangle for the
reflected diagram. -/
theorem mem_fullyBlockedRectangles_transpose (x y : GridState n) (R : GridRectangleBetween x y) :
    R.transpose ∈ G.transpose.fullyBlockedRectangles x.transpose y.transpose ↔
      R ∈ G.fullyBlockedRectangles x y := by
  simp only [mem_fullyBlockedRectangles, GridRectangleBetween.isEmpty_transpose,
    GridRectangleBetween.avoidsMarkings_transpose]

/-- The fully blocked rectangle count is invariant under the diagonal reflection of a grid
diagram and its two states. This is the matrix-coefficient form of the statement that the
diagonal reflection is a chain symmetry of the fully blocked grid complex. -/
theorem fullyBlockedRectangleCount_transpose (x y : GridState n) :
    G.transpose.fullyBlockedRectangleCount x.transpose y.transpose =
      G.fullyBlockedRectangleCount x y := by
  rw [fullyBlockedRectangleCount_def, fullyBlockedRectangleCount_def]
  congr 1
  exact (Finset.card_equiv (GridRectangleBetween.transposeEquiv x y) fun R =>
    (G.mem_fullyBlockedRectangles_transpose x y R).symm).symm

/-- The half-turn rotation of a fully blocked rectangle is a fully blocked rectangle for the
rotated diagram and rotated states. -/
theorem mem_fullyBlockedRectangles_rotate (x y : GridState n) (R : GridRectangleBetween x y) :
    R.rotate ∈ G.rotate.fullyBlockedRectangles x.rotate y.rotate ↔
      R ∈ G.fullyBlockedRectangles x y := by
  simp only [mem_fullyBlockedRectangles, GridRectangleBetween.isEmpty_rotate,
    GridRectangleBetween.avoidsMarkings_rotate]

/-- The fully blocked rectangle count is invariant under the half-turn rotation of a grid diagram
and its two states. This is the matrix-coefficient form of the statement that the half-turn
rotation is a chain symmetry of the fully blocked grid complex. -/
theorem fullyBlockedRectangleCount_rotate (x y : GridState n) :
    G.rotate.fullyBlockedRectangleCount x.rotate y.rotate =
      G.fullyBlockedRectangleCount x y := by
  rw [fullyBlockedRectangleCount_def, fullyBlockedRectangleCount_def]
  congr 1
  exact (Finset.card_equiv (GridRectangleBetween.rotateEquiv x y) fun R =>
    (G.mem_fullyBlockedRectangles_rotate x y R).symm).symm

/-- The fully blocked rectangles are unchanged by swapping the `O` and `X` markings, since
marking avoidance only refers to the union of the two marking sets. -/
@[simp]
theorem fullyBlockedRectangles_swapMarkings (x y : GridState n) :
    G.swapMarkings.fullyBlockedRectangles x y = G.fullyBlockedRectangles x y := by
  ext R
  rw [mem_fullyBlockedRectangles, mem_fullyBlockedRectangles,
    GridRectangleBetween.avoidsMarkings_swapMarkings]

/-- The fully blocked rectangle count is invariant under swapping the `O` and `X` markings. -/
@[simp]
theorem fullyBlockedRectangleCount_swapMarkings (x y : GridState n) :
    G.swapMarkings.fullyBlockedRectangleCount x y = G.fullyBlockedRectangleCount x y := by
  rw [fullyBlockedRectangleCount_def, fullyBlockedRectangleCount_def,
    fullyBlockedRectangles_swapMarkings]

end GridDiagram

end TauCeti
