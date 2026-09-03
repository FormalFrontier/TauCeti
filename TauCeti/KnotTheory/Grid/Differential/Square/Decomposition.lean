/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.Support
public import TauCeti.KnotTheory.Grid.Rectangle.Swap

/-!
# Two-step rectangle decompositions

A two-step term in the square of the grid differential consists of a rectangle from `x` to an
intermediate grid state and a second rectangle from that state to `z`. This file packages such a
factorization as `GridRectangleDecomposition`, the shared object on which the disjoint,
overlapping and annular cases of the square-zero argument all operate.

Such a factorization is determined by the ordered side columns of its two rectangles: the
intermediate state is the source with the first pair of columns swapped, and an oriented rectangle
between two given states is determined by its side columns.

## Main definitions

* `TauCeti.GridRectangleDecomposition`: two composable oriented grid rectangles.

## Main results

* `TauCeti.GridRectangleDecomposition.ext`: a decomposition is determined by the ordered side
  columns of its two rectangles.
* `TauCeti.GridRectangleDecomposition.transpose`: diagonal reflection of both constituent
  rectangles gives a decomposition between the transposed endpoint states.
* `TauCeti.GridRectangleDecomposition.target_mem_twoStepColumnSwapNeighbors`: the target of a
  decomposition is reached from its source by two nontrivial column transpositions.

## References

This supplies the shared two-step bookkeeping for
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, "The complexes and `∂² = 0`".
The decomposition pairing follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*,
Chapter 4.6.
-/

public section

namespace TauCeti

/-- A decomposition of a two-step rectangle domain from `x` to `z` through an intermediate grid
state. -/
structure GridRectangleDecomposition {n : ℕ} (x z : GridState n) where
  /-- The grid state between the two rectangle moves. -/
  middle : GridState n
  /-- The first oriented rectangle, from the source to the intermediate state. -/
  first : GridRectangleBetween x middle
  /-- The second oriented rectangle, from the intermediate state to the target. -/
  second : GridRectangleBetween middle z

namespace GridRectangleDecomposition

variable {n : ℕ} {x z : GridState n}

/-- Two rectangle decompositions are equal when their ordered side columns agree: the first pair
already determines the intermediate state. -/
@[ext]
theorem ext {D E : GridRectangleDecomposition x z}
    (hfirstLeft : D.first.left = E.first.left)
    (hfirstRight : D.first.right = E.first.right)
    (hsecondLeft : D.second.left = E.second.left)
    (hsecondRight : D.second.right = E.second.right) : D = E := by
  have hmiddle : D.middle = E.middle := by
    rw [D.first.target_eq_swapColumns, hfirstLeft, hfirstRight,
      ← E.first.target_eq_swapColumns]
  cases D with
  | mk Dmiddle Dfirst Dsecond =>
      cases E with
      | mk Emiddle Efirst Esecond =>
          dsimp only at hmiddle
          subst Emiddle
          have hfirst : Dfirst = Efirst :=
            GridRectangleBetween.eq_of_sides hfirstLeft hfirstRight
          subst Efirst
          have hsecond : Dsecond = Esecond :=
            GridRectangleBetween.eq_of_sides hsecondLeft hsecondRight
          subst Esecond
          rfl

/-- The diagonal reflection of a two-step rectangle decomposition. It reflects both constituent
rectangles and the intermediate state, and hence gives a decomposition between the transposed
endpoint states. -/
def transpose (D : GridRectangleDecomposition x z) :
    GridRectangleDecomposition x.transpose z.transpose where
  middle := D.middle.transpose
  first := D.first.transpose
  second := D.second.transpose

/-- The intermediate state of a transposed decomposition is the transposed intermediate state. -/
@[simp]
theorem transpose_middle (D : GridRectangleDecomposition x z) :
    D.transpose.middle = D.middle.transpose := by
  rw [transpose]

/-- The first rectangle of a transposed decomposition has the original initial corner row as its
initial side column. -/
@[simp]
theorem transpose_first_left (D : GridRectangleDecomposition x z) :
    D.transpose.first.left = D.first.bottom := by
  rw [transpose]
  exact D.first.transpose_left

/-- The first rectangle of a transposed decomposition has the original terminal corner row as its
terminal side column. -/
@[simp]
theorem transpose_first_right (D : GridRectangleDecomposition x z) :
    D.transpose.first.right = D.first.top := by
  rw [transpose]
  exact D.first.transpose_right

/-- The first rectangle of a transposed decomposition has the original initial side column as its
initial corner row. -/
@[simp]
theorem transpose_first_bottom (D : GridRectangleDecomposition x z) :
    D.transpose.first.bottom = D.first.left := by
  rw [transpose]
  exact D.first.transpose_bottom

/-- The first rectangle of a transposed decomposition has the original terminal side column as its
terminal corner row. -/
@[simp]
theorem transpose_first_top (D : GridRectangleDecomposition x z) :
    D.transpose.first.top = D.first.right := by
  rw [transpose]
  exact D.first.transpose_top

/-- The second rectangle of a transposed decomposition has the original initial corner row as its
initial side column. -/
@[simp]
theorem transpose_second_left (D : GridRectangleDecomposition x z) :
    D.transpose.second.left = D.second.bottom := by
  rw [transpose]
  exact D.second.transpose_left

/-- The second rectangle of a transposed decomposition has the original terminal corner row as its
terminal side column. -/
@[simp]
theorem transpose_second_right (D : GridRectangleDecomposition x z) :
    D.transpose.second.right = D.second.top := by
  rw [transpose]
  exact D.second.transpose_right

/-- The second rectangle of a transposed decomposition has the original initial side column as its
initial corner row. -/
@[simp]
theorem transpose_second_bottom (D : GridRectangleDecomposition x z) :
    D.transpose.second.bottom = D.second.left := by
  rw [transpose]
  exact D.second.transpose_bottom

/-- The second rectangle of a transposed decomposition has the original terminal side column as
its terminal corner row. -/
@[simp]
theorem transpose_second_top (D : GridRectangleDecomposition x z) :
    D.transpose.second.top = D.second.right := by
  rw [transpose]
  exact D.second.transpose_top

/-- The first rectangle of a transposed decomposition is empty exactly when the original first
rectangle is. -/
@[simp]
theorem isEmpty_transpose_first (D : GridRectangleDecomposition x z) :
    D.transpose.first.IsEmpty ↔ D.first.IsEmpty := by
  rw [transpose]
  exact D.first.isEmpty_transpose

/-- The second rectangle of a transposed decomposition is empty exactly when the original second
rectangle is. -/
@[simp]
theorem isEmpty_transpose_second (D : GridRectangleDecomposition x z) :
    D.transpose.second.IsEmpty ↔ D.second.IsEmpty := by
  rw [transpose]
  exact D.second.isEmpty_transpose

/-- Reflecting a two-step rectangle decomposition twice recovers the original decomposition. -/
@[simp]
theorem transpose_transpose (D : GridRectangleDecomposition x z) : D.transpose.transpose = D := by
  ext <;> simp

/-- The target of a two-step rectangle decomposition is a two-step column-swap neighbour of its
source: each of the two rectangles transposes its pair of distinct side columns. -/
theorem target_mem_twoStepColumnSwapNeighbors (D : GridRectangleDecomposition x z) :
    z ∈ x.twoStepColumnSwapNeighbors :=
  GridState.mem_twoStepColumnSwapNeighbors.mpr
    ⟨D.middle,
      GridState.mem_columnSwapNeighbors.mpr
        ⟨D.first.left, D.first.right, D.first.left_ne_right, D.first.target_eq_swapColumns⟩,
      GridState.mem_columnSwapNeighbors.mpr
        ⟨D.second.left, D.second.right, D.second.left_ne_right, D.second.target_eq_swapColumns⟩⟩

end GridRectangleDecomposition

end TauCeti
