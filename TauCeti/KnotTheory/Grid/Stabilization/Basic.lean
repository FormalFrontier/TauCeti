/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Logic.Equiv.Fin.Rotate
public import TauCeti.KnotTheory.Grid.Diagram.Basic

/-!
# Elementary grid stabilization moves

A grid stabilization inserts one row and one column near a marking. In the resulting local
`2 × 2` block, the chosen marking is split across two opposite corners and one marking of the
other type occupies a third corner. Deleting the new row and column recovers the original
diagram.

This file first gives the two permutation operations underlying this construction.
`GridState.insertPoint` inserts one point at the intersection of the new row and column, while
`GridState.splitPoint` replaces a chosen old point by the other two corners of that local block.
It then constructs stabilizations that split either an `O`- or an `X`-marking.

The predicates `GridDiagram.IsOStabilization` and `GridDiagram.IsXStabilization` require the new
row and column to be cyclically adjacent to the row and column of the split marking. Allowing
either cyclic orientation in each coordinate gives the four corner types for each marking, hence
the eight standard stabilization types. `GridDiagram.IsStabilization` combines the two marking
types, and `GridDiagram.IsDestabilization` reverses the relation.

## Main definitions

* `TauCeti.GridState.insertPoint`: insert a point into a permutation graph.
* `TauCeti.GridState.splitPoint`: split one old point across the other corners of an inserted
  row and column.
* `TauCeti.GridDiagram.stabilizeO`, `TauCeti.GridDiagram.stabilizeX`: the two marking-level
  stabilization constructions.
* `TauCeti.GridDiagram.IsStabilization`, `TauCeti.GridDiagram.IsDestabilization`: elementary
  stabilization and destabilization relations.

## References

This supplies the stabilization half of the standing convention in
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md` that a link is initially a grid diagram
modulo grid moves. The local three-marking construction and its eight types follow
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

public section

namespace TauCeti

namespace GridState

variable {n : ℕ}

/-- Insert a new point `(newColumn, newRow)` into a grid state.

Every old point `(c, x c)` is sent to
`(newColumn.succAbove c, newRow.succAbove (x c))`. -/
def insertPoint (x : GridState n) (newColumn newRow : Fin (n + 1)) : GridState (n + 1) where
  toPerm :=
    (finSuccEquiv' newColumn).trans
      ((Equiv.optionCongr x.toPerm).trans (finSuccEquiv' newRow).symm)

/-- The inserted column contains the inserted row. -/
@[simp]
theorem insertPoint_apply_newColumn (x : GridState n) (newColumn newRow : Fin (n + 1)) :
    x.insertPoint newColumn newRow newColumn = newRow := by
  simp [insertPoint]

/-- An old column contains the embedded image of its old row after inserting a point. -/
@[simp]
theorem insertPoint_apply_succAbove (x : GridState n) (newColumn newRow : Fin (n + 1))
    (c : Fin n) :
    x.insertPoint newColumn newRow (newColumn.succAbove c) =
      newRow.succAbove (x c) := by
  simp [insertPoint]

/-- Split the point in column `splitColumn` across an inserted row and column.

The old point at `(splitColumn, x splitColumn)` is replaced by the two points
`(newColumn, newRow.succAbove (x splitColumn))` and
`(newColumn.succAbove splitColumn, newRow)`. All other old points are embedded as in
`GridState.insertPoint`. -/
def splitPoint (x : GridState n) (newColumn newRow : Fin (n + 1))
    (splitColumn : Fin n) : GridState (n + 1) :=
  (x.insertPoint newColumn newRow).swapColumns newColumn
    (newColumn.succAbove splitColumn)

/-- The new column of a split point contains the embedded old row of the split point. -/
@[simp]
theorem splitPoint_apply_newColumn (x : GridState n) (newColumn newRow : Fin (n + 1))
    (splitColumn : Fin n) :
    x.splitPoint newColumn newRow splitColumn newColumn =
      newRow.succAbove (x splitColumn) := by
  simp [splitPoint]

/-- The embedded old column of a split point contains the new row. -/
@[simp]
theorem splitPoint_apply_splitColumn (x : GridState n) (newColumn newRow : Fin (n + 1))
    (splitColumn : Fin n) :
    x.splitPoint newColumn newRow splitColumn (newColumn.succAbove splitColumn) =
      newRow := by
  simp [splitPoint]

/-- Away from the split column, `splitPoint` embeds old points in the inserted grid. -/
@[simp]
theorem splitPoint_apply_succAbove (x : GridState n) (newColumn newRow : Fin (n + 1))
    (splitColumn c : Fin n) :
    x.splitPoint newColumn newRow splitColumn (newColumn.succAbove c) =
      if c = splitColumn then newRow else newRow.succAbove (x c) := by
  by_cases h : c = splitColumn
  · subst c
    simp
  · rw [splitPoint, swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne (newColumn.succAbove_ne c)
        (fun hc ↦ h (Fin.succAbove_right_injective hc))]
    simpa using h

end GridState

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- Stabilize a grid diagram by splitting the `O`-marking in `splitColumn`.

The `O` state uses the two off-diagonal corners of the inserted row and column, while the new
`X`-marking occupies their intersection. The elementary-move predicate below separately requires
the inserted row and column to be adjacent to the split marking. -/
def stabilizeO (newColumn newRow : Fin (n + 1)) (splitColumn : Fin n) :
    GridDiagram (n + 1) where
  O := G.O.splitPoint newColumn newRow splitColumn
  X := G.X.insertPoint newColumn newRow
  disjoint := by
    intro c
    refine Fin.succAboveCases newColumn ?_ (fun i ↦ ?_) c
    · simpa only [GridState.splitPoint_apply_newColumn,
        GridState.insertPoint_apply_newColumn] using
        newRow.succAbove_ne (G.O splitColumn)
    · by_cases hi : i = splitColumn
      · subst i
        simpa only [GridState.splitPoint_apply_splitColumn,
          GridState.insertPoint_apply_succAbove] using
          (newRow.succAbove_ne (G.X splitColumn)).symm
      · simp only [GridState.splitPoint_apply_succAbove,
          GridState.insertPoint_apply_succAbove, if_neg hi]
        exact fun h ↦ G.disjoint i (Fin.succAbove_right_injective h)

/-- Stabilize a grid diagram by splitting the `X`-marking in `splitColumn`.

The `X` state uses the two off-diagonal corners of the inserted row and column, while the new
`O`-marking occupies their intersection. The elementary-move predicate below separately requires
the inserted row and column to be adjacent to the split marking. -/
def stabilizeX (newColumn newRow : Fin (n + 1)) (splitColumn : Fin n) :
    GridDiagram (n + 1) where
  O := G.O.insertPoint newColumn newRow
  X := G.X.splitPoint newColumn newRow splitColumn
  disjoint := by
    intro c
    refine Fin.succAboveCases newColumn ?_ (fun i ↦ ?_) c
    · simpa only [GridState.insertPoint_apply_newColumn,
        GridState.splitPoint_apply_newColumn] using
        (newRow.succAbove_ne (G.X splitColumn)).symm
    · by_cases hi : i = splitColumn
      · subst i
        simpa only [GridState.insertPoint_apply_succAbove,
          GridState.splitPoint_apply_splitColumn] using
          newRow.succAbove_ne (G.O splitColumn)
      · simp only [GridState.insertPoint_apply_succAbove,
          GridState.splitPoint_apply_succAbove, if_neg hi]
        exact fun h ↦ G.disjoint i (Fin.succAbove_right_injective h)

/-- The `O` state of an `O`-stabilization is obtained by splitting the chosen `O`-marking. -/
@[simp]
theorem stabilizeO_O (newColumn newRow : Fin (n + 1)) (splitColumn : Fin n) :
    (G.stabilizeO newColumn newRow splitColumn).O =
      G.O.splitPoint newColumn newRow splitColumn :=
  (rfl)

/-- The `X` state of an `O`-stabilization is obtained by inserting the new `X`-marking. -/
@[simp]
theorem stabilizeO_X (newColumn newRow : Fin (n + 1)) (splitColumn : Fin n) :
    (G.stabilizeO newColumn newRow splitColumn).X =
      G.X.insertPoint newColumn newRow :=
  (rfl)

/-- The `O` state of an `X`-stabilization is obtained by inserting the new `O`-marking. -/
@[simp]
theorem stabilizeX_O (newColumn newRow : Fin (n + 1)) (splitColumn : Fin n) :
    (G.stabilizeX newColumn newRow splitColumn).O =
      G.O.insertPoint newColumn newRow :=
  (rfl)

/-- The `X` state of an `X`-stabilization is obtained by splitting the chosen `X`-marking. -/
@[simp]
theorem stabilizeX_X (newColumn newRow : Fin (n + 1)) (splitColumn : Fin n) :
    (G.stabilizeX newColumn newRow splitColumn).X =
      G.X.splitPoint newColumn newRow splitColumn :=
  (rfl)

/-- Exchanging the marking types turns an `O`-stabilization into an `X`-stabilization. -/
@[simp]
theorem stabilizeO_swapMarkings (newColumn newRow : Fin (n + 1)) (splitColumn : Fin n) :
    (G.stabilizeO newColumn newRow splitColumn).swapMarkings =
      G.swapMarkings.stabilizeX newColumn newRow splitColumn := by
  ext c <;> simp

/-- Exchanging the marking types turns an `X`-stabilization into an `O`-stabilization. -/
@[simp]
theorem stabilizeX_swapMarkings (newColumn newRow : Fin (n + 1)) (splitColumn : Fin n) :
    (G.stabilizeX newColumn newRow splitColumn).swapMarkings =
      G.swapMarkings.stabilizeO newColumn newRow splitColumn := by
  ext c <;> simp

/-- Two grid diagrams differ by an elementary stabilization that splits an `O`-marking.

The new column is cyclically adjacent to the embedded split column, and the new row is cyclically
adjacent to the embedded row of its `O`-marking. The two disjunctions independently choose the
cyclic orientation, giving the four `O`-stabilization corner types. -/
def IsOStabilization (G : GridDiagram n) (G' : GridDiagram (n + 1)) : Prop :=
  ∃ newColumn newRow splitColumn,
    (finRotate (n + 1) newColumn = newColumn.succAbove splitColumn ∨
      finRotate (n + 1) (newColumn.succAbove splitColumn) = newColumn) ∧
    (finRotate (n + 1) newRow = newRow.succAbove (G.O splitColumn) ∨
      finRotate (n + 1) (newRow.succAbove (G.O splitColumn)) = newRow) ∧
    G' = G.stabilizeO newColumn newRow splitColumn

/-- A local `O`-stabilization construction is an elementary `O`-stabilization. -/
theorem isOStabilization_stabilizeO (newColumn newRow : Fin (n + 1))
    (splitColumn : Fin n)
    (hColumn : finRotate (n + 1) newColumn = newColumn.succAbove splitColumn ∨
      finRotate (n + 1) (newColumn.succAbove splitColumn) = newColumn)
    (hRow : finRotate (n + 1) newRow = newRow.succAbove (G.O splitColumn) ∨
      finRotate (n + 1) (newRow.succAbove (G.O splitColumn)) = newRow) :
    IsOStabilization G (G.stabilizeO newColumn newRow splitColumn) :=
  ⟨newColumn, newRow, splitColumn, hColumn, hRow, rfl⟩

/-- Inserting a column immediately before `splitColumn` and a row immediately before its
`O`-marking gives an elementary `O`-stabilization. -/
theorem isOStabilization_stabilizeO_castSucc (splitColumn : Fin n) :
    IsOStabilization G
      (G.stabilizeO splitColumn.castSucc (G.O splitColumn).castSucc splitColumn) := by
  apply G.isOStabilization_stabilizeO
  · left
    simp
  · left
    simp

/-- Two grid diagrams differ by an elementary stabilization that splits an `X`-marking.

The new column is cyclically adjacent to the embedded split column, and the new row is cyclically
adjacent to the embedded row of its `X`-marking. The two disjunctions independently choose the
cyclic orientation, giving the four `X`-stabilization corner types. -/
def IsXStabilization (G : GridDiagram n) (G' : GridDiagram (n + 1)) : Prop :=
  ∃ newColumn newRow splitColumn,
    (finRotate (n + 1) newColumn = newColumn.succAbove splitColumn ∨
      finRotate (n + 1) (newColumn.succAbove splitColumn) = newColumn) ∧
    (finRotate (n + 1) newRow = newRow.succAbove (G.X splitColumn) ∨
      finRotate (n + 1) (newRow.succAbove (G.X splitColumn)) = newRow) ∧
    G' = G.stabilizeX newColumn newRow splitColumn

/-- A local `X`-stabilization construction is an elementary `X`-stabilization. -/
theorem isXStabilization_stabilizeX (newColumn newRow : Fin (n + 1))
    (splitColumn : Fin n)
    (hColumn : finRotate (n + 1) newColumn = newColumn.succAbove splitColumn ∨
      finRotate (n + 1) (newColumn.succAbove splitColumn) = newColumn)
    (hRow : finRotate (n + 1) newRow = newRow.succAbove (G.X splitColumn) ∨
      finRotate (n + 1) (newRow.succAbove (G.X splitColumn)) = newRow) :
    IsXStabilization G (G.stabilizeX newColumn newRow splitColumn) :=
  ⟨newColumn, newRow, splitColumn, hColumn, hRow, rfl⟩

/-- Inserting a column immediately before `splitColumn` and a row immediately before its
`X`-marking gives an elementary `X`-stabilization. -/
theorem isXStabilization_stabilizeX_castSucc (splitColumn : Fin n) :
    IsXStabilization G
      (G.stabilizeX splitColumn.castSucc (G.X splitColumn).castSucc splitColumn) := by
  apply G.isXStabilization_stabilizeX
  · left
    simp
  · left
    simp

/-- Exchanging the marking types turns an `O`-stabilization relation into an
`X`-stabilization relation. -/
@[simp]
theorem isOStabilization_swapMarkings (G : GridDiagram n)
    (G' : GridDiagram (n + 1)) :
    IsOStabilization G.swapMarkings G'.swapMarkings ↔ IsXStabilization G G' := by
  constructor
  · rintro ⟨newColumn, newRow, splitColumn, hColumn, hRow, hG'⟩
    refine ⟨newColumn, newRow, splitColumn, hColumn, ?_, ?_⟩
    · simpa using hRow
    · simpa using congrArg GridDiagram.swapMarkings hG'
  · rintro ⟨newColumn, newRow, splitColumn, hColumn, hRow, hG'⟩
    refine ⟨newColumn, newRow, splitColumn, hColumn, ?_, ?_⟩
    · simpa using hRow
    · simpa using congrArg GridDiagram.swapMarkings hG'

/-- Exchanging the marking types turns an `X`-stabilization relation into an
`O`-stabilization relation. -/
@[simp]
theorem isXStabilization_swapMarkings (G : GridDiagram n)
    (G' : GridDiagram (n + 1)) :
    IsXStabilization G.swapMarkings G'.swapMarkings ↔ IsOStabilization G G' := by
  simpa only [swapMarkings_swapMarkings] using
    (isOStabilization_swapMarkings G.swapMarkings G'.swapMarkings).symm

/-- One elementary grid stabilization, splitting either an `O`- or an `X`-marking. -/
def IsStabilization (G : GridDiagram n) (G' : GridDiagram (n + 1)) : Prop :=
  IsOStabilization G G' ∨ IsXStabilization G G'

/-- Exchanging the marking types preserves the elementary stabilization relation. -/
@[simp]
theorem isStabilization_swapMarkings (G : GridDiagram n)
    (G' : GridDiagram (n + 1)) :
    IsStabilization G.swapMarkings G'.swapMarkings ↔ IsStabilization G G' := by
  simp only [IsStabilization, isOStabilization_swapMarkings,
    isXStabilization_swapMarkings, or_comm]

/-- One elementary grid destabilization, oriented from the larger diagram to the smaller one. -/
def IsDestabilization (G' : GridDiagram (n + 1)) (G : GridDiagram n) : Prop :=
  IsStabilization G G'

/-- A destabilization from the larger diagram to the smaller one is the reverse orientation of
the corresponding stabilization. -/
theorem isDestabilization_iff (G' : GridDiagram (n + 1)) (G : GridDiagram n) :
    IsDestabilization G' G ↔ IsStabilization G G' :=
  Iff.rfl

/-- Exchanging the marking types preserves the elementary destabilization relation. -/
@[simp]
theorem isDestabilization_swapMarkings (G' : GridDiagram (n + 1))
    (G : GridDiagram n) :
    IsDestabilization G'.swapMarkings G.swapMarkings ↔ IsDestabilization G' G := by
  simpa only [IsDestabilization] using isStabilization_swapMarkings G G'

end GridDiagram

end TauCeti
