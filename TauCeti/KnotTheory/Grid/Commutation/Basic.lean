/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CyclicInterval
public import TauCeti.KnotTheory.Grid.Diagram.Basic

/-!
# Grid diagram commutation moves

This file starts the commutation-move API for grid diagrams. The total row and column swap
operations used as underlying relabelings live in `TauCeti.KnotTheory.Grid.Diagram.Basic`, next to
the general row and column relabeling API. Here we add the move-specific hypothesis: two rows or
columns are commutable when their marking segments do not interleave around the torus.

For columns, the vertical segment in column `c` has endpoints `G.O c` and `G.X c`, and two columns
are non-interleaving when each pair of endpoints lies on one side of the other column's endpoint
pair. The row version is the same definition after reading, in each row, the unique columns
containing the `O` and `X` markings.

The predicates are intentionally just the combinatorial hypotheses. The pentagon-counting maps
and chain homotopies for commutation invariance are later Lane G.5 targets.

## Main definitions

* `TauCeti.GridDiagram.columnArc`: the open cyclic interval between the two markings in a column.
* `TauCeti.GridDiagram.rowArc`: the open cyclic interval between the two markings in a row.
* `TauCeti.GridDiagram.ColumnsNoninterleaving`: the hypothesis for a column commutation.
* `TauCeti.GridDiagram.RowsNoninterleaving`: the hypothesis for a row commutation.

## Main results

* `TauCeti.GridDiagram.columnsNoninterleaving_comm` and
  `TauCeti.GridDiagram.rowsNoninterleaving_comm`: non-interleaving is symmetric in the two rows or
  columns.
* `TauCeti.GridDiagram.rowsNoninterleaving_transpose` and
  `TauCeti.GridDiagram.columnsNoninterleaving_transpose`: diagonal reflection exchanges row and
  column non-interleaving.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.5,
"Invariance over `𝔽₂`. Grid moves = commutation + (de)stabilization." It isolates the
non-interleaving condition for row and column commutations in the grid homology construction of
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

@[expose] public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The open vertical arc from the `O` marking to the `X` marking in a column of a grid diagram.

This is the one-dimensional cyclic interval in the row coordinate. Its opposite arc is obtained by
swapping the two markings, not by changing the column. -/
noncomputable def columnArc (c : Fin n) : Finset (Fin n) :=
  Grid.cIoo (G.O c) (G.X c)

/-- Membership in a column arc is membership in the open cyclic interval from that column's `O`
row to its `X` row. -/
@[simp]
theorem mem_columnArc (c r : Fin n) : r ∈ columnArc G c ↔ r ∈ Grid.cIoo (G.O c) (G.X c) :=
  Iff.rfl

/-- The `O` endpoint of a column is not in its own open column arc. -/
theorem O_notMem_columnArc (c : Fin n) : G.O c ∉ columnArc G c := by
  simp [columnArc]

/-- The `X` endpoint of a column is not in its own open column arc. -/
theorem X_notMem_columnArc (c : Fin n) : G.X c ∉ columnArc G c := by
  simp [columnArc]

/-- The open horizontal arc from the `O` marking to the `X` marking in a row of a grid diagram.

This is the column-coordinate version of `columnArc`: it starts at the unique column containing
the row's `O` marking and ends at the unique column containing the row's `X` marking. -/
noncomputable def rowArc (r : Fin n) : Finset (Fin n) :=
  Grid.cIoo (OColumnOfRow G r) (XColumnOfRow G r)

/-- Membership in a row arc is membership in the open cyclic interval from that row's `O` column
to its `X` column. -/
@[simp]
theorem mem_rowArc (r c : Fin n) :
    c ∈ rowArc G r ↔ c ∈ Grid.cIoo (OColumnOfRow G r) (XColumnOfRow G r) :=
  Iff.rfl

/-- The `O` endpoint of a row is not in its own open row arc. -/
theorem OColumn_notMem_rowArc (r : Fin n) : OColumnOfRow G r ∉ rowArc G r := by
  simp [rowArc]

/-- The `X` endpoint of a row is not in its own open row arc. -/
theorem XColumn_notMem_rowArc (r : Fin n) : XColumnOfRow G r ∉ rowArc G r := by
  simp [rowArc]

/-- Two columns of a grid diagram have non-interleaving marking segments.

The condition is phrased in both directions: the two endpoints in column `a` lie on the same side
of the endpoint pair in column `b`, and conversely. This symmetric form is robust in degenerate
row-sharing cases, where one endpoint of a segment may have the same row coordinate as an endpoint
of the other segment. -/
def ColumnsNoninterleaving (a b : Fin n) : Prop :=
  Grid.Noninterleaving (G.O a) (G.X a) (G.O b) (G.X b)

/-- Two rows of a grid diagram have non-interleaving marking segments. -/
def RowsNoninterleaving (a b : Fin n) : Prop :=
  Grid.Noninterleaving (OColumnOfRow G a) (XColumnOfRow G a)
    (OColumnOfRow G b) (XColumnOfRow G b)

/-- The defining endpoint-side conditions for column non-interleaving. -/
theorem columnsNoninterleaving_iff (a b : Fin n) :
    ColumnsNoninterleaving G a b ↔
      (G.O a ∈ columnArc G b ↔ G.X a ∈ columnArc G b) ∧
        (G.O b ∈ columnArc G a ↔ G.X b ∈ columnArc G a) := by
  rfl

/-- The defining endpoint-side conditions for row non-interleaving. -/
theorem rowsNoninterleaving_iff (a b : Fin n) :
    RowsNoninterleaving G a b ↔
      (OColumnOfRow G a ∈ rowArc G b ↔ XColumnOfRow G a ∈ rowArc G b) ∧
        (OColumnOfRow G b ∈ rowArc G a ↔ XColumnOfRow G b ∈ rowArc G a) := by
  rfl

/-- A column is non-interleaving with itself. -/
@[simp]
theorem columnsNoninterleaving_self (a : Fin n) : ColumnsNoninterleaving G a a := by
  simp [ColumnsNoninterleaving]

/-- A row is non-interleaving with itself. -/
@[simp]
theorem rowsNoninterleaving_self (a : Fin n) : RowsNoninterleaving G a a := by
  simp [RowsNoninterleaving]

/-- Column non-interleaving is symmetric in the two columns. -/
theorem columnsNoninterleaving_comm {a b : Fin n} :
    ColumnsNoninterleaving G a b ↔ ColumnsNoninterleaving G b a := by
  exact Grid.noninterleaving_comm

/-- Row non-interleaving is symmetric in the two rows. -/
theorem rowsNoninterleaving_comm {a b : Fin n} :
    RowsNoninterleaving G a b ↔ RowsNoninterleaving G b a := by
  exact Grid.noninterleaving_comm

/-- Diagonal reflection turns the row arc in the reflected diagram into the column arc in the
original diagram. -/
@[simp]
theorem rowArc_transpose (c : Fin n) : rowArc G.transpose c = columnArc G c := by
  simp [rowArc, columnArc]

/-- Diagonal reflection turns the column arc in the reflected diagram into the row arc in the
original diagram. -/
@[simp]
theorem columnArc_transpose (r : Fin n) : columnArc G.transpose r = rowArc G r := by
  simp only [columnArc, rowArc, transpose_O_apply, transpose_X_apply]

/-- Diagonal reflection exchanges row non-interleaving with column non-interleaving. -/
@[simp]
theorem rowsNoninterleaving_transpose (a b : Fin n) :
    RowsNoninterleaving G.transpose a b ↔ ColumnsNoninterleaving G a b :=
  by simp [RowsNoninterleaving, ColumnsNoninterleaving]

/-- Diagonal reflection exchanges column non-interleaving with row non-interleaving. -/
@[simp]
theorem columnsNoninterleaving_transpose (a b : Fin n) :
    ColumnsNoninterleaving G.transpose a b ↔ RowsNoninterleaving G a b :=
  by
    simp only [RowsNoninterleaving, ColumnsNoninterleaving, transpose_O_apply, transpose_X_apply]

end GridDiagram

end TauCeti
