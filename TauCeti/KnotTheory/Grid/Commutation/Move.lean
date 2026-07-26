/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Logic.Equiv.Fin.Rotate
public import TauCeti.KnotTheory.Grid.Commutation.Relabeling

/-!
# Elementary grid commutation moves

This file packages row and column commutations as relations between grid diagrams. Two columns
are eligible for an elementary commutation when they are cyclically adjacent, their marking
segments are non-interleaving, and the target diagram is obtained by swapping them. Row
commutations are defined dually.

Cyclic adjacency is represented without an extra predicate: an edge of the cyclically ordered
set `Fin n` is the pair `a`, `finRotate n a`. Requiring these endpoints to be distinct excludes
the degenerate one-column identity swap. The resulting relations are symmetric because a swap
is an involution and preserves non-interleaving of the swapped pair.

## Main definitions

* `TauCeti.GridDiagram.IsColumnCommutation`: one elementary column commutation.
* `TauCeti.GridDiagram.IsRowCommutation`: one elementary row commutation.
* `TauCeti.GridDiagram.IsCommutation`: one elementary commutation of either kind.

## Main results

* `TauCeti.GridDiagram.isColumnCommutation_comm` and
  `TauCeti.GridDiagram.isRowCommutation_comm`: elementary moves are reversible.
* `TauCeti.GridDiagram.isRowCommutation_transpose` and
  `TauCeti.GridDiagram.isColumnCommutation_transpose`: diagonal reflection exchanges the two
  kinds of commutation.
* `TauCeti.GridDiagram.isCommutation_comm`: the combined commutation relation is symmetric.

## References

This is a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.5,
"Invariance over 𝔽₂. Grid moves = commutation + (de)stabilization": the later pentagon-counting
chain maps are attached to the elementary moves defined here. The definition follows
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ}

/-- Two grid diagrams differ by one elementary column commutation.

The columns are consecutive in the cyclic order on `Fin n`, have non-interleaving marking
segments in the source diagram, and are swapped to obtain the target diagram. -/
def IsColumnCommutation (G G' : GridDiagram n) : Prop :=
  ∃ a : Fin n, a ≠ finRotate n a ∧
    ColumnsNoninterleaving G a (finRotate n a) ∧
      G' = G.swapColumns a (finRotate n a)

/-- Swapping a cyclically adjacent non-interleaving pair of columns is a column commutation. -/
theorem isColumnCommutation_swapColumns (G : GridDiagram n) (a : Fin n)
    (ha : a ≠ finRotate n a) (hG : ColumnsNoninterleaving G a (finRotate n a)) :
    IsColumnCommutation G (G.swapColumns a (finRotate n a)) :=
  ⟨a, ha, hG, rfl⟩

/-- An elementary column commutation is reversible. -/
theorem isColumnCommutation_comm {G G' : GridDiagram n} :
    IsColumnCommutation G G' ↔ IsColumnCommutation G' G := by
  constructor
  · rintro ⟨a, ha, hnon, rfl⟩
    refine ⟨a, ha, ?_, by simp⟩
    simpa [columnsNoninterleaving_comm] using hnon
  · rintro ⟨a, ha, hnon, rfl⟩
    refine ⟨a, ha, ?_, by simp⟩
    simpa [columnsNoninterleaving_comm] using hnon

/-- Two grid diagrams differ by one elementary row commutation.

The rows are consecutive in the cyclic order on `Fin n`, have non-interleaving marking
segments in the source diagram, and are swapped to obtain the target diagram. -/
def IsRowCommutation (G G' : GridDiagram n) : Prop :=
  ∃ a : Fin n, a ≠ finRotate n a ∧
    RowsNoninterleaving G a (finRotate n a) ∧
      G' = G.swapRows a (finRotate n a)

/-- Swapping a cyclically adjacent non-interleaving pair of rows is a row commutation. -/
theorem isRowCommutation_swapRows (G : GridDiagram n) (a : Fin n)
    (ha : a ≠ finRotate n a) (hG : RowsNoninterleaving G a (finRotate n a)) :
    IsRowCommutation G (G.swapRows a (finRotate n a)) :=
  ⟨a, ha, hG, rfl⟩

/-- An elementary row commutation is reversible. -/
theorem isRowCommutation_comm {G G' : GridDiagram n} :
    IsRowCommutation G G' ↔ IsRowCommutation G' G := by
  constructor
  · rintro ⟨a, ha, hnon, rfl⟩
    refine ⟨a, ha, ?_, by simp⟩
    simpa [rowsNoninterleaving_comm] using hnon
  · rintro ⟨a, ha, hnon, rfl⟩
    refine ⟨a, ha, ?_, by simp⟩
    simpa [rowsNoninterleaving_comm] using hnon

/-- Diagonal reflection turns a row commutation into a column commutation. -/
@[simp]
theorem isRowCommutation_transpose (G G' : GridDiagram n) :
    IsRowCommutation G.transpose G'.transpose ↔ IsColumnCommutation G G' := by
  constructor
  · rintro ⟨a, ha, hnon, hswap⟩
    refine ⟨a, ha, ?_, ?_⟩
    · simpa using hnon
    · have := congrArg GridDiagram.transpose hswap
      simpa using this
  · rintro ⟨a, ha, hnon, hswap⟩
    refine ⟨a, ha, ?_, ?_⟩
    · simpa using hnon
    · simpa using congrArg GridDiagram.transpose hswap

/-- Diagonal reflection turns a column commutation into a row commutation. -/
@[simp]
theorem isColumnCommutation_transpose (G G' : GridDiagram n) :
    IsColumnCommutation G.transpose G'.transpose ↔ IsRowCommutation G G' := by
  constructor
  · rintro ⟨a, ha, hnon, hswap⟩
    refine ⟨a, ha, ?_, ?_⟩
    · simpa using hnon
    · have := congrArg GridDiagram.transpose hswap
      simpa using this
  · rintro ⟨a, ha, hnon, hswap⟩
    refine ⟨a, ha, ?_, ?_⟩
    · simpa using hnon
    · simpa using congrArg GridDiagram.transpose hswap

/-- One elementary grid commutation, either of rows or of columns. -/
def IsCommutation (G G' : GridDiagram n) : Prop :=
  IsRowCommutation G G' ∨ IsColumnCommutation G G'

/-- The elementary grid commutation relation is symmetric. -/
theorem isCommutation_comm {G G' : GridDiagram n} :
    IsCommutation G G' ↔ IsCommutation G' G := by
  unfold IsCommutation
  rw [isRowCommutation_comm,
    isColumnCommutation_comm]

/-- Diagonal reflection preserves the elementary commutation relation, exchanging row and
column moves. -/
@[simp]
theorem isCommutation_transpose (G G' : GridDiagram n) :
    IsCommutation G.transpose G'.transpose ↔ IsCommutation G G' := by
  unfold IsCommutation
  rw [isRowCommutation_transpose, isColumnCommutation_transpose, or_comm]

end GridDiagram

end TauCeti
