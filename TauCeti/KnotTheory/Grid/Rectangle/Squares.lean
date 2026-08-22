/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Rectangle.Basic

/-!
# The squares a toroidal rectangle covers

A toroidal grid rectangle has two different finite domains, and the grid gradings need both.
Its corners are grid points, that is, intersections of grid lines, and the grid points strictly
inside it are `GridRectangle.interior`, the product of the two open cyclic intervals: this is the
domain against which a grid state is tested for emptiness. The `O`- and `X`-markings, however,
sit at the centres of squares, so a marked square lies inside the rectangle exactly when its
index lies in the **half-open** cyclic interval in each direction. That domain is
`GridRectangle.coveredSquares`, the product of the two half-open arcs
`Grid.cIco left right` and `Grid.cIco bottom top`.

When the vertical sides differ, `coveredSquares` includes the initial column in addition to the
open column interval; when they coincide, both column sets are empty. The analogous statement
holds for rows. `GridRectangle.interior_subset_coveredSquares` records the resulting inclusion
without a nondegeneracy hypothesis.

The convention that markings sit at the centres of their squares is the one the Maslov and
Alexander gradings already use (`JFunction/Center.lean`); this file supplies the matching
rectangle domain, which `Grading/MarkingCount.lean` then uses to turn the Maslov and Alexander
grading changes across a rectangle move into marking counts. The Lane G.3 differential predicate
`GridRectangle.AvoidsMarkings` still tests the grid-line interior and is left untouched here;
aligning it with the square-centred convention is a separate correction to that predicate and to
everything it feeds.

## Main definitions

* `TauCeti.GridRectangle.coveredColumns`, `TauCeti.GridRectangle.coveredRows`: the columns and
  rows of squares a toroidal rectangle covers.
* `TauCeti.GridRectangle.coveredSquares`: the squares a toroidal rectangle covers.

## Main results

* `TauCeti.GridRectangle.interior_subset_coveredSquares`: every grid point strictly inside a
  rectangle names a square the rectangle covers.
* `TauCeti.GridRectangle.card_coveredSquares`: the number of covered squares is the product of the
  two arc lengths.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.2,
"Gradings. The `J`-function, `M_O`, `M_X`, `A`; integer-valuedness of `A`; grading-change formulas
across a rectangle." The placement of the markings at the centres of their squares, and hence the
half-open shape of the domain they are counted in, follows Ozsváth--Stipsicz--Szabó, *Grid
Homology for Knots and Links*, Chapters 3.1--3.2 and 4.1.
-/

public section

namespace TauCeti

namespace GridRectangle

variable {n : ℕ} (R : GridRectangle n)

/-- The columns of squares covered by a toroidal grid rectangle: the clockwise half-open arc
from the initial vertical side to the terminal one. -/
noncomputable def coveredColumns : Finset (Fin n) :=
  Grid.cIco R.left R.right

/-- The rows of squares covered by a toroidal grid rectangle: the clockwise half-open arc from
the initial horizontal side to the terminal one. -/
noncomputable def coveredRows : Finset (Fin n) :=
  Grid.cIco R.bottom R.top

/-- Membership in the covered columns is membership in the corresponding half-open circular
interval. -/
@[simp]
theorem mem_coveredColumns (c : Fin n) : c ∈ R.coveredColumns ↔ c ∈ Grid.cIco R.left R.right :=
  Iff.rfl

/-- Membership in the covered rows is membership in the corresponding half-open circular
interval. -/
@[simp]
theorem mem_coveredRows (r : Fin n) : r ∈ R.coveredRows ↔ r ∈ Grid.cIco R.bottom R.top :=
  Iff.rfl

/-- Every interior column is a covered column. For distinct vertical sides the covered columns
also contain the initial column; for coincident sides both sets are empty. -/
theorem columnInterior_subset_coveredColumns : R.columnInterior ⊆ R.coveredColumns :=
  Grid.cIoo_subset_cIco R.left R.right

/-- Every interior row is a covered row. For distinct horizontal sides the covered rows also
contain the initial row; for coincident sides both sets are empty. -/
theorem rowInterior_subset_coveredRows : R.rowInterior ⊆ R.coveredRows :=
  Grid.cIoo_subset_cIco R.bottom R.top

/-- The number of covered columns, expressed in the standard representatives of the sides. -/
@[simp]
theorem card_coveredColumns :
    R.coveredColumns.card =
      if R.left = R.right then 0
      else if R.left.val < R.right.val then R.right.val - R.left.val
      else n - R.left.val + R.right.val := by
  rw [coveredColumns, Grid.card_cIco]

/-- The number of covered rows, expressed in the standard representatives of the sides. -/
@[simp]
theorem card_coveredRows :
    R.coveredRows.card =
      if R.bottom = R.top then 0
      else if R.bottom.val < R.top.val then R.top.val - R.bottom.val
      else n - R.bottom.val + R.top.val := by
  rw [coveredRows, Grid.card_cIco]

/-- The finite set of squares a toroidal grid rectangle covers.

A marking sits at the centre of its square, so it lies inside the rectangle exactly when its
column and row indices lie in the two half-open arcs. -/
noncomputable def coveredSquares : Finset (Fin n × Fin n) :=
  R.coveredColumns ×ˢ R.coveredRows

/-- The covered squares are the product of the covered columns and rows. -/
theorem coveredSquares_def : R.coveredSquares = R.coveredColumns ×ˢ R.coveredRows :=
  (rfl)

/-- Membership in the covered squares is membership in both one-dimensional half-open arcs. -/
@[simp]
theorem mem_coveredSquares (p : Fin n × Fin n) :
    p ∈ R.coveredSquares ↔ p.1 ∈ R.coveredColumns ∧ p.2 ∈ R.coveredRows := by
  simp [coveredSquares]

/-- Every grid point strictly inside a rectangle names a square that the rectangle covers. -/
theorem interior_subset_coveredSquares : R.interior ⊆ R.coveredSquares :=
  Finset.product_subset_product R.columnInterior_subset_coveredColumns
    R.rowInterior_subset_coveredRows

/-- The number of covered squares is the product of the numbers of covered columns and covered
rows. -/
@[simp]
theorem card_coveredSquares :
    R.coveredSquares.card = R.coveredColumns.card * R.coveredRows.card := by
  simp [coveredSquares, Finset.card_product]

end GridRectangle

end TauCeti
