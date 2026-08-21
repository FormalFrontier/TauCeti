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
`GridRectangle.squares`, the product of the two half-open arcs
`Grid.cIco left right` and `Grid.cIco bottom top`.

The two domains are genuinely different: `squares` has one more column and one more row than
`interior`, namely the initial ones. `GridRectangle.interior_subset_squares` records the
inclusion.

The convention that markings sit at the centres of their squares is the one the Maslov and
Alexander gradings already use (`JFunction/Center.lean`); this file supplies the matching
rectangle domain, which `Grading/MarkingCount.lean` then uses to turn the Maslov and Alexander
grading changes across a rectangle move into marking counts. The Lane G.3 differential predicate
`GridRectangle.AvoidsMarkings` still tests the grid-line interior and is left untouched here;
aligning it with the square-centred convention is a separate correction to that predicate and to
everything it feeds.

## Main definitions

* `TauCeti.GridRectangle.columnSpan`, `TauCeti.GridRectangle.rowSpan`: the columns and the rows
  of squares a toroidal rectangle covers.
* `TauCeti.GridRectangle.squares`: the squares a toroidal rectangle covers.

## Main results

* `TauCeti.GridRectangle.interior_subset_squares`: every grid point strictly inside a rectangle
  names a square the rectangle covers.
* `TauCeti.GridRectangle.card_squares`: the number of covered squares is the product of the two
  arc lengths.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.2,
"Gradings. The `J`-function, `M_O`, `M_X`, `A`; integer-valuedness of `A`; grading-change formulas
across a rectangle." The placement of the markings at the centres of their squares, and hence the
half-open shape of the domain they are counted in, follows Ozsváth--Stipsicz--Szabó, *Grid
Homology for Knots and Links*, Chapters 3.1--3.2 and 4.1.
-/

@[expose] public section

namespace TauCeti

namespace GridRectangle

variable {n : ℕ} (R : GridRectangle n)

/-- The columns of squares covered by a toroidal grid rectangle: the clockwise half-open arc
from the initial vertical side to the terminal one. -/
noncomputable def columnSpan : Finset (Fin n) :=
  Grid.cIco R.left R.right

/-- The rows of squares covered by a toroidal grid rectangle: the clockwise half-open arc from
the initial horizontal side to the terminal one. -/
noncomputable def rowSpan : Finset (Fin n) :=
  Grid.cIco R.bottom R.top

/-- Membership in the covered columns is membership in the corresponding half-open circular
interval. -/
@[simp]
theorem mem_columnSpan (c : Fin n) : c ∈ R.columnSpan ↔ c ∈ Grid.cIco R.left R.right :=
  Iff.rfl

/-- Membership in the covered rows is membership in the corresponding half-open circular
interval. -/
@[simp]
theorem mem_rowSpan (r : Fin n) : r ∈ R.rowSpan ↔ r ∈ Grid.cIco R.bottom R.top :=
  Iff.rfl

/-- The interior columns are covered columns: only the initial vertical side is added. -/
theorem columnInterior_subset_columnSpan : R.columnInterior ⊆ R.columnSpan :=
  Grid.cIoo_subset_cIco R.left R.right

/-- The interior rows are covered rows: only the initial horizontal side is added. -/
theorem rowInterior_subset_rowSpan : R.rowInterior ⊆ R.rowSpan :=
  Grid.cIoo_subset_cIco R.bottom R.top

/-- The finite set of squares a toroidal grid rectangle covers.

A marking sits at the centre of its square, so it lies inside the rectangle exactly when its
column and row indices lie in the two half-open arcs. -/
noncomputable def squares : Finset (Fin n × Fin n) :=
  R.columnSpan ×ˢ R.rowSpan

/-- Membership in the covered squares is membership in both one-dimensional half-open arcs. -/
@[simp]
theorem mem_squares (p : Fin n × Fin n) :
    p ∈ R.squares ↔ p.1 ∈ R.columnSpan ∧ p.2 ∈ R.rowSpan := by
  simp [squares]

/-- A square is covered exactly when its column and row lie in the corresponding half-open
cyclic intervals. -/
theorem mk_mem_squares (c r : Fin n) :
    (c, r) ∈ R.squares ↔ c ∈ Grid.cIco R.left R.right ∧ r ∈ Grid.cIco R.bottom R.top := by
  simp

/-- Every grid point strictly inside a rectangle names a square that the rectangle covers. -/
theorem interior_subset_squares : R.interior ⊆ R.squares :=
  Finset.product_subset_product R.columnInterior_subset_columnSpan R.rowInterior_subset_rowSpan

/-- A rectangle covers no square if its two vertical sides coincide. -/
@[simp]
theorem squares_eq_empty_of_left_eq_right (h : R.left = R.right) : R.squares = ∅ := by
  simp [squares, columnSpan, h]

/-- A rectangle covers no square if its two horizontal sides coincide. -/
@[simp]
theorem squares_eq_empty_of_bottom_eq_top (h : R.bottom = R.top) : R.squares = ∅ := by
  simp [squares, rowSpan, h]

/-- The number of covered squares is the product of the numbers of covered columns and covered
rows. -/
@[simp]
theorem card_squares : R.squares.card = R.columnSpan.card * R.rowSpan.card := by
  simp [squares, Finset.card_product]

end GridRectangle

end TauCeti
