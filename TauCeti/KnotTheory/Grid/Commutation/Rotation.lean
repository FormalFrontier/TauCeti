/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CyclicInterval
public import TauCeti.KnotTheory.Grid.Commutation.Basic
public import TauCeti.KnotTheory.Grid.Rotation

/-!
# Rotation and grid commutation arcs

This file records how the row and column arcs used in grid commutation hypotheses transform
under the half-turn rotation of a grid diagram. The commutation API in
`TauCeti.KnotTheory.Grid.Commutation.Basic` defines the oriented vertical and horizontal arcs from
the `O` marking to the `X` marking. Since `Fin.rev` reverses the cyclic order, rotating a diagram
sends these arcs to the reversed images of the corresponding arcs in the marking-swapped diagram.

## Main results

* `TauCeti.GridDiagram.columnArc_rotate` and `TauCeti.GridDiagram.rowArc_rotate`: the oriented
  commutation arcs of the rotated diagram are the `Fin.rev`-images of the opposite oriented arcs
  of the original diagram.
* `TauCeti.GridDiagram.mem_columnArc_rotate` and `TauCeti.GridDiagram.mem_rowArc_rotate`: pointwise
  membership forms of those image formulas.
* `TauCeti.GridDiagram.columnsNoninterleaving_rotate` and
  `TauCeti.GridDiagram.rowsNoninterleaving_rotate`: the commutation hypotheses are transported by
  half-turn rotation.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane
G.5, "Invariance over 𝔽₂. Grid moves = commutation + (de)stabilization", where commutation maps
are built from the row and column marking arcs. The orientation convention follows
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The column arc of the rotated diagram is the coordinate reversal of the opposite oriented
column arc in the original diagram. The `swapMarkings` appears because `Fin.rev` reverses the
cyclic orientation. -/
theorem columnArc_rotate (c : Fin n) :
    columnArc G.rotate c = (columnArc G.swapMarkings c.rev).image Fin.rev := by
  simp [columnArc, Grid.cIoo_image_rev]

/-- Membership in a rotated column arc is membership of the reversed row in the opposite oriented
column arc of the original diagram. -/
theorem mem_columnArc_rotate (c r : Fin n) :
    r ∈ columnArc G.rotate c ↔ r.rev ∈ columnArc G.swapMarkings c.rev := by
  rw [columnArc_rotate, Finset.mem_image]
  constructor
  · rintro ⟨s, hs, hsr⟩
    rwa [← hsr, Fin.rev_rev]
  · intro hr
    exact ⟨r.rev, hr, Fin.rev_rev r⟩

/-- Column non-interleaving is preserved by half-turn rotation, with the cyclic orientation
reversal accounted for by swapping the two marking states. -/
@[simp]
theorem columnsNoninterleaving_rotate (a b : Fin n) :
    ColumnsNoninterleaving G.rotate a b ↔
      ColumnsNoninterleaving G.swapMarkings a.rev b.rev := by
  simpa [ColumnsNoninterleaving] using
    (Grid.noninterleaving_rev (G.O a.rev) (G.X a.rev) (G.O b.rev) (G.X b.rev))

/-- The row arc of the rotated diagram is the coordinate reversal of the opposite oriented row
arc in the original diagram. The `swapMarkings` appears because `Fin.rev` reverses the cyclic
orientation. -/
theorem rowArc_rotate (r : Fin n) :
    rowArc G.rotate r = (rowArc G.swapMarkings r.rev).image Fin.rev := by
  simp [rowArc, Grid.cIoo_image_rev, OColumnOfRow_rotate, XColumnOfRow_rotate]

/-- Membership in a rotated row arc is membership of the reversed column in the opposite oriented
row arc of the original diagram. -/
theorem mem_rowArc_rotate (r c : Fin n) :
    c ∈ rowArc G.rotate r ↔ c.rev ∈ rowArc G.swapMarkings r.rev := by
  rw [rowArc_rotate, Finset.mem_image]
  constructor
  · rintro ⟨s, hs, hsc⟩
    rwa [← hsc, Fin.rev_rev]
  · intro hc
    exact ⟨c.rev, hc, Fin.rev_rev c⟩

/-- Row non-interleaving is preserved by half-turn rotation, with the cyclic orientation reversal
accounted for by swapping the two marking states. -/
@[simp]
theorem rowsNoninterleaving_rotate (a b : Fin n) :
    RowsNoninterleaving G.rotate a b ↔ RowsNoninterleaving G.swapMarkings a.rev b.rev := by
  simpa [RowsNoninterleaving] using
    (Grid.noninterleaving_rev (OColumnOfRow G a.rev) (XColumnOfRow G a.rev)
      (OColumnOfRow G b.rev) (XColumnOfRow G b.rev))

end GridDiagram

end TauCeti
