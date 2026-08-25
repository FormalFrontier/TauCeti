/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Rectangle.Squares

/-!
# A pair of rectangles returning to its source covers an annulus

A term in the square of a grid differential is a pair of composable oriented rectangles. This
file treats the *annular* case, in which the second rectangle returns to the source of the
first: `R` runs from a grid state `x` to a grid state `y` and `S` runs from `y` back to `x`.

Such a pair is rigid. Both rectangles must use the same two side columns, because those columns
are exactly the columns in which `x` and `y` differ. There are therefore only two shapes. If `S`
starts on the same side column as `R`, then the two rectangles have the same columns and
complementary rows, and together they cover every square in a full vertical band. If `S` starts
on the other side column, then they have the same rows and complementary columns, and together
they cover every square in a full horizontal band. Either way the union of the covered squares is
a toroidal annulus, `GridRectangleBetween.coveredSquares_union_coveredSquares`.

A grid state occupies one square in every column and one square in every row, so it meets every
nonempty vertical band and every nonempty horizontal band
(`GridState.not_disjoint_product_univ_pointSet` and `GridState.not_disjoint_univ_product_pointSet`
of `Diagram/Basic.lean`). Consequently a grid state always meets the union of the squares covered
by a returning pair
(`GridRectangleBetween.not_disjoint_coveredSquares_or_not_disjoint_coveredSquares`).

The region a marking is tested against here is `GridRectangle.coveredSquares`: markings sit at the
centres of their squares, the convention fixed in `Rectangle/Squares.lean` and used by the gradings
and by the unblocked complex `GC⁻`. Applied to the `O`- or the `X`-markings of a grid diagram, both
of which are grid states, the last lemma therefore says that a returning pair of rectangles can
never consist of two rectangles disjoint from the markings' squares, so the annular terms vanish
for any grid differential whose marking-free test is that disjointness — in particular for the
`X`-test of the unblocked differential `∂⁻`. It does not apply as it stands to the fully blocked
differential of `Complex.lean`, whose `GridRectangle.AvoidsMarkings` predicate still tests the open
grid-line interior, treating markings as lattice points rather than as square centres; that is the
acknowledged convention error whose correction is the open TauCeti#3135, and against the corrected
square-centred predicate this lemma will serve the fully blocked case unchanged.

## Main results

* `TauCeti.GridRectangleBetween.sideColumns_eq_sideColumns`: a returning pair of rectangles uses
  the same two side columns.
* `TauCeti.GridRectangleBetween.coveredSquares_union_coveredSquares`: the squares covered by a
  returning pair are a full vertical band or a full horizontal band.
* `TauCeti.GridRectangleBetween.not_disjoint_coveredSquares_or_not_disjoint_coveredSquares`: at
  least one rectangle of a returning pair covers a square occupied by any given grid state.

## References

This supplies the annular case split for
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, "The complexes and `∂² = 0`",
whose juxtaposition argument distinguishes disjoint, overlapping and annular pairs of empty
rectangles. The annular case follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Chapter 4.6.
-/

public section

namespace TauCeti

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n} (R : GridRectangleBetween x y) (S : GridRectangleBetween y x)

/-- The initial side column of a returning rectangle is a side column of the outgoing one: away
from the two side columns of `R` the states `x` and `y` agree, and there `S` could not exchange
two distinct rows. -/
private theorem left_eq_left_or_left_eq_right : S.left = R.left ∨ S.left = R.right := by
  by_cases hl : S.left = R.left
  · exact Or.inl hl
  by_cases hr : S.left = R.right
  · exact Or.inr hr
  have h : y S.left = y S.right := by
    rw [R.map_of_ne S.left hl hr]
    exact S.map_left
  exact absurd (y.toPerm.injective h) S.left_ne_right

/-- The terminal side column of a returning rectangle is a side column of the outgoing one. -/
private theorem right_eq_left_or_right_eq_right : S.right = R.left ∨ S.right = R.right := by
  by_cases hl : S.right = R.left
  · exact Or.inl hl
  by_cases hr : S.right = R.right
  · exact Or.inr hr
  have h : y S.right = y S.left := by
    rw [R.map_of_ne S.right hl hr]
    exact S.map_right
  exact absurd (y.toPerm.injective h).symm S.left_ne_right

/-- If a returning rectangle starts on the same side column as the outgoing one, then it also
ends on the same side column. -/
private theorem right_eq_right_of_left_eq_left (h : S.left = R.left) : S.right = R.right := by
  rcases R.right_eq_left_or_right_eq_right S with h' | h'
  · exact absurd (h.trans h'.symm) S.left_ne_right
  · exact h'

/-- If a returning rectangle starts on the terminal side column of the outgoing one, then it ends
on the initial one. -/
private theorem right_eq_left_of_left_eq_right (h : S.left = R.right) : S.right = R.left := by
  rcases R.right_eq_left_or_right_eq_right S with h' | h'
  · exact h'
  · exact absurd (h.trans h'.symm) S.left_ne_right

/-- A returning pair of rectangles uses the same unordered pair of side columns. -/
theorem sideColumns_eq_sideColumns : S.sideColumns = R.sideColumns := by
  simp only [sideColumns]
  rcases R.left_eq_left_or_left_eq_right S with h | h
  · rw [h, R.right_eq_right_of_left_eq_left S h]
  · rw [h, R.right_eq_left_of_left_eq_right S h, Finset.pair_comm]

/-- A returning rectangle starting on the initial side column starts on the terminal side row:
its two rows are those of the outgoing rectangle, in the opposite order. -/
private theorem bottom_eq_top_of_left_eq_left (h : S.left = R.left) : S.bottom = R.top := by
  rw [bottom_def, h, R.map_left, top_def]

/-- A returning rectangle starting on the initial side column ends on the initial side row. -/
private theorem top_eq_bottom_of_left_eq_left (h : S.left = R.left) : S.top = R.bottom := by
  rw [top_def, R.right_eq_right_of_left_eq_left S h, R.map_right, bottom_def]

/-- A returning rectangle starting on the terminal side column has the same two side rows, in the
same order, as the outgoing one. -/
private theorem bottom_eq_bottom_of_left_eq_right (h : S.left = R.right) : S.bottom = R.bottom := by
  rw [bottom_def, h, R.map_right, bottom_def]

/-- A returning rectangle starting on the terminal side column ends on the terminal side row. -/
private theorem top_eq_top_of_left_eq_right (h : S.left = R.right) : S.top = R.top := by
  rw [top_def, R.right_eq_left_of_left_eq_right S h, R.map_left, top_def]

/-- A returning pair whose two rectangles start on the same side column covers a full vertical
band: the same columns as the outgoing rectangle, and every row. -/
theorem coveredSquares_union_coveredSquares_of_left_eq_left (h : S.left = R.left) :
    R.toGridRectangle.coveredSquares ∪ S.toGridRectangle.coveredSquares =
      R.toGridRectangle.coveredColumns ×ˢ (Finset.univ : Finset (Fin n)) := by
  have hrow : Grid.cIco R.bottom R.top ∪ Grid.cIco R.top R.bottom = Finset.univ :=
    Grid.cIco_union_swap R.bottom_ne_top
  ext p
  simp only [Finset.mem_union, GridRectangle.mem_coveredSquares,
    GridRectangle.mem_coveredColumns, GridRectangle.mem_coveredRows, Finset.mem_product,
    Finset.mem_univ, and_true, toGridRectangle_left, toGridRectangle_right,
    toGridRectangle_bottom, toGridRectangle_top, h, R.right_eq_right_of_left_eq_left S h,
    R.bottom_eq_top_of_left_eq_left S h, R.top_eq_bottom_of_left_eq_left S h]
  refine ⟨fun hp => hp.elim And.left And.left, fun hp => ?_⟩
  have := hrow ▸ Finset.mem_univ p.2
  rcases Finset.mem_union.mp this with hb | hb
  · exact Or.inl ⟨hp, hb⟩
  · exact Or.inr ⟨hp, hb⟩

/-- A returning pair whose second rectangle starts on the other side column covers a full
horizontal band: every column, and the same rows as the outgoing rectangle. -/
theorem coveredSquares_union_coveredSquares_of_left_eq_right (h : S.left = R.right) :
    R.toGridRectangle.coveredSquares ∪ S.toGridRectangle.coveredSquares =
      (Finset.univ : Finset (Fin n)) ×ˢ R.toGridRectangle.coveredRows := by
  have hcol : Grid.cIco R.left R.right ∪ Grid.cIco R.right R.left = Finset.univ :=
    Grid.cIco_union_swap R.left_ne_right
  ext p
  simp only [Finset.mem_union, GridRectangle.mem_coveredSquares,
    GridRectangle.mem_coveredColumns, GridRectangle.mem_coveredRows, Finset.mem_product,
    Finset.mem_univ, true_and, toGridRectangle_left, toGridRectangle_right,
    toGridRectangle_bottom, toGridRectangle_top, h, R.right_eq_left_of_left_eq_right S h,
    R.bottom_eq_bottom_of_left_eq_right S h, R.top_eq_top_of_left_eq_right S h]
  refine ⟨fun hp => hp.elim And.right And.right, fun hp => ?_⟩
  have := hcol ▸ Finset.mem_univ p.1
  rcases Finset.mem_union.mp this with hb | hb
  · exact Or.inl ⟨hb, hp⟩
  · exact Or.inr ⟨hb, hp⟩

/-- The squares covered by a returning pair of rectangles form a toroidal annulus: either a full
vertical band or a full horizontal band. -/
theorem coveredSquares_union_coveredSquares :
    R.toGridRectangle.coveredSquares ∪ S.toGridRectangle.coveredSquares =
        R.toGridRectangle.coveredColumns ×ˢ (Finset.univ : Finset (Fin n)) ∨
      R.toGridRectangle.coveredSquares ∪ S.toGridRectangle.coveredSquares =
        (Finset.univ : Finset (Fin n)) ×ˢ R.toGridRectangle.coveredRows := by
  rcases R.left_eq_left_or_left_eq_right S with h | h
  · exact Or.inl (R.coveredSquares_union_coveredSquares_of_left_eq_left S h)
  · exact Or.inr (R.coveredSquares_union_coveredSquares_of_left_eq_right S h)

/-- A grid state meets the squares covered by a returning pair of rectangles. -/
theorem not_disjoint_union_coveredSquares_pointSet (M : GridState n) :
    ¬Disjoint (R.toGridRectangle.coveredSquares ∪ S.toGridRectangle.coveredSquares)
      M.pointSet := by
  have hcol : R.toGridRectangle.coveredColumns.Nonempty :=
    ⟨R.left, (GridRectangle.mem_coveredColumns _ _).mpr (Grid.left_mem_cIco R.left_ne_right)⟩
  have hrow : R.toGridRectangle.coveredRows.Nonempty :=
    ⟨R.bottom, (GridRectangle.mem_coveredRows _ _).mpr (Grid.left_mem_cIco R.bottom_ne_top)⟩
  rcases R.coveredSquares_union_coveredSquares S with h | h
  · rw [h]
    exact M.not_disjoint_product_univ_pointSet hcol
  · rw [h]
    exact M.not_disjoint_univ_product_pointSet hrow

/-- At least one rectangle of a returning pair covers a square occupied by any given grid state.

Applied to the `O`- or `X`-markings of a grid diagram, this is the vanishing of the annular terms
in the square of a grid differential that tests markings by disjointness from
`GridRectangle.coveredSquares`, such as the unblocked differential `∂⁻`: two rectangles that return
to their source can never both avoid the markings in that sense. The fully blocked differential of
`Complex.lean` is not yet such a differential, since `GridRectangle.AvoidsMarkings` still tests the
open grid-line interior; see the module docstring. -/
theorem not_disjoint_coveredSquares_or_not_disjoint_coveredSquares (M : GridState n) :
    ¬Disjoint R.toGridRectangle.coveredSquares M.pointSet ∨
      ¬Disjoint S.toGridRectangle.coveredSquares M.pointSet := by
  by_cases hR : Disjoint R.toGridRectangle.coveredSquares M.pointSet
  · by_cases hS : Disjoint S.toGridRectangle.coveredSquares M.pointSet
    · exact absurd (Finset.disjoint_union_left.mpr ⟨hR, hS⟩)
        (R.not_disjoint_union_coveredSquares_pointSet S M)
    · exact Or.inr hS
  · exact Or.inl hR

end GridRectangleBetween

end TauCeti
