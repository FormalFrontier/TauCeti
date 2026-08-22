/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod
public import TauCeti.KnotTheory.Grid.CyclicInterval
public import TauCeti.KnotTheory.Grid.Diagram.Basic
public import TauCeti.KnotTheory.Grid.Rotation

/-!
# Rectangles in grid diagrams

This file adds the first rectangle API for the grid-combinatorial lane of the Heegaard Floer
roadmap. The grid lives on a torus, so the basic one-dimensional ingredient is the open-open
circular interval in `Fin n`. A grid rectangle is then the product of two such intervals,
recorded as the finite set of squares in its interior.

The final section packages an oriented rectangle from one grid state to another: two columns
where the states exchange rows, and agreement everywhere else. This is the shape counted by
the grid differential; the `IsEmptyFor` and `AvoidsMarkings` predicates record the two
finite-set disjointness conditions used for empty rectangles and marking-avoiding rectangles.

`AvoidsMarkings` currently uses the same open grid-line interior as `IsEmptyFor`. Thus it treats
marking indices as lattice points, not as the southwest corners of square-centred markings. The
Lane G.2 grading correction does not silently change this Lane G.3 differential convention;
changing it requires a separate update of the blocked-rectangle and small-grid differential API.

## Main definitions

* `TauCeti.GridRectangle`: a toroidal rectangle, represented by its four cyclic sides.
* `TauCeti.GridRectangle.symm`: the opposite toroidal rectangle with side columns reversed.
* `TauCeti.GridRectangle.transpose`: the diagonal reflection of a toroidal rectangle, exchanging
  the column and row sides.
* `TauCeti.GridRectangle.rotate`: the half-turn rotation of a toroidal rectangle, reversing both
  coordinates.
* `TauCeti.GridRectangle.interior`: the finite set of squares strictly inside the rectangle.
* `TauCeti.GridRectangleBetween`: an oriented rectangle from one grid state to another.
* `TauCeti.GridRectangleBetween.symm`: the opposite oriented rectangle from `y` to `x`.
* `TauCeti.GridRectangleBetween.swapSides`: the complementary oriented rectangle from `x` to `y`
  with its two side columns exchanged.
* `TauCeti.GridRectangleBetween.transpose`: the diagonal reflection of an oriented rectangle, from
  `x.transpose` to `y.transpose`.
* `TauCeti.GridRectangleBetween.transposeEquiv`: the diagonal reflection packaged as an involutive
  equivalence with oriented rectangles from `x.transpose` to `y.transpose`.
* `TauCeti.GridRectangleBetween.rotate`: the half-turn rotation of an oriented rectangle, from
  `x.rotate` to `y.rotate`.
* `TauCeti.GridRectangleBetween.rotateEquiv`: the half-turn rotation packaged as an equivalence
  with oriented rectangles from `x.rotate` to `y.rotate`.
* `TauCeti.GridRectangleBetween.all`: all oriented rectangles from `x` to `y`.
* `TauCeti.GridRectangleBetween.emptyRectangles`: the empty rectangles from `x` to `y`.

## References

This supplies a prerequisite for the Tau Ceti Heegaard Floer roadmap,
`HeegaardFloer/README.md` in TauCetiRoadmap. Lane G.1, "Grid diagrams and grid states",
asks for rectangles and empty rectangles `Rect°(x, y)`, and Lane G.3, "The complexes and
`∂² = 0`", uses the opposite-rectangle bookkeeping in the rectangle-pairing arguments. The
encoding follows the toroidal grid-diagram convention from Ozsváth--Stipsicz--Szabó, *Grid
Homology for Knots and Links*, Chapter 3.
-/

@[expose] public section

namespace TauCeti

/-- A toroidal grid rectangle, represented by its oriented column and row sides.

The interior is the product of the clockwise open interval from `left` to `right` with the
clockwise open interval from `bottom` to `top`. Degenerate side choices are allowed at this
level; their interiors are empty in the degenerate direction. -/
structure GridRectangle (n : ℕ) where
  /-- The initial vertical side of the rectangle. -/
  left : Fin n
  /-- The terminal vertical side of the rectangle. -/
  right : Fin n
  /-- The initial horizontal side of the rectangle. -/
  bottom : Fin n
  /-- The terminal horizontal side of the rectangle. -/
  top : Fin n

namespace GridRectangle

variable {n : ℕ} (R : GridRectangle n)

/-- The opposite toroidal rectangle, obtained by reversing the two vertical sides while
keeping the horizontal sides fixed. -/
def symm : GridRectangle n where
  left := R.right
  right := R.left
  bottom := R.bottom
  top := R.top

/-- The opposite rectangle's left side is the original right side. -/
@[simp]
theorem symm_left : R.symm.left = R.right :=
  rfl

/-- The opposite rectangle's right side is the original left side. -/
@[simp]
theorem symm_right : R.symm.right = R.left :=
  rfl

/-- The opposite rectangle has the same bottom row. -/
@[simp]
theorem symm_bottom : R.symm.bottom = R.bottom :=
  rfl

/-- The opposite rectangle has the same top row. -/
@[simp]
theorem symm_top : R.symm.top = R.top :=
  rfl

/-- Reversing a toroidal rectangle twice gives the original rectangle. -/
@[simp]
theorem symm_symm : R.symm.symm = R := by
  cases R
  rfl

/-- The columns strictly inside a toroidal grid rectangle. -/
noncomputable def columnInterior : Finset (Fin n) :=
  Grid.cIoo R.left R.right

/-- The rows strictly inside a toroidal grid rectangle. -/
noncomputable def rowInterior : Finset (Fin n) :=
  Grid.cIoo R.bottom R.top

/-- Membership in the interior columns is membership in the corresponding open-open circular
interval. -/
@[simp]
theorem mem_columnInterior (c : Fin n) :
    c ∈ R.columnInterior ↔ c ∈ Grid.cIoo R.left R.right := by
  rfl

/-- Membership in the interior rows is membership in the corresponding open-open circular
interval. -/
@[simp]
theorem mem_rowInterior (r : Fin n) :
    r ∈ R.rowInterior ↔ r ∈ Grid.cIoo R.bottom R.top := by
  rfl

/-- The left side is not an interior column. -/
theorem left_notMem_columnInterior : R.left ∉ R.columnInterior := by
  simp [columnInterior]

/-- The right side is not an interior column. -/
theorem right_notMem_columnInterior : R.right ∉ R.columnInterior := by
  simp [columnInterior]

/-- The bottom side is not an interior row. -/
theorem bottom_notMem_rowInterior : R.bottom ∉ R.rowInterior := by
  simp [rowInterior]

/-- The top side is not an interior row. -/
theorem top_notMem_rowInterior : R.top ∉ R.rowInterior := by
  simp [rowInterior]

/-- The finite set of squares strictly inside a toroidal grid rectangle. -/
noncomputable def interior : Finset (Fin n × Fin n) :=
  R.columnInterior ×ˢ R.rowInterior

/-- Membership in a rectangle interior is membership in both one-dimensional open intervals. -/
@[simp]
theorem mem_interior (p : Fin n × Fin n) :
    p ∈ R.interior ↔ p.1 ∈ R.columnInterior ∧ p.2 ∈ R.rowInterior := by
  simp [interior]

/-- A coordinate pair lies in the rectangle interior exactly when its column and row lie in
the corresponding open cyclic intervals. -/
theorem mk_mem_interior (c r : Fin n) :
    (c, r) ∈ R.interior ↔ c ∈ R.columnInterior ∧ r ∈ R.rowInterior := by
  simp

/-- A rectangle has empty interior if its two column sides coincide. -/
@[simp]
theorem interior_eq_empty_of_left_eq_right (h : R.left = R.right) : R.interior = ∅ := by
  ext p
  simp [interior, columnInterior, h]

/-- A rectangle has empty interior if its two row sides coincide. -/
@[simp]
theorem interior_eq_empty_of_bottom_eq_top (h : R.bottom = R.top) : R.interior = ∅ := by
  ext p
  simp [interior, rowInterior, h]

/-- The number of interior squares is the product of the numbers of interior columns and
interior rows. -/
@[simp]
theorem card_interior :
    R.interior.card = R.columnInterior.card * R.rowInterior.card := by
  simp [interior, Finset.card_product]

/-- In a grid of size at most two, every toroidal rectangle has empty interior. -/
theorem interior_eq_empty_of_le_two (hn : n ≤ 2) (R : GridRectangle n) : R.interior = ∅ := by
  ext p
  simp [interior, columnInterior, Grid.cIoo_eq_empty_of_le_two hn R.left R.right]

/-- A rectangle is empty for a grid state when the state has no point in its interior. -/
def IsEmptyFor (x : GridState n) : Prop :=
  Disjoint R.interior x.pointSet

/-- A rectangle is empty for a grid state exactly when no point of the state lies in its
interior. -/
theorem isEmptyFor_iff (x : GridState n) :
    R.IsEmptyFor x ↔ ∀ p ∈ x.pointSet, p ∉ R.interior := by
  rw [IsEmptyFor, disjoint_comm, Finset.disjoint_iff_ne]
  constructor
  · intro h p hp hpR
    exact h p hp p hpR rfl
  · intro h p hp q hq hpq
    subst hpq
    exact h p hp hq

/-- In a grid of size at most two, every toroidal rectangle is empty for every grid state. -/
theorem isEmptyFor_of_le_two (hn : n ≤ 2) (R : GridRectangle n) (x : GridState n) :
    R.IsEmptyFor x := by
  rw [IsEmptyFor, R.interior_eq_empty_of_le_two hn]
  simp

/-- A rectangle avoids the markings of a grid diagram when its open grid-line interior contains
no `O` or `X` marking index. This is the existing differential convention; unlike the grading
pairing, it does not yet interpret the index as the southwest corner of a square-centred
marking. -/
def AvoidsMarkings (G : GridDiagram n) : Prop :=
  Disjoint R.interior (G.OSet ∪ G.XSet)

/-- A marking-avoiding rectangle has no `O` marking in its interior. -/
theorem disjoint_interior_OSet_of_avoidsMarkings {G : GridDiagram n}
    (h : R.AvoidsMarkings G) : Disjoint R.interior G.OSet :=
  h.mono_right Finset.subset_union_left

/-- A marking-avoiding rectangle has no `X` marking in its interior. -/
theorem disjoint_interior_XSet_of_avoidsMarkings {G : GridDiagram n}
    (h : R.AvoidsMarkings G) : Disjoint R.interior G.XSet :=
  h.mono_right Finset.subset_union_right

/-- A rectangle avoids markings exactly when neither the `O` nor the `X` marking set meets
its interior. -/
theorem avoidsMarkings_iff (G : GridDiagram n) :
    R.AvoidsMarkings G ↔
      Disjoint R.interior G.OSet ∧ Disjoint R.interior G.XSet := by
  rw [AvoidsMarkings, Finset.disjoint_union_right]

/-- In a grid of size at most two, every toroidal rectangle avoids every diagram's markings. -/
theorem avoidsMarkings_of_le_two (hn : n ≤ 2) (R : GridRectangle n) (G : GridDiagram n) :
    R.AvoidsMarkings G := by
  rw [AvoidsMarkings, R.interior_eq_empty_of_le_two hn]
  simp

/-- Marking avoidance is unchanged by swapping the `O` and `X` markings, since it only refers to
the union of the two marking sets. -/
theorem avoidsMarkings_swapMarkings (G : GridDiagram n) :
    R.AvoidsMarkings G.swapMarkings ↔ R.AvoidsMarkings G := by
  rw [avoidsMarkings_iff, avoidsMarkings_iff, GridDiagram.swapMarkings_OSet,
    GridDiagram.swapMarkings_XSet]
  exact and_comm

/-- The diagonal reflection of a toroidal rectangle, exchanging the two vertical sides with the
two horizontal sides.

Reflecting across the main diagonal turns columns into rows and rows into columns, so the
interior is reflected by `Prod.swap`. -/
def transpose : GridRectangle n where
  left := R.bottom
  right := R.top
  bottom := R.left
  top := R.right

/-- The reflected rectangle's left side is the original bottom side. -/
@[simp]
theorem transpose_left : R.transpose.left = R.bottom :=
  rfl

/-- The reflected rectangle's right side is the original top side. -/
@[simp]
theorem transpose_right : R.transpose.right = R.top :=
  rfl

/-- The reflected rectangle's bottom side is the original left side. -/
@[simp]
theorem transpose_bottom : R.transpose.bottom = R.left :=
  rfl

/-- The reflected rectangle's top side is the original right side. -/
@[simp]
theorem transpose_top : R.transpose.top = R.right :=
  rfl

/-- Reflecting a toroidal rectangle twice gives the original rectangle. -/
@[simp]
theorem transpose_transpose : R.transpose.transpose = R := by
  cases R
  rfl

/-- The interior of the reflected rectangle is the diagonal reflection of the original
interior. -/
theorem interior_transpose : R.transpose.interior = R.interior.image Prod.swap :=
  (Finset.image_swap_product _ _).symm

/-- The half-turn rotation of a toroidal rectangle.

Reversing both coordinates reverses the cyclic order in each direction, so the two vertical sides
are reversed and exchanged, and likewise the two horizontal sides. -/
def rotate : GridRectangle n where
  left := R.right.rev
  right := R.left.rev
  bottom := R.top.rev
  top := R.bottom.rev

/-- The rotated rectangle's left side is the reversed original right side. -/
@[simp]
theorem rotate_left : R.rotate.left = R.right.rev :=
  rfl

/-- The rotated rectangle's right side is the reversed original left side. -/
@[simp]
theorem rotate_right : R.rotate.right = R.left.rev :=
  rfl

/-- The rotated rectangle's bottom side is the reversed original top side. -/
@[simp]
theorem rotate_bottom : R.rotate.bottom = R.top.rev :=
  rfl

/-- The rotated rectangle's top side is the reversed original bottom side. -/
@[simp]
theorem rotate_top : R.rotate.top = R.bottom.rev :=
  rfl

/-- The interior columns of the rotated rectangle are the reversed original interior columns. -/
theorem columnInterior_rotate : R.rotate.columnInterior = R.columnInterior.image Fin.rev := by
  simp only [columnInterior, rotate_left, rotate_right, Grid.cIoo_image_rev]

/-- The interior rows of the rotated rectangle are the reversed original interior rows. -/
theorem rowInterior_rotate : R.rotate.rowInterior = R.rowInterior.image Fin.rev := by
  simp only [rowInterior, rotate_bottom, rotate_top, Grid.cIoo_image_rev]

/-- The interior of the rotated rectangle is the half-turn rotation of the original interior. -/
theorem interior_rotate :
    R.rotate.interior = R.interior.image (Prod.map Fin.rev Fin.rev) := by
  simp only [interior, Finset.prodMap_image_product, columnInterior_rotate, rowInterior_rotate]

end GridRectangle

/-- An oriented toroidal rectangle from one grid state to another.

The two states agree outside the two side columns, and in those side columns they exchange the
two rows. Swapping `left` and `right` gives the complementary oriented rectangle. -/
structure GridRectangleBetween {n : ℕ} (x y : GridState n) where
  /-- The initial vertical side. -/
  left : Fin n
  /-- The terminal vertical side. -/
  right : Fin n
  /-- The two side columns are distinct. -/
  left_ne_right : left ≠ right
  /-- At the initial side, `y` uses the row that `x` uses at the terminal side. -/
  map_left : y left = x right
  /-- At the terminal side, `y` uses the row that `x` uses at the initial side. -/
  map_right : y right = x left
  /-- Away from the side columns, the two states agree. -/
  map_of_ne : ∀ c : Fin n, c ≠ left → c ≠ right → y c = x c

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n}

/-- The unordered finite set of side columns of an oriented grid rectangle. -/
def sideColumns (R : GridRectangleBetween x y) : Finset (Fin n) :=
  {R.left, R.right}

/-- Membership in the side-column set of an oriented grid rectangle. -/
@[simp]
theorem mem_sideColumns (R : GridRectangleBetween x y) (c : Fin n) :
    c ∈ R.sideColumns ↔ c = R.left ∨ c = R.right := by
  simp [sideColumns]

/-- An oriented grid rectangle has exactly two side columns. -/
@[simp]
theorem card_sideColumns (R : GridRectangleBetween x y) : R.sideColumns.card = 2 := by
  simp [sideColumns, R.left_ne_right]

/-- A rectangle between two grid states is determined by its two side columns. -/
theorem sidePair_injective :
    Function.Injective fun R : GridRectangleBetween x y => (R.left, R.right) := by
  intro R S h
  cases R
  cases S
  simp only at h
  obtain ⟨hleft, hright⟩ := Prod.ext_iff.mp h
  cases hleft
  cases hright
  rfl

/-- An oriented rectangle between two grid states has decidable equality: it is determined by its
ordered pair of side columns, which has decidable equality. -/
instance : DecidableEq (GridRectangleBetween x y) :=
  sidePair_injective.decidableEq

/-- For fixed source and target grid states, the oriented rectangles between them form a
finite type. Each rectangle is determined by its two side columns. -/
noncomputable instance : Fintype (GridRectangleBetween x y) :=
  Fintype.ofInjective (fun R : GridRectangleBetween x y => (R.left, R.right))
    sidePair_injective

/-- The finite set of all oriented rectangles from `x` to `y`. -/
noncomputable def all (x y : GridState n) : Finset (GridRectangleBetween x y) := by
  classical
  exact Finset.univ

/-- Membership in `GridRectangleBetween.all` is automatic. -/
@[simp]
theorem mem_all (R : GridRectangleBetween x y) : R ∈ all x y := by
  classical
  simp [all]

variable (R : GridRectangleBetween x y)

/-- The row of `x` on the initial side. -/
def bottom : Fin n :=
  x R.left

/-- The row of `x` on the terminal side. -/
def top : Fin n :=
  x R.right

/-- The initial horizontal side is the row occupied by the source state in the initial column. -/
theorem bottom_def : R.bottom = x R.left :=
  rfl

/-- The terminal horizontal side is the row occupied by the source state in the terminal column. -/
theorem top_def : R.top = x R.right :=
  rfl

/-- The associated toroidal rectangle. -/
def toGridRectangle : GridRectangle n where
  left := R.left
  right := R.right
  bottom := R.bottom
  top := R.top

/-- The associated toroidal rectangle has the same initial vertical side. -/
@[simp]
theorem toGridRectangle_left : R.toGridRectangle.left = R.left :=
  rfl

/-- The associated toroidal rectangle has the same terminal vertical side. -/
@[simp]
theorem toGridRectangle_right : R.toGridRectangle.right = R.right :=
  rfl

/-- The associated toroidal rectangle has the same initial horizontal side. -/
@[simp]
theorem toGridRectangle_bottom : R.toGridRectangle.bottom = R.bottom :=
  rfl

/-- The associated toroidal rectangle has the same terminal horizontal side. -/
@[simp]
theorem toGridRectangle_top : R.toGridRectangle.top = R.top :=
  rfl

/-- The opposite oriented rectangle, obtained by reversing the two side columns.

If `R` goes from `x` to `y`, then `R.symm` goes from `y` back to `x`. It has the same two
horizontal side rows and traverses the complementary horizontal direction on the torus. -/
def symm (R : GridRectangleBetween x y) : GridRectangleBetween y x where
  left := R.right
  right := R.left
  left_ne_right := R.left_ne_right.symm
  map_left := R.map_left.symm
  map_right := R.map_right.symm
  map_of_ne c hleft hright := (R.map_of_ne c hright hleft).symm

/-- The opposite rectangle's left side is the original right side. -/
@[simp]
theorem symm_left (R : GridRectangleBetween x y) : R.symm.left = R.right :=
  rfl

/-- The opposite rectangle's right side is the original left side. -/
@[simp]
theorem symm_right (R : GridRectangleBetween x y) : R.symm.right = R.left :=
  rfl

/-- Reversing an oriented rectangle twice gives the original rectangle. -/
@[simp]
theorem symm_symm (R : GridRectangleBetween x y) : R.symm.symm = R := by
  cases R
  rfl

/-- Reversal is injective on oriented rectangles. -/
@[simp]
theorem symm_inj {R S : GridRectangleBetween x y} : R.symm = S.symm ↔ R = S := by
  constructor
  · intro h
    simpa using congrArg symm h
  · intro h
    simp [h]

/-- Opposite rectangles give an equivalence between rectangles from `x` to `y` and from `y`
to `x`. -/
def symmEquiv (x y : GridState n) : GridRectangleBetween x y ≃ GridRectangleBetween y x where
  toFun := symm
  invFun := symm
  left_inv := symm_symm
  right_inv := symm_symm

/-- Applying the opposite-rectangle equivalence is `GridRectangleBetween.symm`. -/
@[simp]
theorem symmEquiv_apply (R : GridRectangleBetween x y) :
    symmEquiv x y R = R.symm :=
  rfl

/-- Applying the inverse opposite-rectangle equivalence is `GridRectangleBetween.symm`. -/
@[simp]
theorem symmEquiv_symm_apply (R : GridRectangleBetween y x) : (symmEquiv x y).symm R = R.symm :=
  rfl

/-- The opposite rectangle has the same bottom row. -/
@[simp]
theorem symm_bottom (R : GridRectangleBetween x y) : R.symm.bottom = R.bottom := by
  simp [bottom, symm, R.map_right]

/-- The opposite rectangle has the same top row. -/
@[simp]
theorem symm_top (R : GridRectangleBetween x y) : R.symm.top = R.top := by
  simp [top, symm, R.map_left]

/-- The associated toroidal rectangle of the opposite oriented rectangle is the opposite of
the associated toroidal rectangle. -/
@[simp]
theorem symm_toGridRectangle (R : GridRectangleBetween x y) :
    R.symm.toGridRectangle = R.toGridRectangle.symm := by
  cases R with
  | mk left right left_ne_right map_left map_right map_of_ne =>
      simp [toGridRectangle, GridRectangle.symm, symm, bottom, top, map_left, map_right]

/-- The two side rows of a rectangle between states are distinct. -/
theorem bottom_ne_top : R.bottom ≠ R.top := by
  intro h
  exact R.left_ne_right (x.toPerm.injective (by simpa [bottom, top] using h))

/-- A rectangle between grid states has distinct source and target states. A self-rectangle
would force the source state's permutation to take the same value on the two distinct side
columns. -/
theorem source_ne_target (R : GridRectangleBetween x y) : x ≠ y := by
  intro hxy
  cases hxy
  exact R.left_ne_right (x.toPerm.injective (by simpa [bottom, top] using R.map_left))

/-- There are no rectangles from a grid state to itself. -/
@[simp]
theorem all_self (x : GridState n) : all x x = ∅ := by
  classical
  ext R
  exact R.source_ne_target rfl |>.elim

/-- The initial lower corner is a point of the source state. -/
theorem left_bottom_mem_source : (R.left, R.bottom) ∈ x.pointSet := by
  simp [bottom]

/-- The terminal upper corner is a point of the source state. -/
theorem right_top_mem_source : (R.right, R.top) ∈ x.pointSet := by
  simp [top]

/-- The initial upper corner is a point of the target state. -/
theorem left_top_mem_target : (R.left, R.top) ∈ y.pointSet := by
  simp [top, R.map_left]

/-- The terminal lower corner is a point of the target state. -/
theorem right_bottom_mem_target : (R.right, R.bottom) ∈ y.pointSet := by
  simp [bottom, R.map_right]

/-- The lower-left corner of the opposite rectangle is a target-state point of the original
rectangle. -/
theorem symm_left_bottom_mem_source (R : GridRectangleBetween x y) :
    (R.symm.left, R.symm.bottom) ∈ y.pointSet := by
  simpa only [symm_left, symm_bottom] using R.right_bottom_mem_target

/-- The upper-right corner of the opposite rectangle is a target-state point of the original
rectangle. -/
theorem symm_right_top_mem_source (R : GridRectangleBetween x y) :
    (R.symm.right, R.symm.top) ∈ y.pointSet := by
  simpa only [symm_right, symm_top] using R.left_top_mem_target

/-- The upper-left corner of the opposite rectangle is a source-state point of the original
rectangle. -/
theorem symm_left_top_mem_target (R : GridRectangleBetween x y) :
    (R.symm.left, R.symm.top) ∈ x.pointSet := by
  simpa only [symm_left, symm_top] using R.right_top_mem_source

/-- The lower-right corner of the opposite rectangle is a source-state point of the original
rectangle. -/
theorem symm_right_bottom_mem_target (R : GridRectangleBetween x y) :
    (R.symm.right, R.symm.bottom) ∈ x.pointSet := by
  simpa only [symm_right, symm_bottom] using R.left_bottom_mem_source

/-- There are as many oriented rectangles from `x` to `y` as from `y` to `x`. -/
theorem card_all_comm (x y : GridState n) : (all x y).card = (all y x).card := by
  classical
  simp [all, Fintype.card_congr (symmEquiv x y)]

/-- Away from the two side columns, membership in the source and target states is identical. -/
theorem mem_target_pointSet_iff_of_ne {p : Fin n × Fin n}
    (hleft : p.1 ≠ R.left) (hright : p.1 ≠ R.right) :
    p ∈ y.pointSet ↔ p ∈ x.pointSet := by
  simp [R.map_of_ne p.1 hleft hright]

/-- The associated rectangle is empty for the source state when no source-state point lies in
its interior. -/
def IsEmpty : Prop :=
  R.toGridRectangle.IsEmptyFor x

/-- The finite set of empty oriented rectangles from `x` to `y`. -/
noncomputable def emptyRectangles (x y : GridState n) : Finset (GridRectangleBetween x y) := by
  classical
  exact (all x y).filter fun R => R.IsEmpty

/-- Membership in the finite set of empty rectangles is exactly the emptiness predicate. -/
@[simp]
theorem mem_emptyRectangles (R : GridRectangleBetween x y) :
    R ∈ emptyRectangles x y ↔ R.IsEmpty := by
  classical
  simp [emptyRectangles]

/-- Every rectangle in `emptyRectangles` is empty. -/
theorem isEmpty_of_mem_emptyRectangles {R : GridRectangleBetween x y}
    (hR : R ∈ emptyRectangles x y) : R.IsEmpty :=
  (mem_emptyRectangles R).mp hR

/-- In grid size at most two, every oriented rectangle between grid states is empty. -/
theorem isEmpty_of_le_two (hn : n ≤ 2) (R : GridRectangleBetween x y) : R.IsEmpty :=
  R.toGridRectangle.isEmptyFor_of_le_two hn x

/-- Empty rectangles are a subset of all rectangles between the same two states. -/
theorem emptyRectangles_subset_all (x y : GridState n) :
    emptyRectangles x y ⊆ all x y := by
  classical
  intro R hR
  simp [emptyRectangles] at hR ⊢

/-- In grid size at most two, the empty rectangles are all oriented rectangles. -/
theorem emptyRectangles_eq_all_of_le_two (hn : n ≤ 2) (x y : GridState n) :
    emptyRectangles x y = all x y := by
  ext R
  simp [isEmpty_of_le_two hn R]

/-- There are no empty rectangles from a grid state to itself. -/
@[simp]
theorem emptyRectangles_self (x : GridState n) : emptyRectangles x x = ∅ := by
  classical
  simp [emptyRectangles]

/-- The associated rectangle avoids a grid diagram's markings when no marking lies in its
interior. -/
def AvoidsMarkings (G : GridDiagram n) : Prop :=
  R.toGridRectangle.AvoidsMarkings G

/-- The source state has no point in the interior of an empty rectangle between states. -/
theorem not_mem_interior_of_isEmpty (h : R.IsEmpty) {p : Fin n × Fin n}
    (hp : p ∈ x.pointSet) : p ∉ R.toGridRectangle.interior :=
  (R.toGridRectangle.isEmptyFor_iff x).mp h p hp

/-- A rectangle between states is empty exactly when no source-state point lies in its
interior. -/
theorem isEmpty_iff :
    R.IsEmpty ↔ ∀ p ∈ x.pointSet, p ∉ R.toGridRectangle.interior :=
  R.toGridRectangle.isEmptyFor_iff x

/-- If a target-state point lies on a side column, then it is not in the associated
rectangle's interior. -/
theorem not_mem_interior_of_fst_eq_left {p : Fin n × Fin n} (hp : p.1 = R.left) :
    p ∉ R.toGridRectangle.interior := by
  intro hpR
  have hpcol := (R.toGridRectangle.mem_interior p).mp hpR |>.1
  rw [hp] at hpcol
  exact R.toGridRectangle.left_notMem_columnInterior hpcol

/-- If a target-state point lies on the other side column, then it is not in the associated
rectangle's interior. -/
theorem not_mem_interior_of_fst_eq_right {p : Fin n × Fin n} (hp : p.1 = R.right) :
    p ∉ R.toGridRectangle.interior := by
  intro hpR
  have hpcol := (R.toGridRectangle.mem_interior p).mp hpR |>.1
  rw [hp] at hpcol
  exact R.toGridRectangle.right_notMem_columnInterior hpcol

/-- A rectangle between states is empty exactly when no target-state point lies in its
interior. -/
theorem isEmpty_iff_target :
    R.IsEmpty ↔ ∀ p ∈ y.pointSet, p ∉ R.toGridRectangle.interior := by
  rw [isEmpty_iff]
  constructor
  · intro h p hp
    by_cases hleft : p.1 = R.left
    · exact R.not_mem_interior_of_fst_eq_left hleft
    by_cases hright : p.1 = R.right
    · exact R.not_mem_interior_of_fst_eq_right hright
    exact h p ((R.mem_target_pointSet_iff_of_ne hleft hright).mp hp)
  · intro h p hp hpR
    have hleft : p.1 ≠ R.left := by
      intro hcol
      exact R.not_mem_interior_of_fst_eq_left hcol hpR
    have hright : p.1 ≠ R.right := by
      intro hcol
      exact R.not_mem_interior_of_fst_eq_right hcol hpR
    exact h p ((R.mem_target_pointSet_iff_of_ne hleft hright).mpr hp) hpR

/-- The target state has no point in the interior of an empty rectangle between states. -/
theorem not_mem_interior_target_of_isEmpty (h : R.IsEmpty) {p : Fin n × Fin n}
    (hp : p ∈ y.pointSet) : p ∉ R.toGridRectangle.interior :=
  (R.isEmpty_iff_target).mp h p hp

/-- A rectangle between states avoids markings exactly when neither marking set meets its
interior. -/
theorem avoidsMarkings_iff (G : GridDiagram n) :
    R.AvoidsMarkings G ↔
      Disjoint R.toGridRectangle.interior G.OSet ∧
        Disjoint R.toGridRectangle.interior G.XSet :=
  R.toGridRectangle.avoidsMarkings_iff G

/-- A marking-avoiding rectangle between states has no `O` marking in its interior. -/
theorem disjoint_interior_OSet_of_avoidsMarkings {G : GridDiagram n}
    (h : R.AvoidsMarkings G) : Disjoint R.toGridRectangle.interior G.OSet :=
  R.toGridRectangle.disjoint_interior_OSet_of_avoidsMarkings h

/-- A marking-avoiding rectangle between states has no `X` marking in its interior. -/
theorem disjoint_interior_XSet_of_avoidsMarkings {G : GridDiagram n}
    (h : R.AvoidsMarkings G) : Disjoint R.toGridRectangle.interior G.XSet :=
  R.toGridRectangle.disjoint_interior_XSet_of_avoidsMarkings h

/-- The diagonal reflection of an oriented rectangle from `x` to `y`, an oriented rectangle from
`x.transpose` to `y.transpose`.

Reflecting across the main diagonal exchanges the side columns with the side rows: the new side
columns are the two rows `x R.left` and `x R.right` that `R` connects. -/
def transpose (R : GridRectangleBetween x y) :
    GridRectangleBetween x.transpose y.transpose where
  left := R.bottom
  right := R.top
  left_ne_right := R.bottom_ne_top
  map_left := by
    simp only [GridRectangleBetween.bottom, GridRectangleBetween.top]
    rw [GridState.transpose_apply, GridState.transpose_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_eq]
    exact R.map_right.symm
  map_right := by
    simp only [GridRectangleBetween.bottom, GridRectangleBetween.top]
    rw [GridState.transpose_apply, GridState.transpose_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_eq]
    exact R.map_left.symm
  map_of_ne c hl hr := by
    have hsymm : x (x.toPerm.symm c) = c := Equiv.apply_symm_apply _ _
    have hd_left : x.toPerm.symm c ≠ R.left := by
      intro h; rw [h] at hsymm; exact hl hsymm.symm
    have hd_right : x.toPerm.symm c ≠ R.right := by
      intro h; rw [h] at hsymm; exact hr hsymm.symm
    rw [GridState.transpose_apply, GridState.transpose_apply, Equiv.symm_apply_eq,
      R.map_of_ne _ hd_left hd_right]
    exact hsymm.symm

/-- The reflected rectangle's initial side column is the original initial side row. -/
@[simp]
theorem transpose_left (R : GridRectangleBetween x y) : R.transpose.left = R.bottom :=
  rfl

/-- The reflected rectangle's terminal side column is the original terminal side row. -/
@[simp]
theorem transpose_right (R : GridRectangleBetween x y) : R.transpose.right = R.top :=
  rfl

/-- The reflected rectangle's initial side row is the original initial side column. -/
@[simp]
theorem transpose_bottom (R : GridRectangleBetween x y) : R.transpose.bottom = R.left := by
  simp only [GridRectangleBetween.bottom, transpose_left, GridState.transpose_apply,
    Equiv.symm_apply_apply]

/-- The reflected rectangle's terminal side row is the original terminal side column. -/
@[simp]
theorem transpose_top (R : GridRectangleBetween x y) : R.transpose.top = R.right := by
  simp only [GridRectangleBetween.top, transpose_right, GridState.transpose_apply,
    Equiv.symm_apply_apply]

/-- The toroidal rectangle of the reflected oriented rectangle, written out by its four sides. -/
@[simp]
theorem transpose_toGridRectangle (R : GridRectangleBetween x y) :
    R.transpose.toGridRectangle =
      { left := R.bottom, right := R.top, bottom := R.left, top := R.right } := by
  unfold GridRectangleBetween.toGridRectangle
  rw [transpose_bottom, transpose_top, transpose_left, transpose_right]

/-- Two oriented rectangles between the same states with equal side columns are equal. -/
theorem eq_of_sides {R S : GridRectangleBetween x y} (hleft : R.left = S.left)
    (hright : R.right = S.right) : R = S := by
  obtain ⟨_, _, _, _, _, _⟩ := R
  obtain ⟨_, _, _, _, _, _⟩ := S
  obtain rfl : _ = _ := hleft
  obtain rfl : _ = _ := hright
  rfl

end GridRectangleBetween

end TauCeti

end

public section

namespace TauCeti

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n}

/-- The oriented rectangle from `x` to `y` obtained by exchanging the two side columns.

It connects the same two states `x` and `y` -- the two states still exchange rows at the two
side columns and agree elsewhere -- but traverses the complementary toroidal region. This is not
the opposite rectangle `symm`, which runs from `y` back to `x`. -/
def swapSides (R : GridRectangleBetween x y) : GridRectangleBetween x y where
  left := R.right
  right := R.left
  left_ne_right := R.left_ne_right.symm
  map_left := R.map_right
  map_right := R.map_left
  map_of_ne c hl hr := R.map_of_ne c hr hl

end GridRectangleBetween

end TauCeti

end

section

namespace TauCeti

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n}

private theorem swapSides_left_aux (R : GridRectangleBetween x y) : R.swapSides.left = R.right :=
  rfl

private theorem swapSides_right_aux (R : GridRectangleBetween x y) : R.swapSides.right = R.left :=
  rfl

private theorem swapSides_bottom_aux (R : GridRectangleBetween x y) : R.swapSides.bottom = R.top :=
  rfl

private theorem swapSides_top_aux (R : GridRectangleBetween x y) : R.swapSides.top = R.bottom :=
  rfl

private theorem swapSides_toGridRectangle_aux (R : GridRectangleBetween x y) :
    R.swapSides.toGridRectangle =
      { left := R.right, right := R.left, bottom := R.top, top := R.bottom } := by
  rfl

end GridRectangleBetween

end TauCeti

end

public section

namespace TauCeti

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n}

/-- The side-swapped rectangle's initial side column is the original terminal side column. -/
@[simp]
theorem swapSides_left (R : GridRectangleBetween x y) : R.swapSides.left = R.right :=
  swapSides_left_aux R

/-- The side-swapped rectangle's terminal side column is the original initial side column. -/
@[simp]
theorem swapSides_right (R : GridRectangleBetween x y) : R.swapSides.right = R.left :=
  swapSides_right_aux R

/-- The side-swapped rectangle's bottom row is the original top row. -/
@[simp]
theorem swapSides_bottom (R : GridRectangleBetween x y) : R.swapSides.bottom = R.top :=
  swapSides_bottom_aux R

/-- The side-swapped rectangle's top row is the original bottom row. -/
@[simp]
theorem swapSides_top (R : GridRectangleBetween x y) : R.swapSides.top = R.bottom :=
  swapSides_top_aux R

/-- The toroidal rectangle of the side-swapped oriented rectangle, written out by its four
sides. -/
@[simp]
theorem swapSides_toGridRectangle (R : GridRectangleBetween x y) :
    R.swapSides.toGridRectangle =
      { left := R.right, right := R.left, bottom := R.top, top := R.bottom } := by
  exact swapSides_toGridRectangle_aux R

/-- Exchanging the two side columns twice gives the original rectangle. -/
@[simp]
theorem swapSides_swapSides (R : GridRectangleBetween x y) : R.swapSides.swapSides = R :=
  eq_of_sides (swapSides_right R) (swapSides_left R)

/-- Exchanging the two side columns gives a genuinely different rectangle, since the two side
columns are distinct. -/
theorem swapSides_ne_self (R : GridRectangleBetween x y) : R.swapSides ≠ R := by
  intro h
  have hleft : R.swapSides.left = R.left := congrArg GridRectangleBetween.left h
  rw [swapSides_left] at hleft
  exact R.left_ne_right hleft.symm

end GridRectangleBetween

end TauCeti

end

@[expose] public section

namespace TauCeti

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n}

/-- Reflecting an oriented rectangle twice gives the original rectangle. -/
@[simp]
theorem transpose_transpose (R : GridRectangleBetween x y) : R.transpose.transpose = R :=
  eq_of_sides (transpose_bottom R) (transpose_top R)

/-- The diagonal reflection as an equivalence between oriented rectangles from `x` to `y` and
oriented rectangles from `x.transpose` to `y.transpose`. Since reflecting twice is the identity,
`transpose` is its own inverse. -/
def transposeEquiv (x y : GridState n) :
    GridRectangleBetween x y ≃ GridRectangleBetween x.transpose y.transpose where
  toFun := transpose
  invFun := transpose
  left_inv := transpose_transpose
  right_inv := transpose_transpose

/-- The transpose equivalence applies a rectangle by reflecting it. -/
@[simp]
theorem transposeEquiv_apply (R : GridRectangleBetween x y) :
    transposeEquiv x y R = R.transpose :=
  rfl

/-- The inverse of the transpose equivalence is again reflection. -/
@[simp]
theorem transposeEquiv_symm_apply (R : GridRectangleBetween x.transpose y.transpose) :
    (transposeEquiv x y).symm R = R.transpose :=
  rfl

/-- The diagonal reflection is injective on oriented rectangles. -/
theorem transpose_injective :
    Function.Injective
      (transpose : GridRectangleBetween x y → GridRectangleBetween x.transpose y.transpose) :=
  (transposeEquiv x y).injective

/-- Two oriented rectangles have equal diagonal reflections exactly when they are equal. -/
@[simp]
theorem transpose_inj {R S : GridRectangleBetween x y} :
    R.transpose = S.transpose ↔ R = S :=
  (transposeEquiv x y).apply_eq_iff_eq

/-- The interior of the reflected rectangle is the diagonal reflection of the interior of the
original rectangle. This is the oriented-rectangle corollary of
`GridRectangle.interior_transpose`. -/
theorem interior_transpose (R : GridRectangleBetween x y) :
    R.transpose.toGridRectangle.interior = R.toGridRectangle.interior.image Prod.swap := by
  rw [transpose_toGridRectangle]
  exact R.toGridRectangle.interior_transpose

/-- The diagonal reflection preserves emptiness of a rectangle between grid states. -/
theorem isEmpty_transpose (R : GridRectangleBetween x y) :
    R.transpose.IsEmpty ↔ R.IsEmpty := by
  unfold GridRectangleBetween.IsEmpty GridRectangle.IsEmptyFor
  rw [interior_transpose, GridState.transpose_pointSet,
    Finset.disjoint_image Prod.swap_injective]

/-- The diagonal reflection preserves marking avoidance of a rectangle between grid states. -/
theorem avoidsMarkings_transpose (G : GridDiagram n) (R : GridRectangleBetween x y) :
    R.transpose.AvoidsMarkings G.transpose ↔ R.AvoidsMarkings G := by
  unfold GridRectangleBetween.AvoidsMarkings GridRectangle.AvoidsMarkings
  rw [interior_transpose, G.transpose_OSet, G.transpose_XSet, ← Finset.image_union,
    Finset.disjoint_image Prod.swap_injective]

/-- Swapping the `O` and `X` markings preserves marking avoidance of a rectangle between grid
states. -/
theorem avoidsMarkings_swapMarkings (G : GridDiagram n) (R : GridRectangleBetween x y) :
    R.AvoidsMarkings G.swapMarkings ↔ R.AvoidsMarkings G :=
  R.toGridRectangle.avoidsMarkings_swapMarkings G

/-- The half-turn rotation of an oriented rectangle from `x` to `y`, an oriented rectangle from
`x.rotate` to `y.rotate`.

Reversing both coordinates reverses and exchanges the two side columns: the new initial side is
the reversed terminal column `R.rightᵒ` and the new terminal side is the reversed initial column
`R.leftᵒ`. -/
def rotate (R : GridRectangleBetween x y) : GridRectangleBetween x.rotate y.rotate where
  left := R.right.rev
  right := R.left.rev
  left_ne_right := fun h => R.left_ne_right (Fin.rev_injective h).symm
  map_left := by
    simp only [GridState.rotate_apply, Fin.rev_rev, R.map_right]
  map_right := by
    simp only [GridState.rotate_apply, Fin.rev_rev, R.map_left]
  map_of_ne c hl hr := by
    have h1 : Fin.rev c ≠ R.left := fun h => hr (Fin.rev_eq_iff.mp h)
    have h2 : Fin.rev c ≠ R.right := fun h => hl (Fin.rev_eq_iff.mp h)
    simp only [GridState.rotate_apply, R.map_of_ne (Fin.rev c) h1 h2]

/-- The rotated oriented rectangle's initial side column is the reversed terminal side column. -/
@[simp]
theorem rotate_left (R : GridRectangleBetween x y) : R.rotate.left = R.right.rev :=
  rfl

/-- The rotated oriented rectangle's terminal side column is the reversed initial side column. -/
@[simp]
theorem rotate_right (R : GridRectangleBetween x y) : R.rotate.right = R.left.rev :=
  rfl

/-- The rotated oriented rectangle's initial side row is the reversed terminal side row. -/
@[simp]
theorem rotate_bottom (R : GridRectangleBetween x y) : R.rotate.bottom = R.top.rev := by
  simp only [GridRectangleBetween.bottom, GridRectangleBetween.top, rotate_left,
    GridState.rotate_apply, Fin.rev_rev]

/-- The rotated oriented rectangle's terminal side row is the reversed initial side row. -/
@[simp]
theorem rotate_top (R : GridRectangleBetween x y) : R.rotate.top = R.bottom.rev := by
  simp only [GridRectangleBetween.top, GridRectangleBetween.bottom, rotate_right,
    GridState.rotate_apply, Fin.rev_rev]

/-- The toroidal rectangle of the rotated oriented rectangle is the rotation of the toroidal
rectangle. -/
theorem rotate_toGridRectangle (R : GridRectangleBetween x y) :
    R.rotate.toGridRectangle = R.toGridRectangle.rotate := by
  simp only [GridRectangleBetween.toGridRectangle, GridRectangle.rotate, rotate_left, rotate_right,
    rotate_bottom, rotate_top]

/-- The interior of the rotated oriented rectangle is the half-turn rotation of the interior of
the original oriented rectangle. -/
theorem interior_rotate (R : GridRectangleBetween x y) :
    R.rotate.toGridRectangle.interior =
      R.toGridRectangle.interior.image (Prod.map Fin.rev Fin.rev) := by
  rw [rotate_toGridRectangle, GridRectangle.interior_rotate]

/-- The inverse half-turn rotation, an oriented rectangle from `x` to `y` built from one between
the rotated states. It reverses and exchanges the side columns by the same recipe as `rotate`,
but lands in `GridRectangleBetween x y` directly; reversal is only an involution up to
`Fin.rev_rev`, so this avoids transporting along the (non-definitional) state involution. -/
def rotateSymm (S : GridRectangleBetween x.rotate y.rotate) : GridRectangleBetween x y where
  left := S.right.rev
  right := S.left.rev
  left_ne_right := fun h => S.left_ne_right (Fin.rev_injective h).symm
  map_left := by
    have h := S.map_right
    rw [GridState.rotate_apply, GridState.rotate_apply] at h
    exact Fin.rev_injective h
  map_right := by
    have h := S.map_left
    rw [GridState.rotate_apply, GridState.rotate_apply] at h
    exact Fin.rev_injective h
  map_of_ne c hl hr := by
    have h1 : Fin.rev c ≠ S.left := fun h => hr (Fin.rev_eq_iff.mp h)
    have h2 : Fin.rev c ≠ S.right := fun h => hl (Fin.rev_eq_iff.mp h)
    have h := S.map_of_ne (Fin.rev c) h1 h2
    rw [GridState.rotate_apply, GridState.rotate_apply, Fin.rev_rev] at h
    exact Fin.rev_injective h

/-- The inverse rotation's initial side column is the reversed terminal side column. -/
@[simp]
theorem rotateSymm_left (S : GridRectangleBetween x.rotate y.rotate) :
    (rotateSymm S).left = S.right.rev :=
  rfl

/-- The inverse rotation's terminal side column is the reversed initial side column. -/
@[simp]
theorem rotateSymm_right (S : GridRectangleBetween x.rotate y.rotate) :
    (rotateSymm S).right = S.left.rev :=
  rfl

/-- The half-turn rotation as an equivalence between oriented rectangles from `x` to `y` and
oriented rectangles from `x.rotate` to `y.rotate`. -/
def rotateEquiv (x y : GridState n) :
    GridRectangleBetween x y ≃ GridRectangleBetween x.rotate y.rotate where
  toFun := rotate
  invFun := rotateSymm
  left_inv R := eq_of_sides (by simp) (by simp)
  right_inv S := eq_of_sides (by simp) (by simp)

/-- The rotation equivalence applies a rectangle by rotating it. -/
@[simp]
theorem rotateEquiv_apply (R : GridRectangleBetween x y) :
    rotateEquiv x y R = R.rotate :=
  rfl

/-- The inverse of the rotation equivalence is the inverse rotation. -/
@[simp]
theorem rotateEquiv_symm_apply (S : GridRectangleBetween x.rotate y.rotate) :
    (rotateEquiv x y).symm S = rotateSymm S :=
  rfl

/-- The half-turn rotation preserves emptiness of a rectangle between grid states. -/
theorem isEmpty_rotate (R : GridRectangleBetween x y) :
    R.rotate.IsEmpty ↔ R.IsEmpty := by
  unfold GridRectangleBetween.IsEmpty GridRectangle.IsEmptyFor
  rw [interior_rotate, GridState.rotate_pointSet,
    Finset.disjoint_image (Fin.rev_injective.prodMap Fin.rev_injective)]

/-- The half-turn rotation preserves marking avoidance of a rectangle between grid states. -/
theorem avoidsMarkings_rotate (G : GridDiagram n) (R : GridRectangleBetween x y) :
    R.rotate.AvoidsMarkings G.rotate ↔ R.AvoidsMarkings G := by
  unfold GridRectangleBetween.AvoidsMarkings GridRectangle.AvoidsMarkings
  rw [interior_rotate, G.rotate_OSet, G.rotate_XSet, ← Finset.image_union,
    Finset.disjoint_image (Fin.rev_injective.prodMap Fin.rev_injective)]

end GridRectangleBetween

end TauCeti
