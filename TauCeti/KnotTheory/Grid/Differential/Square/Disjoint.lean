/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.Decomposition
public import TauCeti.KnotTheory.Grid.Differential.Square.Intermediates

/-!
# Reordering rectangle decompositions with disjoint side columns

A two-step term in the square of the grid differential consists of a rectangle from `x` to an
intermediate state and a second rectangle from that state to `z`. When the two rectangles use
disjoint pairs of side columns, their column transpositions commute. They may therefore be applied
in the opposite order, through a different intermediate state.

This file reorders such a `GridRectangleDecomposition`. The first reordered rectangle has exactly
the toroidal domain of the old second rectangle, and conversely for the second. In particular,
both marking-avoidance conditions are preserved. Reordering is an involution and changes the
intermediate state, giving the fixed-point-free pairing needed in the disjoint-side case of the
eventual rectangle juxtaposition argument.

Reordering also transfers emptiness. If both rectangles of the original decomposition are empty,
then so are both rectangles of the reordered one. This is the one genuinely geometric step of the
disjoint-side case: the two side columns of one rectangle sit on opposite cyclic arcs of the other
pair, and `Grid.mem_cIoo_of_mem_cIoo_of_mem_cIoo_swap` turns that separation around to produce a
grid-state point inside the rectangle assumed empty. The overlapping and annular cases remain
separate parts of the square-zero proof.

## Main definitions

* `TauCeti.GridRectangleDecomposition.HasDisjointSides`: the two side-column pairs are disjoint.
* `TauCeti.GridRectangleDecomposition.commute`: apply two rectangles with disjoint side columns
  in the opposite order.

## Main results

* `TauCeti.GridRectangleDecomposition.commute_first_toGridRectangle` and
  `commute_second_toGridRectangle`: reordering exchanges the two toroidal domains.
* `TauCeti.GridRectangleDecomposition.avoidsMarkings_commute_first_iff` and
  `avoidsMarkings_commute_second_iff`: reordering preserves the marking-avoidance conditions.
* `TauCeti.GridRectangleDecomposition.commute_commute`: reordering twice is the identity.
* `TauCeti.GridRectangleDecomposition.commute_middle_ne` and
  `TauCeti.GridRectangleDecomposition.commute_ne`: the intermediate state changes, so reordering
  has no fixed point.
* `TauCeti.GridRectangleDecomposition.isEmpty_commute_first` and
  `TauCeti.GridRectangleDecomposition.isEmpty_commute_second`: reordering a decomposition into
  two empty rectangles again gives two empty rectangles.

## References

This supplies the disjoint-side orientation step for
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, "The complexes and `∂² = 0`".
The decomposition pairing follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*,
Chapter 4.6.
-/

public section

namespace TauCeti

namespace GridRectangleDecomposition

variable {n : ℕ} {x z : GridState n}

/-- The two rectangles in a decomposition use disjoint pairs of side columns. -/
def HasDisjointSides (D : GridRectangleDecomposition x z) : Prop :=
  Disjoint D.first.sideColumns D.second.sideColumns

/-- Disjointness of the two side-column pairs, expanded into the four cross-inequalities. -/
theorem hasDisjointSides_iff (D : GridRectangleDecomposition x z) :
    D.HasDisjointSides ↔
      D.first.left ≠ D.second.left ∧ D.first.left ≠ D.second.right ∧
        D.first.right ≠ D.second.left ∧ D.first.right ≠ D.second.right := by
  simp only [HasDisjointSides, GridRectangleBetween.sideColumns, Finset.disjoint_insert_left,
    Finset.disjoint_singleton_left, Finset.mem_insert, Finset.mem_singleton]
  aesop

private theorem swapColumns_comm_of_hasDisjointSides (D : GridRectangleDecomposition x z)
    (h : D.HasDisjointSides) :
    (x.swapColumns D.first.left D.first.right).swapColumns D.second.left D.second.right =
      (x.swapColumns D.second.left D.second.right).swapColumns D.first.left D.first.right := by
  obtain ⟨hll, hlr, hrl, hrr⟩ := (D.hasDisjointSides_iff.mp h)
  rw [x.swapColumns_swapColumns_conj]
  simp only [Equiv.swap_apply_of_ne_of_ne hll hlr,
    Equiv.swap_apply_of_ne_of_ne hrl hrr]

private theorem target_eq_commuted (D : GridRectangleDecomposition x z)
    (h : D.HasDisjointSides) :
    z = (x.swapColumns D.second.left D.second.right).swapColumns
      D.first.left D.first.right := by
  calc
    z = D.middle.swapColumns D.second.left D.second.right :=
      D.second.target_eq_swapColumns
    _ = (x.swapColumns D.first.left D.first.right).swapColumns
        D.second.left D.second.right :=
      congrArg (fun w => w.swapColumns D.second.left D.second.right)
        D.first.target_eq_swapColumns
    _ = (x.swapColumns D.second.left D.second.right).swapColumns
        D.first.left D.first.right := D.swapColumns_comm_of_hasDisjointSides h

private def commuteFirst (D : GridRectangleDecomposition x z) :
    GridRectangleBetween x (x.swapColumns D.second.left D.second.right) :=
  GridRectangleBetween.ofSwapColumns x _ D.second.left D.second.right
    D.second.left_ne_right rfl

private def commuteSecond (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides) :
    GridRectangleBetween (x.swapColumns D.second.left D.second.right) z :=
  GridRectangleBetween.ofSwapColumns _ z D.first.left D.first.right D.first.left_ne_right
    (D.target_eq_commuted h)

@[simp]
private theorem commuteFirst_left (D : GridRectangleDecomposition x z) :
    D.commuteFirst.left = D.second.left := by
  unfold commuteFirst
  simp

@[simp]
private theorem commuteFirst_right (D : GridRectangleDecomposition x z) :
    D.commuteFirst.right = D.second.right := by
  unfold commuteFirst
  simp

@[simp]
private theorem commuteSecond_left (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides) :
    (D.commuteSecond h).left = D.first.left := by
  unfold commuteSecond
  simp

@[simp]
private theorem commuteSecond_right (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides) :
    (D.commuteSecond h).right = D.first.right := by
  unfold commuteSecond
  simp

/-- Reorder two rectangle moves whose pairs of side columns are disjoint. -/
def commute (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides) :
    GridRectangleDecomposition x z where
  middle := x.swapColumns D.second.left D.second.right
  first := D.commuteFirst
  second := D.commuteSecond h

/-- The initial side of the first reordered rectangle. -/
@[simp]
theorem commute_first_left (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides) :
    (D.commute h).first.left = D.second.left := by
  unfold commute
  exact D.commuteFirst_left

/-- The terminal side of the first reordered rectangle. -/
@[simp]
theorem commute_first_right (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides) :
    (D.commute h).first.right = D.second.right := by
  unfold commute
  exact D.commuteFirst_right

/-- The initial side of the second reordered rectangle. -/
@[simp]
theorem commute_second_left (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides) :
    (D.commute h).second.left = D.first.left := by
  unfold commute
  exact D.commuteSecond_left h

/-- The terminal side of the second reordered rectangle. -/
@[simp]
theorem commute_second_right (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides) :
    (D.commute h).second.right = D.first.right := by
  unfold commute
  exact D.commuteSecond_right h

/-- The intermediate state of the reordered decomposition. -/
@[simp]
theorem commute_middle (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides) :
    (D.commute h).middle = x.swapColumns D.second.left D.second.right :=
  by
    unfold commute
    rfl

/-- Reordering exchanges the first toroidal rectangle with the old second rectangle. -/
@[simp]
theorem commute_first_toGridRectangle (D : GridRectangleDecomposition x z)
    (h : D.HasDisjointSides) :
    (D.commute h).first.toGridRectangle = D.second.toGridRectangle := by
  obtain ⟨hll, hlr, hrl, hrr⟩ := D.hasDisjointSides_iff.mp h
  have hleft : D.middle D.second.left = x D.second.left :=
    D.first.map_of_ne D.second.left hll.symm hrl.symm
  have hright : D.middle D.second.right = x D.second.right :=
    D.first.map_of_ne D.second.right hlr.symm hrr.symm
  unfold commute
  dsimp only
  unfold commuteFirst
  rw [GridRectangleBetween.ofSwapColumns_toGridRectangle]
  simp [GridRectangleBetween.toGridRectangle, GridRectangleBetween.bottom,
    GridRectangleBetween.top, hleft, hright]

/-- Reordering exchanges the second toroidal rectangle with the old first rectangle. -/
@[simp]
theorem commute_second_toGridRectangle (D : GridRectangleDecomposition x z)
    (h : D.HasDisjointSides) :
    (D.commute h).second.toGridRectangle = D.first.toGridRectangle := by
  obtain ⟨hll, hlr, hrl, hrr⟩ := D.hasDisjointSides_iff.mp h
  unfold commute
  dsimp only
  unfold commuteSecond
  rw [GridRectangleBetween.ofSwapColumns_toGridRectangle]
  simp [GridRectangleBetween.toGridRectangle, GridRectangleBetween.bottom,
    GridRectangleBetween.top, GridState.swapColumns_apply,
    Equiv.swap_apply_of_ne_of_ne hll hlr, Equiv.swap_apply_of_ne_of_ne hrl hrr]

/-- Reordering preserves the marking-avoidance condition on the first domain. -/
@[simp]
theorem avoidsMarkings_commute_first_iff (D : GridRectangleDecomposition x z)
    (h : D.HasDisjointSides) (G : GridDiagram n) :
    (D.commute h).first.AvoidsMarkings G ↔ D.second.AvoidsMarkings G := by
  unfold GridRectangleBetween.AvoidsMarkings
  rw [D.commute_first_toGridRectangle h]

/-- Reordering preserves the marking-avoidance condition on the second domain. -/
@[simp]
theorem avoidsMarkings_commute_second_iff (D : GridRectangleDecomposition x z)
    (h : D.HasDisjointSides) (G : GridDiagram n) :
    (D.commute h).second.AvoidsMarkings G ↔ D.first.AvoidsMarkings G := by
  unfold GridRectangleBetween.AvoidsMarkings
  rw [D.commute_second_toGridRectangle h]

/-- The reordered decomposition again has disjoint side-column pairs. -/
theorem hasDisjointSides_commute (D : GridRectangleDecomposition x z)
    (h : D.HasDisjointSides) : (D.commute h).HasDisjointSides := by
  rw [HasDisjointSides]
  simpa only [commute_first_left, commute_first_right, commute_second_left,
    commute_second_right, GridRectangleBetween.sideColumns] using h.symm

/-- Reordering two disjoint-side rectangle decompositions twice recovers the original
decomposition. -/
@[simp]
theorem commute_commute (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides) :
    (D.commute h).commute (D.hasDisjointSides_commute h) = D := by
  ext <;> simp

private theorem sidePairs_ne (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides) :
    s(D.first.left, D.first.right) ≠ s(D.second.left, D.second.right) := by
  obtain ⟨hll, hlr, hrl, hrr⟩ := D.hasDisjointSides_iff.mp h
  intro hpairs
  rw [Sym2.eq, Sym2.rel_iff'] at hpairs
  rcases hpairs with hpairs | hpairs
  · exact hll (Prod.ext_iff.mp hpairs).1
  · exact hlr (Prod.ext_iff.mp hpairs).1

/-- The reordered decomposition passes through a different intermediate state. -/
theorem commute_middle_ne (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides) :
    (D.commute h).middle ≠ D.middle := by
  have halt := (x.swapColumns_mem_twoStepColumnSwapIntermediates_ne D.first.left_ne_right
    D.second.left_ne_right (D.sidePairs_ne h)).2
  intro heq
  apply halt
  calc
    x.swapColumns D.second.left D.second.right = (D.commute h).middle :=
      (D.commute_middle h).symm
    _ = D.middle := heq
    _ = x.swapColumns D.first.left D.first.right := D.first.target_eq_swapColumns

/-- Reordering never fixes a decomposition with disjoint side columns: its intermediate state
changes. -/
theorem commute_ne (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides) :
    D.commute h ≠ D :=
  fun heq => D.commute_middle_ne h (congrArg GridRectangleDecomposition.middle heq)

/-- The reordered intermediate state belongs to the endpoint pair's two-step intermediate set. -/
theorem commute_middle_mem_twoStepColumnSwapIntermediates
    (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides) :
    (D.commute h).middle ∈ x.twoStepColumnSwapIntermediates z := by
  rw [GridState.mem_twoStepColumnSwapIntermediates_iff_mem_columnSwapNeighbors]
  constructor
  · rw [D.commute_middle h, GridState.mem_columnSwapNeighbors]
    exact ⟨D.second.left, D.second.right, D.second.left_ne_right, rfl⟩
  · rw [GridState.mem_columnSwapNeighbors]
    exact ⟨D.first.left, D.first.right, D.first.left_ne_right, D.target_eq_commuted h⟩

/-! ### Reordering preserves emptiness -/

/-- The interior of the first rectangle of a decomposition, as a product of cyclic arcs of the
source state. -/
private theorem mem_interior_first_iff (D : GridRectangleDecomposition x z)
    (p : Fin n × Fin n) :
    p ∈ D.first.toGridRectangle.interior ↔
      p.1 ∈ Grid.cIoo D.first.left D.first.right ∧
        p.2 ∈ Grid.cIoo (x D.first.left) (x D.first.right) := by
  simp [GridRectangleBetween.bottom, GridRectangleBetween.top]

/-- The interior of the second rectangle of a decomposition with disjoint side columns, as a
product of cyclic arcs of the *source* state: the intermediate state agrees with the source away
from the first pair of side columns. -/
private theorem mem_interior_second_iff (D : GridRectangleDecomposition x z)
    (h : D.HasDisjointSides) (p : Fin n × Fin n) :
    p ∈ D.second.toGridRectangle.interior ↔
      p.1 ∈ Grid.cIoo D.second.left D.second.right ∧
        p.2 ∈ Grid.cIoo (x D.second.left) (x D.second.right) := by
  obtain ⟨hll, hlr, hrl, hrr⟩ := D.hasDisjointSides_iff.mp h
  have hleft : D.middle D.second.left = x D.second.left :=
    D.first.map_of_ne _ hll.symm hrl.symm
  have hright : D.middle D.second.right = x D.second.right :=
    D.first.map_of_ne _ hlr.symm hrr.symm
  simp [GridRectangleBetween.bottom, GridRectangleBetween.top, hleft, hright]

/-- The intermediate state of a decomposition occupies the initial side column of the first
rectangle in the terminal row. -/
private theorem first_left_mem_middle_pointSet (D : GridRectangleDecomposition x z) :
    (D.first.left, x D.first.right) ∈ D.middle.pointSet :=
  (D.middle.mk_mem_pointSet _ _).mpr D.first.map_left

/-- The intermediate state of a decomposition occupies the terminal side column of the first
rectangle in the initial row. -/
private theorem first_right_mem_middle_pointSet (D : GridRectangleDecomposition x z) :
    (D.first.right, x D.first.left) ∈ D.middle.pointSet :=
  (D.middle.mk_mem_pointSet _ _).mpr D.first.map_right

/-- Reordering two empty rectangles with disjoint side columns leaves the new first rectangle
empty.

Its domain is the old second domain, which is empty for the intermediate state. The two states
differ only in the first pair of side columns, and if either of those two source points fell
inside the domain, then the cyclic separation forced on the four columns and on the four rows
would put a source point inside the first domain instead. -/
theorem isEmpty_commute_first (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides)
    (h₁ : D.first.IsEmpty) (h₂ : D.second.IsEmpty) : (D.commute h).first.IsEmpty := by
  obtain ⟨hll, hlr, hrl, hrr⟩ := D.hasDisjointSides_iff.mp h
  have hxcd : x D.second.left ≠ x D.second.right :=
    fun hx => D.second.left_ne_right (x.toPerm.injective hx)
  -- the two intermediate-state points off the second pair of side columns
  have hmid₁ := D.mem_interior_second_iff h (D.first.left, x D.first.right)
  have hmid₂ := D.mem_interior_second_iff h (D.first.right, x D.first.left)
  have hout₁ : ¬((D.first.left ∈ Grid.cIoo D.second.left D.second.right) ∧
      x D.first.right ∈ Grid.cIoo (x D.second.left) (x D.second.right)) :=
    fun hc => D.second.not_mem_interior_of_isEmpty h₂ D.first_left_mem_middle_pointSet
      (hmid₁.mpr hc)
  have hout₂ : ¬((D.first.right ∈ Grid.cIoo D.second.left D.second.right) ∧
      x D.first.left ∈ Grid.cIoo (x D.second.left) (x D.second.right)) :=
    fun hc => D.second.not_mem_interior_of_isEmpty h₂ D.first_right_mem_middle_pointSet
      (hmid₂.mpr hc)
  rw [GridRectangleBetween.isEmpty_iff]
  intro p hp hmem
  rw [D.commute_first_toGridRectangle h, D.mem_interior_second_iff h] at hmem
  obtain ⟨hcol, hrow⟩ := hmem
  have hpx : x p.1 = p.2 := (x.mem_pointSet p).mp hp
  by_cases hpleft : p.1 = D.first.left
  · -- the source point on the initial side column of the first rectangle
    rw [← hpx] at hrow
    rw [hpleft] at hcol hrow
    have hb : D.first.right ∈ Grid.cIoo D.second.right D.second.left :=
      ((Grid.mem_cIoo_or_mem_cIoo_swap_iff D.second.left_ne_right).mpr
        ⟨hrl, hrr⟩).resolve_left fun hc => hout₂ ⟨hc, hrow⟩
    have hxb : x D.first.right ∈
        Grid.cIoo (x D.second.right) (x D.second.left) :=
      ((Grid.mem_cIoo_or_mem_cIoo_swap_iff hxcd).mpr
        ⟨fun hc => hrl (x.toPerm.injective hc),
          fun hc => hrr (x.toPerm.injective hc)⟩).resolve_left
        fun hc => hout₁ ⟨hcol, hc⟩
    exact D.first.not_mem_interior_of_isEmpty h₁
      ((x.mk_mem_pointSet D.second.right (x D.second.right)).mpr rfl)
      ((D.mem_interior_first_iff _).mpr
        ⟨Grid.mem_cIoo_of_mem_cIoo_of_mem_cIoo_swap hcol hb,
          Grid.mem_cIoo_of_mem_cIoo_of_mem_cIoo_swap hrow hxb⟩)
  by_cases hpright : p.1 = D.first.right
  · -- the source point on the terminal side column of the first rectangle
    rw [← hpx] at hrow
    rw [hpright] at hcol hrow
    have ha : D.first.left ∈ Grid.cIoo D.second.right D.second.left :=
      ((Grid.mem_cIoo_or_mem_cIoo_swap_iff D.second.left_ne_right).mpr
        ⟨hll, hlr⟩).resolve_left fun hc => hout₁ ⟨hc, hrow⟩
    have hxa : x D.first.left ∈
        Grid.cIoo (x D.second.right) (x D.second.left) :=
      ((Grid.mem_cIoo_or_mem_cIoo_swap_iff hxcd).mpr
        ⟨fun hc => hll (x.toPerm.injective hc),
          fun hc => hlr (x.toPerm.injective hc)⟩).resolve_left
        fun hc => hout₂ ⟨hcol, hc⟩
    exact D.first.not_mem_interior_of_isEmpty h₁
      ((x.mk_mem_pointSet D.second.left (x D.second.left)).mpr rfl)
      ((D.mem_interior_first_iff _).mpr
        ⟨Grid.mem_cIoo_swap_of_mem_cIoo_of_mem_cIoo_swap hcol ha,
          Grid.mem_cIoo_swap_of_mem_cIoo_of_mem_cIoo_swap hrow hxa⟩)
  · -- away from the first pair of side columns the two states agree
    exact D.second.not_mem_interior_of_isEmpty h₂
      ((D.middle.mem_pointSet p).mpr (by rw [D.first.map_of_ne p.1 hpleft hpright, hpx]))
      ((D.mem_interior_second_iff h p).mpr ⟨hcol, hrow⟩)

/-- Reordering two empty rectangles with disjoint side columns leaves the new second rectangle
empty.

Its domain is the old first domain, which is empty for the source state. The new source state
differs from the source only in the second pair of side columns, and if either of those two points
fell inside the domain, then the cyclic separation forced on the four columns and on the four rows
would put an intermediate-state point inside the second domain instead. -/
theorem isEmpty_commute_second (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides)
    (h₁ : D.first.IsEmpty) (h₂ : D.second.IsEmpty) : (D.commute h).second.IsEmpty := by
  obtain ⟨hll, hlr, hrl, hrr⟩ := D.hasDisjointSides_iff.mp h
  have hxab : x D.first.left ≠ x D.first.right :=
    fun hx => D.first.left_ne_right (x.toPerm.injective hx)
  -- the two source points on the second pair of side columns
  have hout₁ : ¬((D.second.left ∈ Grid.cIoo D.first.left D.first.right) ∧
      x D.second.left ∈ Grid.cIoo (x D.first.left) (x D.first.right)) :=
    fun hc => D.first.not_mem_interior_of_isEmpty h₁
      ((x.mk_mem_pointSet D.second.left (x D.second.left)).mpr rfl)
      ((D.mem_interior_first_iff _).mpr hc)
  have hout₂ : ¬((D.second.right ∈ Grid.cIoo D.first.left D.first.right) ∧
      x D.second.right ∈ Grid.cIoo (x D.first.left) (x D.first.right)) :=
    fun hc => D.first.not_mem_interior_of_isEmpty h₁
      ((x.mk_mem_pointSet D.second.right (x D.second.right)).mpr rfl)
      ((D.mem_interior_first_iff _).mpr hc)
  rw [GridRectangleBetween.isEmpty_iff]
  intro p hp hmem
  rw [D.commute_second_toGridRectangle h, D.mem_interior_first_iff] at hmem
  obtain ⟨hcol, hrow⟩ := hmem
  have hpx : x (Equiv.swap D.second.left D.second.right p.1) = p.2 := by
    have := ((D.commute h).middle.mem_pointSet p).mp hp
    rwa [D.commute_middle h, GridState.swapColumns_apply] at this
  by_cases hpleft : p.1 = D.second.left
  · -- the point of the new source state on the initial side column of the second rectangle
    rw [hpleft, Equiv.swap_apply_left] at hpx
    rw [← hpx] at hrow
    rw [hpleft] at hcol
    have hd : D.second.right ∈ Grid.cIoo D.first.right D.first.left :=
      ((Grid.mem_cIoo_or_mem_cIoo_swap_iff D.first.left_ne_right).mpr
        ⟨hlr.symm, hrr.symm⟩).resolve_left fun hc => hout₂ ⟨hc, hrow⟩
    have hxc : x D.second.left ∈ Grid.cIoo (x D.first.right) (x D.first.left) :=
      ((Grid.mem_cIoo_or_mem_cIoo_swap_iff hxab).mpr
        ⟨fun hc => hll.symm (x.toPerm.injective hc),
          fun hc => hrl.symm (x.toPerm.injective hc)⟩).resolve_left
        fun hc => hout₁ ⟨hcol, hc⟩
    exact D.second.not_mem_interior_of_isEmpty h₂ D.first_right_mem_middle_pointSet
      ((D.mem_interior_second_iff h _).mpr
        ⟨Grid.mem_cIoo_of_mem_cIoo_of_mem_cIoo_swap hcol hd,
          Grid.mem_cIoo_swap_of_mem_cIoo_of_mem_cIoo_swap hrow hxc⟩)
  by_cases hpright : p.1 = D.second.right
  · -- the point of the new source state on the terminal side column of the second rectangle
    rw [hpright, Equiv.swap_apply_right] at hpx
    rw [← hpx] at hrow
    rw [hpright] at hcol
    have hc : D.second.left ∈ Grid.cIoo D.first.right D.first.left :=
      ((Grid.mem_cIoo_or_mem_cIoo_swap_iff D.first.left_ne_right).mpr
        ⟨hll.symm, hrl.symm⟩).resolve_left fun hc => hout₁ ⟨hc, hrow⟩
    have hxd : x D.second.right ∈ Grid.cIoo (x D.first.right) (x D.first.left) :=
      ((Grid.mem_cIoo_or_mem_cIoo_swap_iff hxab).mpr
        ⟨fun hc => hlr.symm (x.toPerm.injective hc),
          fun hc => hrr.symm (x.toPerm.injective hc)⟩).resolve_left
        fun hc => hout₂ ⟨hcol, hc⟩
    exact D.second.not_mem_interior_of_isEmpty h₂ D.first_left_mem_middle_pointSet
      ((D.mem_interior_second_iff h _).mpr
        ⟨Grid.mem_cIoo_swap_of_mem_cIoo_of_mem_cIoo_swap hcol hc,
          Grid.mem_cIoo_of_mem_cIoo_of_mem_cIoo_swap hrow hxd⟩)
  · -- away from the second pair of side columns the two states agree
    rw [Equiv.swap_apply_of_ne_of_ne hpleft hpright] at hpx
    exact D.first.not_mem_interior_of_isEmpty h₁ ((x.mem_pointSet p).mpr hpx)
      ((D.mem_interior_first_iff p).mpr ⟨hcol, hrow⟩)

/-- Reordering a two-step decomposition into two empty rectangles with disjoint side columns
again gives two empty rectangles. -/
theorem isEmpty_and_isEmpty_commute (D : GridRectangleDecomposition x z)
    (h : D.HasDisjointSides) (h₁ : D.first.IsEmpty) (h₂ : D.second.IsEmpty) :
    (D.commute h).first.IsEmpty ∧ (D.commute h).second.IsEmpty :=
  ⟨D.isEmpty_commute_first h h₁ h₂, D.isEmpty_commute_second h h₁ h₂⟩

end GridRectangleDecomposition

end TauCeti
