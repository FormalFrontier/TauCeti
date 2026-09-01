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

/-- A point off both endpoints and outside one cyclic arc lies on the opposite arc. -/
private theorem mem_cIoo_swap_of_notMem {a b u : Fin n} (hab : a ≠ b)
    (hua : u ≠ a) (hub : u ≠ b) (hout : u ∉ Grid.cIoo a b) : u ∈ Grid.cIoo b a :=
  ((Grid.mem_cIoo_or_mem_cIoo_swap_iff hab).mpr ⟨hua, hub⟩).resolve_left
    hout

/-- Cyclic separation in two coordinates puts both latter endpoints on the corresponding arcs
between the former pair. -/
private theorem endpoints_mem_cIoo_of_separation {a b c d a' b' c' d' : Fin n}
    (hcd : c ≠ d) (hc'd' : c' ≠ d')
    (hbc : b ≠ c) (hbd : b ≠ d) (hb'c' : b' ≠ c') (hb'd' : b' ≠ d')
    (hbout : b ∉ Grid.cIoo c d) (hb'out : b' ∉ Grid.cIoo c' d')
    (ha : a ∈ Grid.cIoo c d) (ha' : a' ∈ Grid.cIoo c' d') :
    d ∈ Grid.cIoo a b ∧ c ∈ Grid.cIoo b a ∧
      d' ∈ Grid.cIoo a' b' ∧ c' ∈ Grid.cIoo b' a' := by
  have hb := mem_cIoo_swap_of_notMem hcd hbc hbd hbout
  have hb' := mem_cIoo_swap_of_notMem hc'd' hb'c' hb'd' hb'out
  exact ⟨Grid.mem_cIoo_of_mem_cIoo_of_mem_cIoo_swap ha hb,
    Grid.mem_cIoo_of_mem_cIoo_of_mem_cIoo_swap hb ha,
    Grid.mem_cIoo_of_mem_cIoo_of_mem_cIoo_swap ha' hb',
    Grid.mem_cIoo_of_mem_cIoo_of_mem_cIoo_swap hb' ha'⟩

/-- The interior of the second rectangle of a decomposition with disjoint side columns, as a
product of cyclic arcs of the *source* state: the intermediate state agrees with the source away
from the first pair of side columns. -/
private theorem mem_interior_second_iff (D : GridRectangleDecomposition x z)
    (h : D.HasDisjointSides) (p : Fin n × Fin n) :
    p ∈ D.second.toGridRectangle.interior ↔
      p.1 ∈ Grid.cIoo D.second.left D.second.right ∧
        p.2 ∈ Grid.cIoo (x D.second.left) (x D.second.right) := by
  obtain ⟨hll, hlr, hrl, hrr⟩ := D.hasDisjointSides_iff.mp h
  rw [D.second.mem_toGridRectangle_interior,
    D.first.map_of_ne D.second.left hll.symm hrl.symm,
    D.first.map_of_ne D.second.right hlr.symm hrr.symm]

/-- Reordering two empty rectangles with disjoint side columns leaves the new first rectangle
empty.

Its domain is the old second domain, which is empty for the intermediate state. The two states
differ only in the first pair of side columns, and if either of those two source points fell
inside the domain, then the cyclic separation forced on the four columns and on the four rows
would put a source point inside the first domain instead. -/
theorem isEmpty_commute_first (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides)
    (h₁ : D.first.IsEmpty) (h₂ : D.second.IsEmpty) : (D.commute h).first.IsEmpty := by
  obtain ⟨hll, hlr, hrl, hrr⟩ := D.hasDisjointSides_iff.mp h
  -- the two intermediate-state points off the second pair of side columns
  have hmid₁ := D.mem_interior_second_iff h (D.first.left, x D.first.right)
  have hmid₂ := D.mem_interior_second_iff h (D.first.right, x D.first.left)
  have hout₁ : ¬((D.first.left ∈ Grid.cIoo D.second.left D.second.right) ∧
      x D.first.right ∈ Grid.cIoo (x D.second.left) (x D.second.right)) :=
    fun hc => D.second.not_mem_interior_of_isEmpty h₂ D.first.left_top_mem_target
      (hmid₁.mpr hc)
  have hout₂ : ¬((D.first.right ∈ Grid.cIoo D.second.left D.second.right) ∧
      x D.first.left ∈ Grid.cIoo (x D.second.left) (x D.second.right)) :=
    fun hc => D.second.not_mem_interior_of_isEmpty h₂ D.first.right_bottom_mem_target
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
    have hsep := endpoints_mem_cIoo_of_separation D.second.left_ne_right
      (x.toPerm.injective.ne D.second.left_ne_right) hrl hrr
      (x.toPerm.injective.ne hrl) (x.toPerm.injective.ne hrr)
      (fun hb => hout₂ ⟨hb, hrow⟩) (fun hxb => hout₁ ⟨hcol, hxb⟩) hcol hrow
    exact D.first.not_mem_interior_of_isEmpty h₁
      ((x.mk_mem_pointSet D.second.right (x D.second.right)).mpr rfl)
      ((D.first.mem_toGridRectangle_interior _).mpr ⟨hsep.1, hsep.2.2.1⟩)
  by_cases hpright : p.1 = D.first.right
  · -- the source point on the terminal side column of the first rectangle
    rw [← hpx] at hrow
    rw [hpright] at hcol hrow
    have hsep := endpoints_mem_cIoo_of_separation D.second.left_ne_right
      (x.toPerm.injective.ne D.second.left_ne_right) hll hlr
      (x.toPerm.injective.ne hll) (x.toPerm.injective.ne hlr)
      (fun ha => hout₁ ⟨ha, hrow⟩) (fun hxa => hout₂ ⟨hcol, hxa⟩) hcol hrow
    exact D.first.not_mem_interior_of_isEmpty h₁
      ((x.mk_mem_pointSet D.second.left (x D.second.left)).mpr rfl)
      ((D.first.mem_toGridRectangle_interior _).mpr ⟨hsep.2.1, hsep.2.2.2⟩)
  · -- away from the first pair of side columns the two states agree
    exact D.second.not_mem_interior_of_isEmpty h₂
      ((D.first.mem_target_pointSet_iff_of_ne hpleft hpright).mpr hp)
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
  -- the two source points on the second pair of side columns
  have hout₁ : ¬((D.second.left ∈ Grid.cIoo D.first.left D.first.right) ∧
      x D.second.left ∈ Grid.cIoo (x D.first.left) (x D.first.right)) :=
    fun hc => D.first.not_mem_interior_of_isEmpty h₁
      ((x.mk_mem_pointSet D.second.left (x D.second.left)).mpr rfl)
      ((D.first.mem_toGridRectangle_interior _).mpr hc)
  have hout₂ : ¬((D.second.right ∈ Grid.cIoo D.first.left D.first.right) ∧
      x D.second.right ∈ Grid.cIoo (x D.first.left) (x D.first.right)) :=
    fun hc => D.first.not_mem_interior_of_isEmpty h₁
      ((x.mk_mem_pointSet D.second.right (x D.second.right)).mpr rfl)
      ((D.first.mem_toGridRectangle_interior _).mpr hc)
  rw [GridRectangleBetween.isEmpty_iff]
  intro p hp hmem
  rw [D.commute_second_toGridRectangle h, D.first.mem_toGridRectangle_interior] at hmem
  obtain ⟨hcol, hrow⟩ := hmem
  have hpx : x (Equiv.swap D.second.left D.second.right p.1) = p.2 := by
    have := ((D.commute h).middle.mem_pointSet p).mp hp
    rwa [D.commute_middle h, GridState.swapColumns_apply] at this
  by_cases hpleft : p.1 = D.second.left
  · -- the point of the new source state on the initial side column of the second rectangle
    rw [hpleft, Equiv.swap_apply_left] at hpx
    rw [← hpx] at hrow
    rw [hpleft] at hcol
    have hsep := endpoints_mem_cIoo_of_separation D.first.left_ne_right
      (x.toPerm.injective.ne D.first.left_ne_right) hlr.symm hrr.symm
      (x.toPerm.injective.ne hll.symm) (x.toPerm.injective.ne hrl.symm)
      (fun hd => hout₂ ⟨hd, hrow⟩) (fun hxc => hout₁ ⟨hcol, hxc⟩) hcol hrow
    exact D.second.not_mem_interior_of_isEmpty h₂ D.first.right_bottom_mem_target
      ((D.mem_interior_second_iff h _).mpr ⟨hsep.1, hsep.2.2.2⟩)
  by_cases hpright : p.1 = D.second.right
  · -- the point of the new source state on the terminal side column of the second rectangle
    rw [hpright, Equiv.swap_apply_right] at hpx
    rw [← hpx] at hrow
    rw [hpright] at hcol
    have hsep := endpoints_mem_cIoo_of_separation D.first.left_ne_right
      (x.toPerm.injective.ne D.first.left_ne_right) hll.symm hrl.symm
      (x.toPerm.injective.ne hlr.symm) (x.toPerm.injective.ne hrr.symm)
      (fun hc => hout₁ ⟨hc, hrow⟩) (fun hxd => hout₂ ⟨hcol, hxd⟩) hcol hrow
    exact D.second.not_mem_interior_of_isEmpty h₂ D.first.left_top_mem_target
      ((D.mem_interior_second_iff h _).mpr ⟨hsep.2.1, hsep.2.2.1⟩)
  · -- away from the second pair of side columns the two states agree
    exact D.first.not_mem_interior_of_isEmpty h₁
      (((D.commute h).first.mem_target_pointSet_iff_of_ne
        (by simpa only [commute_first_left] using hpleft)
        (by simpa only [commute_first_right] using hpright)).mp hp)
      ((D.first.mem_toGridRectangle_interior p).mpr ⟨hcol, hrow⟩)

end GridRectangleDecomposition

end TauCeti
