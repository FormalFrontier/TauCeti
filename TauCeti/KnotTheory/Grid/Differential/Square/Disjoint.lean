/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.Intermediates
public import TauCeti.KnotTheory.Grid.Rectangle.Swap

/-!
# Reordering rectangle decompositions with disjoint side columns

A two-step term in the square of the grid differential consists of a rectangle from `x` to an
intermediate state and a second rectangle from that state to `z`. When the two rectangles use
disjoint pairs of side columns, their column transpositions commute. They may therefore be applied
in the opposite order, through a different intermediate state.

This file packages such a two-step factorization as `GridRectangleDecomposition` and constructs
its reordered factorization. The first reordered rectangle has exactly the toroidal domain of the
old second rectangle, and conversely for the second. In particular, both marking-avoidance
conditions are preserved. Reordering is an involution and changes the intermediate state, giving
the fixed-point-free pairing needed in the disjoint-side case of the eventual rectangle
juxtaposition argument.

This is purely the orientation and domain bookkeeping. Empty-rectangle transfer needs the
geometric case split controlling how the two domains meet; the overlapping and annular cases also
remain separate parts of the square-zero proof.

## Main definitions

* `TauCeti.GridRectangleDecomposition`: two composable oriented grid rectangles.
* `TauCeti.GridRectangleDecomposition.HasDisjointSides`: the two side-column pairs are disjoint.
* `TauCeti.GridRectangleDecomposition.commute`: apply two rectangles with disjoint side columns
  in the opposite order.

## Main results

* `TauCeti.GridRectangleDecomposition.commute_first_toGridRectangle` and
  `commute_second_toGridRectangle`: reordering exchanges the two toroidal domains.
* `TauCeti.GridRectangleDecomposition.commute_avoidsMarkings_iff`: reordering preserves both
  marking-avoidance conditions.
* `TauCeti.GridRectangleDecomposition.commute_commute`: reordering twice is the identity.
* `TauCeti.GridRectangleDecomposition.commute_middle_ne`: the intermediate state changes.

## References

This supplies the disjoint-side orientation step for
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, "The complexes and `∂² = 0`".
The decomposition pairing follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*,
Chapter 4.6.
-/

public section

namespace TauCeti

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

end GridRectangleBetween

/-- A decomposition of a two-step rectangle domain from `x` to `z` through an intermediate grid
state. -/
structure GridRectangleDecomposition {n : ℕ} (x z : GridState n) where
  /-- The grid state between the two rectangle moves. -/
  middle : GridState n
  /-- The first oriented rectangle, from the source to the intermediate state. -/
  first : GridRectangleBetween x middle
  /-- The second oriented rectangle, from the intermediate state to the target. -/
  second : GridRectangleBetween middle z

namespace GridRectangleDecomposition

variable {n : ℕ} {x z : GridState n}

/-- Two rectangle decompositions are equal when their intermediate states and ordered side
columns agree. -/
@[ext]
theorem ext {D E : GridRectangleDecomposition x z} (hmiddle : D.middle = E.middle)
    (hfirstLeft : D.first.left = E.first.left)
    (hfirstRight : D.first.right = E.first.right)
    (hsecondLeft : D.second.left = E.second.left)
    (hsecondRight : D.second.right = E.second.right) : D = E := by
  cases D with
  | mk Dmiddle Dfirst Dsecond =>
      cases E with
      | mk Emiddle Efirst Esecond =>
          dsimp only at hmiddle
          subst Emiddle
          have hfirst : Dfirst = Efirst :=
            GridRectangleBetween.eq_of_sides hfirstLeft hfirstRight
          subst Efirst
          have hsecond : Dsecond = Esecond :=
            GridRectangleBetween.eq_of_sides hsecondLeft hsecondRight
          subst Esecond
          rfl

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
theorem commute_first_avoidsMarkings_iff (D : GridRectangleDecomposition x z)
    (h : D.HasDisjointSides) (G : GridDiagram n) :
    (D.commute h).first.AvoidsMarkings G ↔ D.second.AvoidsMarkings G := by
  unfold GridRectangleBetween.AvoidsMarkings
  rw [D.commute_first_toGridRectangle h]

/-- Reordering preserves the marking-avoidance condition on the second domain. -/
theorem commute_second_avoidsMarkings_iff (D : GridRectangleDecomposition x z)
    (h : D.HasDisjointSides) (G : GridDiagram n) :
    (D.commute h).second.AvoidsMarkings G ↔ D.first.AvoidsMarkings G := by
  unfold GridRectangleBetween.AvoidsMarkings
  rw [D.commute_second_toGridRectangle h]

/-- Reordering preserves both marking-avoidance conditions and exchanges their order. -/
theorem commute_avoidsMarkings_iff (D : GridRectangleDecomposition x z)
    (h : D.HasDisjointSides) (G : GridDiagram n) :
    ((D.commute h).first.AvoidsMarkings G ∧ (D.commute h).second.AvoidsMarkings G) ↔
      D.second.AvoidsMarkings G ∧ D.first.AvoidsMarkings G := by
  rw [D.commute_first_avoidsMarkings_iff h, D.commute_second_avoidsMarkings_iff h]

/-- The reordered decomposition again has disjoint side-column pairs. -/
theorem commute_hasDisjointSides (D : GridRectangleDecomposition x z)
    (h : D.HasDisjointSides) : (D.commute h).HasDisjointSides := by
  rw [HasDisjointSides]
  simpa only [commute_first_left, commute_first_right, commute_second_left,
    commute_second_right, GridRectangleBetween.sideColumns] using h.symm

/-- Reordering two disjoint-side rectangle decompositions twice recovers the original
decomposition. -/
@[simp]
theorem commute_commute (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides) :
    (D.commute h).commute (D.commute_hasDisjointSides h) = D := by
  apply ext
  · simpa [commute] using D.first.target_eq_swapColumns.symm
  · simp
  · simp
  · simp
  · simp

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

end GridRectangleDecomposition

end TauCeti
