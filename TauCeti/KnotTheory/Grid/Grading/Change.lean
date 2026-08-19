/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.Ring
public import TauCeti.KnotTheory.Grid.Gradings
public import TauCeti.KnotTheory.Grid.Rectangle.Swap

/-!
# Grading changes across a rectangle move

This file records how the Maslov and Alexander gradings of two grid states differ, first as a
pure identity between the grading formulas of any two states, then localized to the four corners
of a rectangle move.

The two Maslov gradings split the same way: their difference is the change in the state's
`J`-self-pairing minus twice the change in the marking pairing,
`M_O(x) - M_O(y) = (J(x, x) - J(y, y)) - 2 (J_O(x) - J_O(y))`, and similarly for `M_X`. The
state-self-pairing term is identical in both Maslov gradings, so it cancels in the Alexander
grading, leaving the clean marking-only identity
`A(x) - A(y) = (J_X(x) - J_X(y)) - (J_O(x) - J_O(y))`. None of these three reductions needs any
relationship between `x` and `y`.

When `y` is obtained from `x` by a rectangle move `R : GridRectangleBetween x y`, the two states
share all but two of their occupied squares (`RectangleSwap.lean`), so each marking pairing
`J_O(x) - J_O(y)` collapses to a difference of four corner `J`-singletons: the source corners
`(left, bottom)`, `(right, top)` against the target corners `(left, top)`, `(right, bottom)`.
For Maslov gradings the state self-pairing does not cancel, so this file also localizes its
change to the moving corners and their pairings with the shared part of the two states. Feeding
these localized formulas back into the grading reductions removes the opaque whole-state
self-pairing term from the rectangle Maslov formulas, while the Alexander formula remains purely
marking-local because the state self-pairing cancels there.

## Main results

* `TauCeti.GridDiagram.maslovO_sub_maslovO_eq`, `TauCeti.GridDiagram.maslovX_sub_maslovX_eq`: the
  difference of a Maslov grading at two states splits into the state self-pairing change and
  twice the marking pairing change.
* `TauCeti.GridDiagram.alexander_sub_alexander_eq`: the Alexander grading change is the difference
  of the two marking pairing changes; the state self-pairing cancels.
* `TauCeti.GridRectangleBetween.JCentre_pointSet_sub_eq`,
  `TauCeti.GridRectangleBetween.J_pointSet_sub_eq`: across a rectangle move, the change in the
  pairing of a state's points against an arbitrary fixed point set collapses to the four moving
  corners, for the marking pairing and for the plain `J`-pairing alike.
* `TauCeti.GridDiagram.JO_sub_JO_eq`, `TauCeti.GridDiagram.JX_sub_JX_eq`: across a
  rectangle move the marking pairing change is a difference of four corner `J`-singletons.
* `TauCeti.GridRectangleBetween.J_self_sub_J_self_eq`: across a rectangle move, the state
  self-pairing change is localized to the moving corners and the shared state points.
* `TauCeti.GridDiagram.alexander_change_rectangle`,
  `TauCeti.GridDiagram.maslovO_change_rectangle`,
  `TauCeti.GridDiagram.maslovX_change_rectangle`: the grading changes across a rectangle move,
  localized to the four corners.

## References

This supplies the rectangle grading-change part of
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.2, "Gradings. The `J`-function,
`M_O`, `M_X`, `A`; integer-valuedness of `A`; grading-change formulas across a rectangle." The
formulas follow the `J`-function bookkeeping in Ozsváth--Stipsicz--Szabó, *Grid Homology for
Knots and Links*, Chapters 3 and 4.
-/

public section

namespace TauCeti

namespace GridPoint

variable {n : ℕ}

/-- Splitting a two-point insertion out of the left argument of the `J`-function. The two fresh
points contribute their singleton pairings and the rest is untouched; this is the bookkeeping a
corner-localized grading-change computation rests on. -/
private theorem J_insert_pair_left {S P : Finset (Fin n × Fin n)} {a b : Fin n × Fin n}
    (hab : a ∉ insert b S) (hb : b ∉ S) :
    GridPoint.J (insert a (insert b S)) P =
      GridPoint.J {a} P + GridPoint.J {b} P + GridPoint.J S P := by
  rw [GridPoint.J_insert_left hab, GridPoint.J_insert_left hb, add_assoc]

/-- Splitting a two-point insertion out of the grid points of the marking pairing. The two fresh
grid points contribute their singleton pairings and the rest is untouched. -/
private theorem JCentre_insert_pair_left {S P : Finset (Fin n × Fin n)} {a b : Fin n × Fin n}
    (hab : a ∉ insert b S) (hb : b ∉ S) :
    GridPoint.JCentre (insert a (insert b S)) P =
      GridPoint.JCentre {a} P + GridPoint.JCentre {b} P + GridPoint.JCentre S P := by
  rw [GridPoint.JCentre_insert_left hab, GridPoint.JCentre_insert_left hb, add_assoc]

/-- Splitting a two-point insertion out of the right argument of the `J`-function. -/
private theorem J_insert_pair_right {S P : Finset (Fin n × Fin n)} {a b : Fin n × Fin n}
    (hab : a ∉ insert b S) (hb : b ∉ S) :
    GridPoint.J P (insert a (insert b S)) =
      GridPoint.J P {a} + GridPoint.J P {b} + GridPoint.J P S := by
  rw [GridPoint.J_comm P, J_insert_pair_left hab hb, GridPoint.J_comm {a} P,
    GridPoint.J_comm {b} P, GridPoint.J_comm S P]

/-- The self-pairing of a point set after inserting two fresh points. The singleton self-terms
vanish, leaving the pair contribution, the two pairings with the old set, and the old
self-pairing. -/
private theorem J_insert_pair_self {S : Finset (Fin n × Fin n)} {a b : Fin n × Fin n}
    (hab : a ∉ insert b S) (hb : b ∉ S) :
    GridPoint.J (insert a (insert b S)) (insert a (insert b S)) =
      2 * (GridPoint.J {a} {b} + GridPoint.J {a} S + GridPoint.J {b} S) +
        GridPoint.J S S := by
  have hleft := J_insert_pair_left (P := insert a (insert b S)) hab hb
  have ha := J_insert_pair_right (P := {a}) hab hb
  have hb' := J_insert_pair_right (P := {b}) hab hb
  have hS := J_insert_pair_right (P := S) hab hb
  rw [hleft, ha, hb', hS, GridPoint.J_comm {b} {a}, GridPoint.J_comm S {a},
    GridPoint.J_comm S {b}]
  simp only [GridPoint.J_singleton_self]
  ring

end GridPoint

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n} (R : GridRectangleBetween x y)

/-- The source corner `(left, bottom)` is distinct from the other source corner `(right, top)`
and avoids the shared part of the two states, so it does not lie in their insertion. -/
private theorem left_bottom_notMem_insert_inter :
    (R.left, R.bottom) ∉ insert (R.right, R.top) (x.pointSet ∩ y.pointSet) := by
  simp only [Finset.mem_insert, not_or]
  exact ⟨fun h => R.left_ne_right (Prod.ext_iff.mp h).1, R.left_bottom_notMem_inter⟩

/-- The target corner `(left, top)` is distinct from the other target corner `(right, bottom)`
and avoids the shared part of the two states, so it does not lie in their insertion. -/
private theorem left_top_notMem_insert_inter :
    (R.left, R.top) ∉ insert (R.right, R.bottom) (x.pointSet ∩ y.pointSet) := by
  simp only [Finset.mem_insert, not_or]
  exact ⟨fun h => R.left_ne_right (Prod.ext_iff.mp h).1, R.left_top_notMem_inter⟩

/-- Across a rectangle move, the change in the state self-pairing is localized to the four
moving corners and their pairings with the shared part of the two states. This removes the
opaque `GridState.J x x - GridState.J y y` term from the Maslov grading-change formulas. -/
theorem J_self_sub_J_self_eq :
    GridState.J x x - GridState.J y y =
      2 * ((GridPoint.J {(R.left, R.bottom)} {(R.right, R.top)} +
              GridPoint.J {(R.left, R.bottom)} (x.pointSet ∩ y.pointSet) +
              GridPoint.J {(R.right, R.top)} (x.pointSet ∩ y.pointSet)) -
            (GridPoint.J {(R.left, R.top)} {(R.right, R.bottom)} +
              GridPoint.J {(R.left, R.top)} (x.pointSet ∩ y.pointSet) +
              GridPoint.J {(R.right, R.bottom)} (x.pointSet ∩ y.pointSet))) := by
  have key₁ :=
    GridPoint.J_insert_pair_self R.left_bottom_notMem_insert_inter R.right_top_notMem_inter
  have key₂ :=
    GridPoint.J_insert_pair_self R.left_top_notMem_insert_inter R.right_bottom_notMem_inter
  rw [← R.source_pointSet_eq] at key₁
  rw [← R.target_pointSet_eq] at key₂
  rw [GridState.J_def, GridState.J_def]
  rw [key₁, key₂]
  ring

/-- Across a rectangle move, the change in the pairing of a state's points against an arbitrary
fixed point set `P` collapses to the four moving corners: the source corners `(left, bottom)`,
`(right, top)` against the target corners `(left, top)`, `(right, bottom)`. The shared part of the
two states cancels. The marking-pairing localizations specialize this at the `O`- and
`X`-marking sets. -/
theorem JCentre_pointSet_sub_eq (P : Finset (Fin n × Fin n)) :
    GridPoint.JCentre x.pointSet P - GridPoint.JCentre y.pointSet P =
      (GridPoint.JCentre {(R.left, R.bottom)} P + GridPoint.JCentre {(R.right, R.top)} P) -
        (GridPoint.JCentre {(R.left, R.top)} P + GridPoint.JCentre {(R.right, R.bottom)} P) := by
  have key₁ :=
    GridPoint.JCentre_insert_pair_left (P := P) R.left_bottom_notMem_insert_inter
      R.right_top_notMem_inter
  have key₂ :=
    GridPoint.JCentre_insert_pair_left (P := P) R.left_top_notMem_insert_inter
      R.right_bottom_notMem_inter
  rw [← R.source_pointSet_eq] at key₁
  rw [← R.target_pointSet_eq] at key₂
  rw [key₁, key₂]
  ring

/-- Across a rectangle move, the change in the `J`-pairing of a state's points against an
arbitrary fixed point set `P` collapses to the four moving corners. -/
theorem J_pointSet_sub_eq (P : Finset (Fin n × Fin n)) :
    GridPoint.J x.pointSet P - GridPoint.J y.pointSet P =
      (GridPoint.J {(R.left, R.bottom)} P + GridPoint.J {(R.right, R.top)} P) -
        (GridPoint.J {(R.left, R.top)} P + GridPoint.J {(R.right, R.bottom)} P) := by
  have key₁ :=
    GridPoint.J_insert_pair_left (P := P) R.left_bottom_notMem_insert_inter R.right_top_notMem_inter
  have key₂ :=
    GridPoint.J_insert_pair_left (P := P) R.left_top_notMem_insert_inter R.right_bottom_notMem_inter
  rw [← R.source_pointSet_eq] at key₁
  rw [← R.target_pointSet_eq] at key₂
  rw [key₁, key₂]
  ring

end GridRectangleBetween

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The difference of the `O`-Maslov grading at two grid states splits into the change in the
state self-pairing and twice the change in the `O`-marking pairing. The two states need not be
related: this is the algebraic shape of the grading formula. -/
theorem maslovO_sub_maslovO_eq (x y : GridState n) :
    G.maslovO x - G.maslovO y =
      (GridState.J x x - GridState.J y y) - 2 * (G.JO x - G.JO y) := by
  rw [maslovO_eq, maslovO_eq]
  ring

/-- The difference of the `X`-Maslov grading at two grid states splits into the change in the
state self-pairing and twice the change in the `X`-marking pairing. -/
theorem maslovX_sub_maslovX_eq (x y : GridState n) :
    G.maslovX x - G.maslovX y =
      (GridState.J x x - GridState.J y y) - 2 * (G.JX x - G.JX y) := by
  rw [maslovX_eq, maslovX_eq]
  ring

/-- The Alexander grading change at two grid states is the difference of the two marking pairing
changes. The state self-pairing term is common to both Maslov gradings and the normalization
shift depends only on the grid size, so both cancel, leaving a marking-only identity that needs
no relationship between `x` and `y`. -/
theorem alexander_sub_alexander_eq (x y : GridState n) :
    G.alexander x - G.alexander y = (G.JX x - G.JX y) - (G.JO x - G.JO y) := by
  rw [alexander_eq, alexander_eq]
  ring

variable {x y : GridState n}

/-- Across a rectangle move the `O`-marking pairing change collapses to the four corners: the
source corners `(left, bottom)`, `(right, top)` against the target corners `(left, top)`,
`(right, bottom)`. The two states share all but their corners, and the shared part cancels. -/
theorem JO_sub_JO_eq (R : GridRectangleBetween x y) :
    G.JO x - G.JO y =
      (GridPoint.JCentre {(R.left, R.bottom)} G.OSet +
          GridPoint.JCentre {(R.right, R.top)} G.OSet) -
        (GridPoint.JCentre {(R.left, R.top)} G.OSet +
          GridPoint.JCentre {(R.right, R.bottom)} G.OSet) := by
  rw [JO_def, JO_def]
  exact R.JCentre_pointSet_sub_eq G.OSet

/-- Across a rectangle move the `X`-marking pairing change collapses to the four corners. -/
theorem JX_sub_JX_eq (R : GridRectangleBetween x y) :
    G.JX x - G.JX y =
      (GridPoint.JCentre {(R.left, R.bottom)} G.XSet +
          GridPoint.JCentre {(R.right, R.top)} G.XSet) -
        (GridPoint.JCentre {(R.left, R.top)} G.XSet +
          GridPoint.JCentre {(R.right, R.bottom)} G.XSet) := by
  rw [JX_def, JX_def]
  exact R.JCentre_pointSet_sub_eq G.XSet

/-- The Alexander grading change across a rectangle move, localized to the four corners: it is the
four `X`-corner pairings minus the four `O`-corner pairings, in each case the two source corners
against the two target corners. The state self-pairing cancels (`alexander_sub_alexander_eq`) and
the shared squares cancel (`JX_sub_JX_eq`, `JO_sub_JO_eq`). -/
theorem alexander_change_rectangle (R : GridRectangleBetween x y) :
    G.alexander x - G.alexander y =
      ((GridPoint.JCentre {(R.left, R.bottom)} G.XSet +
            GridPoint.JCentre {(R.right, R.top)} G.XSet) -
          (GridPoint.JCentre {(R.left, R.top)} G.XSet +
            GridPoint.JCentre {(R.right, R.bottom)} G.XSet)) -
        ((GridPoint.JCentre {(R.left, R.bottom)} G.OSet +
            GridPoint.JCentre {(R.right, R.top)} G.OSet) -
          (GridPoint.JCentre {(R.left, R.top)} G.OSet +
            GridPoint.JCentre {(R.right, R.bottom)} G.OSet)) := by
  rw [alexander_sub_alexander_eq, JX_sub_JX_eq G R, JO_sub_JO_eq G R]

/-- The `O`-Maslov grading change across a rectangle move, with both the state self-pairing
change and the `O`-marking pairing change localized to the rectangle corners. -/
theorem maslovO_change_rectangle (R : GridRectangleBetween x y) :
    G.maslovO x - G.maslovO y =
      2 * ((GridPoint.J {(R.left, R.bottom)} {(R.right, R.top)} +
              GridPoint.J {(R.left, R.bottom)} (x.pointSet ∩ y.pointSet) +
              GridPoint.J {(R.right, R.top)} (x.pointSet ∩ y.pointSet)) -
            (GridPoint.J {(R.left, R.top)} {(R.right, R.bottom)} +
              GridPoint.J {(R.left, R.top)} (x.pointSet ∩ y.pointSet) +
              GridPoint.J {(R.right, R.bottom)} (x.pointSet ∩ y.pointSet))) -
        2 * ((GridPoint.JCentre {(R.left, R.bottom)} G.OSet +
              GridPoint.JCentre {(R.right, R.top)} G.OSet) -
          (GridPoint.JCentre {(R.left, R.top)} G.OSet +
            GridPoint.JCentre {(R.right, R.bottom)} G.OSet)) := by
  rw [maslovO_sub_maslovO_eq, R.J_self_sub_J_self_eq, JO_sub_JO_eq G R]

/-- The `X`-Maslov grading change across a rectangle move, with both the state self-pairing
change and the `X`-marking pairing change localized to the rectangle corners. -/
theorem maslovX_change_rectangle (R : GridRectangleBetween x y) :
    G.maslovX x - G.maslovX y =
      2 * ((GridPoint.J {(R.left, R.bottom)} {(R.right, R.top)} +
              GridPoint.J {(R.left, R.bottom)} (x.pointSet ∩ y.pointSet) +
              GridPoint.J {(R.right, R.top)} (x.pointSet ∩ y.pointSet)) -
            (GridPoint.J {(R.left, R.top)} {(R.right, R.bottom)} +
              GridPoint.J {(R.left, R.top)} (x.pointSet ∩ y.pointSet) +
              GridPoint.J {(R.right, R.bottom)} (x.pointSet ∩ y.pointSet))) -
        2 * ((GridPoint.JCentre {(R.left, R.bottom)} G.XSet +
              GridPoint.JCentre {(R.right, R.top)} G.XSet) -
          (GridPoint.JCentre {(R.left, R.top)} G.XSet +
            GridPoint.JCentre {(R.right, R.bottom)} G.XSet)) := by
  rw [maslovX_sub_maslovX_eq, R.J_self_sub_J_self_eq, JX_sub_JX_eq G R]

end GridDiagram

end TauCeti
