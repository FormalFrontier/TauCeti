/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.Tactic.Ring
public import TauCeti.KnotTheory.Grid.Grading.Change
public import TauCeti.KnotTheory.Grid.Grading.Integer

/-!
# Integer rectangle grading-change formulas

The rational-valued rectangle grading-change formulas of `Grading/Change.lean` and the
integer-valued Maslov and Alexander gradings of `Grading/Integer.lean` combine here: this file
records the four integer-level identities that specialize the rational grading-change chain to
the already-integer Maslov gradings `M_O` and `M_X` and to the integer numerator `2A` of the
Alexander grading.

The general shape is the same as the rational chain: the state self-pairing change and each
marking pairing change collapse to a difference of four corner counts, each corner counted
against the shared part of the two states and against the marking set. At the integer level
these corner counts are the `J`-numerator `JNum` values, so the doubled rational formulas turn
into plain integer identities.

The two intermediate lemmas make the reduction explicit: on any rectangle move the change in
the state self-pairing `I(x, x) - I(y, y)` and the change in any marking pairing
`JNum(x, P) - JNum(y, P)` are both differences of six or four corner `JNum` counts. Feeding
these into the state-difference identities `maslovOℤ_sub_maslovOℤ_eq`,
`maslovXℤ_sub_maslovXℤ_eq`, `alexanderTwoℤ_sub_alexanderTwoℤ_eq` gives the localized
grading-change formulas at the integer level.

## Main results

* `TauCeti.GridDiagram.maslovOℤ_sub_maslovOℤ_eq`,
  `TauCeti.GridDiagram.maslovXℤ_sub_maslovXℤ_eq`,
  `TauCeti.GridDiagram.alexanderTwoℤ_sub_alexanderTwoℤ_eq`: the state-difference identities at
  the integer level.
* `TauCeti.GridRectangleBetween.JNum_pointSet_sub_eq`: across a rectangle move, the change in
  the `JNum`-pairing of a state's point set against an arbitrary fixed point set collapses to
  the four moving corners.
* `TauCeti.GridRectangleBetween.I_self_sub_I_self_eq`: across a rectangle move, the change in
  the state self-pairing `I(·, ·)` is localized to the moving corners and the shared state
  points.
* `TauCeti.GridDiagram.maslovOℤ_change_rectangle`,
  `TauCeti.GridDiagram.maslovXℤ_change_rectangle`,
  `TauCeti.GridDiagram.alexanderTwoℤ_change_rectangle`: the integer grading changes across a
  rectangle move, localized to the four corners.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G item 2,
"Gradings. The `J`-function, `M_O`, `M_X`, `A`; integer-valuedness of `A`; grading-change
formulas across a rectangle." The corner-localized formulas follow the `J`-function
bookkeeping of Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 3
and 4.
-/

public section

namespace TauCeti

namespace GridPoint

variable {n : ℕ}

/-- Splitting a two-point insertion out of the left argument of the `J`-numerator. -/
private theorem JNum_insert_pair_left {S P : Finset (Fin n × Fin n)} {a b : Fin n × Fin n}
    (hab : a ∉ insert b S) (hb : b ∉ S) :
    GridPoint.JNum (insert a (insert b S)) P =
      GridPoint.JNum {a} P + GridPoint.JNum {b} P + GridPoint.JNum S P := by
  rw [GridPoint.JNum_insert_left hab, GridPoint.JNum_insert_left hb, Nat.add_assoc]

/-- Splitting a two-point insertion out of the right argument of the `J`-numerator. -/
private theorem JNum_insert_pair_right {S P : Finset (Fin n × Fin n)} {a b : Fin n × Fin n}
    (hab : a ∉ insert b S) (hb : b ∉ S) :
    GridPoint.JNum P (insert a (insert b S)) =
      GridPoint.JNum P {a} + GridPoint.JNum P {b} + GridPoint.JNum P S := by
  rw [GridPoint.JNum_comm P, JNum_insert_pair_left hab hb,
    GridPoint.JNum_comm {a} P, GridPoint.JNum_comm {b} P, GridPoint.JNum_comm S P]

/-- The self-`JNum` after inserting two fresh points. The singleton self-terms vanish, leaving
the pair contribution, the two pairings with the old set, and the old self-pairing. -/
private theorem JNum_insert_pair_self {S : Finset (Fin n × Fin n)} {a b : Fin n × Fin n}
    (hab : a ∉ insert b S) (hb : b ∉ S) :
    GridPoint.JNum (insert a (insert b S)) (insert a (insert b S)) =
      2 * (GridPoint.JNum {a} {b} + GridPoint.JNum {a} S + GridPoint.JNum {b} S) +
        GridPoint.JNum S S := by
  have hleft := JNum_insert_pair_left (P := insert a (insert b S)) hab hb
  have ha := JNum_insert_pair_right (P := {a}) hab hb
  have hb' := JNum_insert_pair_right (P := {b}) hab hb
  have hS := JNum_insert_pair_right (P := S) hab hb
  have h_aa : GridPoint.JNum {a} {a} = 0 := by
    rw [GridPoint.JNum_self, GridPoint.I_singleton_self]
  have h_bb : GridPoint.JNum {b} {b} = 0 := by
    rw [GridPoint.JNum_self, GridPoint.I_singleton_self]
  rw [hleft, ha, hb', hS, GridPoint.JNum_comm {b} {a}, GridPoint.JNum_comm S {a},
    GridPoint.JNum_comm S {b}, h_aa, h_bb]
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

/-- Across a rectangle move, the change in the `JNum`-pairing of a state's points against an
arbitrary fixed point set `P` collapses to the four moving corners: the source corners
`(left, bottom)`, `(right, top)` against the target corners `(left, top)`, `(right, bottom)`.
The shared part of the two states cancels. This is the integer form of
`J_pointSet_sub_eq`. -/
theorem JNum_pointSet_sub_eq (P : Finset (Fin n × Fin n)) :
    (GridPoint.JNum x.pointSet P : ℤ) - GridPoint.JNum y.pointSet P =
      ((GridPoint.JNum {(R.left, R.bottom)} P : ℤ) + GridPoint.JNum {(R.right, R.top)} P) -
        ((GridPoint.JNum {(R.left, R.top)} P : ℤ) + GridPoint.JNum {(R.right, R.bottom)} P) := by
  have key₁ :=
    GridPoint.JNum_insert_pair_left (P := P) R.left_bottom_notMem_insert_inter
      R.right_top_notMem_inter
  have key₂ :=
    GridPoint.JNum_insert_pair_left (P := P) R.left_top_notMem_insert_inter
      R.right_bottom_notMem_inter
  rw [← R.source_pointSet_eq] at key₁
  rw [← R.target_pointSet_eq] at key₂
  have hxP :
      GridPoint.JNum x.pointSet P =
        GridPoint.JNum {(R.left, R.bottom)} P + GridPoint.JNum {(R.right, R.top)} P +
          GridPoint.JNum (x.pointSet ∩ y.pointSet) P := key₁
  have hyP :
      GridPoint.JNum y.pointSet P =
        GridPoint.JNum {(R.left, R.top)} P + GridPoint.JNum {(R.right, R.bottom)} P +
          GridPoint.JNum (x.pointSet ∩ y.pointSet) P := key₂
  push_cast [hxP, hyP]
  ring

/-- Across a rectangle move, the change in the state self-pairing `I(x, x) - I(y, y)` is
localized to the four moving corners and their pairings with the shared part of the two states.
This is the integer form of `J_self_sub_J_self_eq`, obtained by clearing the factor `2` from
the rational identity: the rational statement is `2 · (…)` because `J s s = I s s` and
`2 · J = JNum` differ by that factor. -/
theorem I_self_sub_I_self_eq :
    (GridPoint.I x.pointSet x.pointSet : ℤ) - GridPoint.I y.pointSet y.pointSet =
      ((GridPoint.JNum {(R.left, R.bottom)} {(R.right, R.top)} : ℤ) +
          GridPoint.JNum {(R.left, R.bottom)} (x.pointSet ∩ y.pointSet) +
          GridPoint.JNum {(R.right, R.top)} (x.pointSet ∩ y.pointSet)) -
        ((GridPoint.JNum {(R.left, R.top)} {(R.right, R.bottom)} : ℤ) +
          GridPoint.JNum {(R.left, R.top)} (x.pointSet ∩ y.pointSet) +
          GridPoint.JNum {(R.right, R.bottom)} (x.pointSet ∩ y.pointSet)) := by
  have key₁ :=
    GridPoint.JNum_insert_pair_self R.left_bottom_notMem_insert_inter R.right_top_notMem_inter
  have key₂ :=
    GridPoint.JNum_insert_pair_self R.left_top_notMem_insert_inter R.right_bottom_notMem_inter
  rw [← R.source_pointSet_eq] at key₁
  rw [← R.target_pointSet_eq] at key₂
  have hxx :
      GridPoint.JNum x.pointSet x.pointSet =
        2 * (GridPoint.JNum {(R.left, R.bottom)} {(R.right, R.top)} +
            GridPoint.JNum {(R.left, R.bottom)} (x.pointSet ∩ y.pointSet) +
            GridPoint.JNum {(R.right, R.top)} (x.pointSet ∩ y.pointSet)) +
          GridPoint.JNum (x.pointSet ∩ y.pointSet) (x.pointSet ∩ y.pointSet) := key₁
  have hyy :
      GridPoint.JNum y.pointSet y.pointSet =
        2 * (GridPoint.JNum {(R.left, R.top)} {(R.right, R.bottom)} +
            GridPoint.JNum {(R.left, R.top)} (x.pointSet ∩ y.pointSet) +
            GridPoint.JNum {(R.right, R.bottom)} (x.pointSet ∩ y.pointSet)) +
          GridPoint.JNum (x.pointSet ∩ y.pointSet) (x.pointSet ∩ y.pointSet) := key₂
  have hxI := GridPoint.JNum_self x.pointSet
  have hyI := GridPoint.JNum_self y.pointSet
  have hxx' : 2 * GridPoint.I x.pointSet x.pointSet =
      2 * (GridPoint.JNum {(R.left, R.bottom)} {(R.right, R.top)} +
            GridPoint.JNum {(R.left, R.bottom)} (x.pointSet ∩ y.pointSet) +
            GridPoint.JNum {(R.right, R.top)} (x.pointSet ∩ y.pointSet)) +
        GridPoint.JNum (x.pointSet ∩ y.pointSet) (x.pointSet ∩ y.pointSet) := hxI ▸ hxx
  have hyy' : 2 * GridPoint.I y.pointSet y.pointSet =
      2 * (GridPoint.JNum {(R.left, R.top)} {(R.right, R.bottom)} +
            GridPoint.JNum {(R.left, R.top)} (x.pointSet ∩ y.pointSet) +
            GridPoint.JNum {(R.right, R.bottom)} (x.pointSet ∩ y.pointSet)) +
        GridPoint.JNum (x.pointSet ∩ y.pointSet) (x.pointSet ∩ y.pointSet) := hyI ▸ hyy
  have hxxZ : (2 * GridPoint.I x.pointSet x.pointSet : ℤ) =
      2 * ((GridPoint.JNum {(R.left, R.bottom)} {(R.right, R.top)} : ℤ) +
            GridPoint.JNum {(R.left, R.bottom)} (x.pointSet ∩ y.pointSet) +
            GridPoint.JNum {(R.right, R.top)} (x.pointSet ∩ y.pointSet)) +
        GridPoint.JNum (x.pointSet ∩ y.pointSet) (x.pointSet ∩ y.pointSet) := by
    exact_mod_cast hxx'
  have hyyZ : (2 * GridPoint.I y.pointSet y.pointSet : ℤ) =
      2 * ((GridPoint.JNum {(R.left, R.top)} {(R.right, R.bottom)} : ℤ) +
            GridPoint.JNum {(R.left, R.top)} (x.pointSet ∩ y.pointSet) +
            GridPoint.JNum {(R.right, R.bottom)} (x.pointSet ∩ y.pointSet)) +
        GridPoint.JNum (x.pointSet ∩ y.pointSet) (x.pointSet ∩ y.pointSet) := by
    exact_mod_cast hyy'
  omega

end GridRectangleBetween

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The difference of the integer `O`-Maslov grading at two grid states splits into the change
in the state self-pairing and the change in the `O`-marking `JNum`-pairing. The two states need
not be related: this is the integer algebraic shape of the grading formula, mirroring the
rational identity `maslovO_sub_maslovO_eq`. -/
theorem maslovOℤ_sub_maslovOℤ_eq (x y : GridState n) :
    G.maslovOℤ x - G.maslovOℤ y =
      ((GridPoint.I x.pointSet x.pointSet : ℤ) - GridPoint.I y.pointSet y.pointSet) -
        ((GridPoint.JNum x.pointSet G.OSet : ℤ) - GridPoint.JNum y.pointSet G.OSet) := by
  rw [maslovOℤ_def, maslovOℤ_def]
  ring

/-- The difference of the integer `X`-Maslov grading at two grid states splits into the change
in the state self-pairing and the change in the `X`-marking `JNum`-pairing. -/
theorem maslovXℤ_sub_maslovXℤ_eq (x y : GridState n) :
    G.maslovXℤ x - G.maslovXℤ y =
      ((GridPoint.I x.pointSet x.pointSet : ℤ) - GridPoint.I y.pointSet y.pointSet) -
        ((GridPoint.JNum x.pointSet G.XSet : ℤ) - GridPoint.JNum y.pointSet G.XSet) := by
  rw [maslovXℤ_def, maslovXℤ_def]
  ring

/-- The change in `2A`, the integer numerator of twice the Alexander grading, at two grid
states is the difference of the two marking `JNum`-pairing changes. The state self-pairing term
is common to the two Maslov gradings and the normalization shift depends only on the grid size,
so both cancel, leaving a marking-only identity that needs no relationship between `x` and
`y`. -/
theorem alexanderTwoℤ_sub_alexanderTwoℤ_eq (x y : GridState n) :
    G.alexanderTwoℤ x - G.alexanderTwoℤ y =
      ((GridPoint.JNum x.pointSet G.XSet : ℤ) - GridPoint.JNum y.pointSet G.XSet) -
        ((GridPoint.JNum x.pointSet G.OSet : ℤ) - GridPoint.JNum y.pointSet G.OSet) := by
  rw [alexanderTwoℤ_def, alexanderTwoℤ_def, maslovOℤ_def, maslovOℤ_def, maslovXℤ_def, maslovXℤ_def]
  ring

variable {x y : GridState n}

/-- The integer `O`-Maslov grading change across a rectangle move, localized to the four
corners: both the state self-pairing change and the `O`-marking `JNum`-pairing change are
written as differences of corner counts. This is the integer form of
`maslovO_change_rectangle`. -/
theorem maslovOℤ_change_rectangle (R : GridRectangleBetween x y) :
    G.maslovOℤ x - G.maslovOℤ y =
      (((GridPoint.JNum {(R.left, R.bottom)} {(R.right, R.top)} : ℤ) +
              GridPoint.JNum {(R.left, R.bottom)} (x.pointSet ∩ y.pointSet) +
              GridPoint.JNum {(R.right, R.top)} (x.pointSet ∩ y.pointSet)) -
            ((GridPoint.JNum {(R.left, R.top)} {(R.right, R.bottom)} : ℤ) +
              GridPoint.JNum {(R.left, R.top)} (x.pointSet ∩ y.pointSet) +
              GridPoint.JNum {(R.right, R.bottom)} (x.pointSet ∩ y.pointSet))) -
        (((GridPoint.JNum {(R.left, R.bottom)} G.OSet : ℤ) +
              GridPoint.JNum {(R.right, R.top)} G.OSet) -
          ((GridPoint.JNum {(R.left, R.top)} G.OSet : ℤ) +
              GridPoint.JNum {(R.right, R.bottom)} G.OSet)) := by
  rw [G.maslovOℤ_sub_maslovOℤ_eq, R.I_self_sub_I_self_eq, R.JNum_pointSet_sub_eq]

/-- The integer `X`-Maslov grading change across a rectangle move, localized to the four
corners. -/
theorem maslovXℤ_change_rectangle (R : GridRectangleBetween x y) :
    G.maslovXℤ x - G.maslovXℤ y =
      (((GridPoint.JNum {(R.left, R.bottom)} {(R.right, R.top)} : ℤ) +
              GridPoint.JNum {(R.left, R.bottom)} (x.pointSet ∩ y.pointSet) +
              GridPoint.JNum {(R.right, R.top)} (x.pointSet ∩ y.pointSet)) -
            ((GridPoint.JNum {(R.left, R.top)} {(R.right, R.bottom)} : ℤ) +
              GridPoint.JNum {(R.left, R.top)} (x.pointSet ∩ y.pointSet) +
              GridPoint.JNum {(R.right, R.bottom)} (x.pointSet ∩ y.pointSet))) -
        (((GridPoint.JNum {(R.left, R.bottom)} G.XSet : ℤ) +
              GridPoint.JNum {(R.right, R.top)} G.XSet) -
          ((GridPoint.JNum {(R.left, R.top)} G.XSet : ℤ) +
              GridPoint.JNum {(R.right, R.bottom)} G.XSet)) := by
  rw [G.maslovXℤ_sub_maslovXℤ_eq, R.I_self_sub_I_self_eq, R.JNum_pointSet_sub_eq]

/-- The change in `2A` across a rectangle move, localized to the four corners: it is the four
`X`-corner `JNum`-counts minus the four `O`-corner `JNum`-counts, in each case the two source
corners against the two target corners. The state self-pairing cancels
(`alexanderTwoℤ_sub_alexanderTwoℤ_eq`) and the shared squares cancel
(`JNum_pointSet_sub_eq`). -/
theorem alexanderTwoℤ_change_rectangle (R : GridRectangleBetween x y) :
    G.alexanderTwoℤ x - G.alexanderTwoℤ y =
      (((GridPoint.JNum {(R.left, R.bottom)} G.XSet : ℤ) +
              GridPoint.JNum {(R.right, R.top)} G.XSet) -
          ((GridPoint.JNum {(R.left, R.top)} G.XSet : ℤ) +
              GridPoint.JNum {(R.right, R.bottom)} G.XSet)) -
        (((GridPoint.JNum {(R.left, R.bottom)} G.OSet : ℤ) +
              GridPoint.JNum {(R.right, R.top)} G.OSet) -
          ((GridPoint.JNum {(R.left, R.top)} G.OSet : ℤ) +
              GridPoint.JNum {(R.right, R.bottom)} G.OSet)) := by
  rw [G.alexanderTwoℤ_sub_alexanderTwoℤ_eq, R.JNum_pointSet_sub_eq (P := G.XSet),
    R.JNum_pointSet_sub_eq (P := G.OSet)]

end GridDiagram

end TauCeti
