/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.KnotTheory.Grid.Rectangle.Basic

/-!
# A grid rectangle move is a column transposition

An oriented rectangle `R : GridRectangleBetween x y` records the two side columns at which the
target state `y` differs from the source state `x`: at the initial side column `y` reads the
row `x` uses at the terminal side, and vice versa, while the two states agree away from the two
side columns. That is exactly the effect of swapping the two side columns of `x`, so the target
state is the column transposition `x.swapColumns R.left R.right`.

This file makes that identification precise and draws the point-set consequences: the two
states share all but two of their occupied squares, and each occupied square they do not share
is one of the four corners of the rectangle. The shared squares are exactly the intersection of
the two point sets, which has `n - 2` elements. These are the bookkeeping facts a Maslov or
Alexander grading-change computation across a rectangle rests on, and they let later
`∂² = 0`-style arguments reason about `x` and `y` through a single transposition.

## Main results

* `TauCeti.GridRectangleBetween.target_eq_swapColumns`: the target state of a rectangle is the
  source state with the two side columns swapped.
* `TauCeti.GridRectangleBetween.nonempty_all_iff`: oriented rectangles between `x` and `y` exist
  exactly when `y` is a column transposition of `x`.
* `TauCeti.GridRectangleBetween.source_eq_swapColumns`: the symmetric statement recovering the
  source from the target.
* `TauCeti.GridRectangleBetween.mem_pointSet_inter_iff`: a square is shared by the two states
  exactly when it belongs to the source and avoids the two side columns -- the rectangle
  specialization of `GridState.mem_pointSet_inter_swapColumns_iff` from `Diagram.lean`.
* `TauCeti.GridRectangleBetween.source_pointSet_eq`,
  `TauCeti.GridRectangleBetween.target_pointSet_eq`: each state's point set is the shared part
  together with its own two corners.
* `TauCeti.GridRectangleBetween.card_pointSet_inter`: the two states share exactly `n - 2`
  squares.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`,
Lane G.2, "grading-change formulas across a rectangle", and Lane G.3, "The complexes and
`∂² = 0`". The column-transposition picture of a rectangle move follows Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Chapter 4.
-/

public section

namespace TauCeti

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n} (R : GridRectangleBetween x y)

/-- Pointwise form of the column-transposition identity: at each column the target state reads
the row the source state reads at the swapped column. -/
theorem target_apply (c : Fin n) : y c = x (Equiv.swap R.left R.right c) := by
  rcases eq_or_ne c R.left with h | hl
  · subst h
    rw [Equiv.swap_apply_left]
    exact R.map_left
  · rcases eq_or_ne c R.right with h | hr
    · subst h
      rw [Equiv.swap_apply_right]
      exact R.map_right
    · rw [Equiv.swap_apply_of_ne_of_ne hl hr]
      exact R.map_of_ne c hl hr

/-- The target state of an oriented rectangle is the source state with its two side columns
swapped. The rectangle's defining equations -- the two side columns exchange their rows and the
other columns are unchanged -- are precisely the action of the column transposition. -/
theorem target_eq_swapColumns : y = x.swapColumns R.left R.right := by
  refine GridState.ext fun c => ?_
  rw [GridState.swapColumns_apply]
  exact target_apply R c

/-- Oriented rectangles between `x` and `y` exist exactly when `y` is a column transposition of
`x`. A rectangle realizes its side columns as a transposition taking `x` to `y`, and conversely a
column transposition exhibits an oriented rectangle on those two columns. -/
theorem nonempty_all_iff : (all x y).Nonempty ↔ ∃ a b : Fin n, a ≠ b ∧ y = x.swapColumns a b := by
  constructor
  · rintro ⟨R, -⟩
    exact ⟨R.left, R.right, R.left_ne_right, R.target_eq_swapColumns⟩
  · rintro ⟨a, b, hab, hy⟩
    refine ⟨⟨a, b, hab, ?_, ?_, ?_⟩, mem_all _⟩
    · rw [hy, GridState.swapColumns_apply, Equiv.swap_apply_left]
    · rw [hy, GridState.swapColumns_apply, Equiv.swap_apply_right]
    · intro c hl hr
      rw [hy, GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hl hr]

/-- The source state of an oriented rectangle is the target state with its two side columns
swapped: swapping the same pair of columns twice is the identity. -/
theorem source_eq_swapColumns : x = y.swapColumns R.left R.right := by
  refine GridState.ext fun c => ?_
  rw [GridState.swapColumns_apply]
  have h := target_apply R (Equiv.swap R.left R.right c)
  rw [Equiv.swap_apply_self] at h
  exact h.symm

/-- The underlying permutation of the target state is the source permutation precomposed with
the transposition of the two side columns. -/
theorem target_toPerm_eq :
    y.toPerm = (Equiv.swap R.left R.right).trans x.toPerm := by
  refine Equiv.ext fun c => ?_
  rw [Equiv.trans_apply]
  exact target_apply R c

/-- A square lies in the target state exactly when its column-transposed square lies in the
source state. -/
theorem mem_target_pointSet_iff (p : Fin n × Fin n) :
    p ∈ y.pointSet ↔ (Equiv.swap R.left R.right p.1, p.2) ∈ x.pointSet := by
  rw [GridState.mem_pointSet, GridState.mk_mem_pointSet, target_apply R p.1]

/-- The two side columns carry the four corners of a rectangle, so a square that the two states
share must avoid both side columns. Conversely, away from the side columns the two states agree,
so every source square off the side columns is shared. -/
theorem mem_pointSet_inter_iff (p : Fin n × Fin n) :
    p ∈ x.pointSet ∩ y.pointSet ↔
      p ∈ x.pointSet ∧ p.1 ≠ R.left ∧ p.1 ≠ R.right := by
  simpa [target_eq_swapColumns R] using
    GridState.mem_pointSet_inter_swapColumns_iff x R.left_ne_right p

/-- The lower-left corner is not shared with the target state: it sits on a side column. -/
theorem left_bottom_notMem_inter : (R.left, R.bottom) ∉ x.pointSet ∩ y.pointSet := by
  rw [mem_pointSet_inter_iff R]
  rintro ⟨_, hleft, _⟩
  exact hleft rfl

/-- The upper-right corner is not shared with the target state: it sits on a side column. -/
theorem right_top_notMem_inter : (R.right, R.top) ∉ x.pointSet ∩ y.pointSet := by
  rw [mem_pointSet_inter_iff R]
  rintro ⟨_, _, hright⟩
  exact hright rfl

/-- The upper-left target corner is not shared with the source state: it sits on a side column. -/
theorem left_top_notMem_inter : (R.left, R.top) ∉ x.pointSet ∩ y.pointSet := by
  rw [mem_pointSet_inter_iff R]
  rintro ⟨_, hleft, _⟩
  exact hleft rfl

/-- The lower-right target corner is not shared with the source state: it sits on a side column. -/
theorem right_bottom_notMem_inter : (R.right, R.bottom) ∉ x.pointSet ∩ y.pointSet := by
  rw [mem_pointSet_inter_iff R]
  rintro ⟨_, _, hright⟩
  exact hright rfl

/-- The source state's point set is its shared intersection with the target point set together
with the two source corners `(R.left, R.bottom)` and `(R.right, R.top)`. -/
theorem source_pointSet_eq :
    x.pointSet =
      insert (R.left, R.bottom) (insert (R.right, R.top) (x.pointSet ∩ y.pointSet)) := by
  simpa [target_eq_swapColumns R, bottom, top] using
    GridState.pointSet_eq_insert_insert_inter_swapColumns x R.left_ne_right

/-- The target state's point set is the shared part together with its own two corners. -/
theorem target_pointSet_eq :
    y.pointSet =
      insert (R.left, R.top) (insert (R.right, R.bottom) (x.pointSet ∩ y.pointSet)) := by
  simpa [target_eq_swapColumns R, bottom, top] using
    GridState.swapColumns_pointSet_eq_insert_insert_inter x R.left_ne_right

include R in
/-- The source and target states share exactly `n - 2` squares: all of the source's `n` squares
except its two corners. -/
theorem card_pointSet_inter : (x.pointSet ∩ y.pointSet).card = n - 2 := by
  simpa [target_eq_swapColumns R] using
    GridState.card_pointSet_inter_swapColumns x R.left_ne_right

end GridRectangleBetween

end TauCeti
