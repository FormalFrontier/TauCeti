/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Finset.Card
public import TauCeti.KnotTheory.Grid.Rectangle.Basic

/-!
# A two-rectangle bound for oriented rectangles between grid states

An oriented rectangle `R : GridRectangleBetween x y` is determined by its two side columns
`R.left`, `R.right`: away from those columns the two states agree, and at those columns they
exchange rows (`RectangleSwap.lean`). This file pins down the uniform two-rectangle upper bound
between two fixed grid states, and the exact count once one such rectangle exists.

The key observation is purely about the side columns. A column `c` is a side column of `R`
exactly when the two states differ there: if `c` is neither `R.left` nor `R.right` then
`y c = x c`, and at a side column the states genuinely disagree because the source permutation
is injective. So the *unordered* pair of side columns is forced — it is the set of columns where
`x` and `y` differ — and a rectangle between `x` and `y` is determined up to the *order* of its
two side columns. Reversing the two side columns gives the other oriented rectangle
(`swapSides`), so there are at most two oriented rectangles, and exactly two whenever at least one
exists. The separate `RectangleSwap.lean` file records the transposition/existence criterion.

This is the finiteness backbone of the grid differential: the coefficient of `y` in the fully
blocked differential of `x` counts a sub-collection of these at-most-two rectangles, so the
differential of a generator is supported on the column-transposition neighbours of that
generator.

## Main results

* `TauCeti.GridRectangleBetween.apply_ne_iff`: a column is a side column exactly when the two
  states differ there.
* `TauCeti.GridRectangleBetween.eq_or_eq_swapSides`: any two oriented rectangles between the same
  states are equal or differ by `swapSides`.
* `TauCeti.GridRectangleBetween.all_eq_pair`, `TauCeti.GridRectangleBetween.card_all_le_two`,
  `TauCeti.GridRectangleBetween.card_all_eq_two_of_nonempty`: there are at most two oriented
  rectangles between two states, and exactly two when there is at least one.
* `TauCeti.GridRectangleBetween.card_emptyRectangles_le_two`: there are at most two empty
  rectangles between two states.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3,
"The complexes and `∂² = 0`": the count of rectangles between two states is the finiteness fact
underlying the differential. The statement that exactly two rectangles connect two states
differing by a transposition follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Chapter 4.
-/

public section

namespace TauCeti

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n}

variable (R : GridRectangleBetween x y)

/-- A column is a side column of the rectangle exactly when the two states read different rows
there. Away from the two side columns the states agree, and at a side column the source
permutation is injective on the two distinct side columns, so the read rows differ. -/
theorem apply_ne_iff (c : Fin n) : y c ≠ x c ↔ c = R.left ∨ c = R.right := by
  constructor
  · intro h
    by_contra hc
    rw [not_or] at hc
    exact h (R.map_of_ne c hc.1 hc.2)
  · rintro (rfl | rfl)
    · rw [R.map_left]
      exact fun h => R.left_ne_right (x.toPerm.injective h).symm
    · rw [R.map_right]
      exact fun h => R.left_ne_right (x.toPerm.injective h)

/-- The states differ at the initial side column. -/
theorem left_apply_ne : y R.left ≠ x R.left :=
  (R.apply_ne_iff R.left).mpr (Or.inl rfl)

/-- The states differ at the terminal side column. -/
theorem right_apply_ne : y R.right ≠ x R.right :=
  (R.apply_ne_iff R.right).mpr (Or.inr rfl)

/-- Any oriented rectangle between the same two states is `R` or its side swap `R.swapSides`. Its
two side columns are exactly the two columns where `x` and `y` differ, which are `R.left` and
`R.right`, so its ordered side pair is one of the two orderings of that pair. -/
theorem eq_or_eq_swapSides (S : GridRectangleBetween x y) : S = R ∨ S = R.swapSides := by
  have hSl := (R.apply_ne_iff S.left).mp S.left_apply_ne
  have hSr := (R.apply_ne_iff S.right).mp S.right_apply_ne
  rcases hSl with hSl | hSl
  · refine Or.inl (eq_of_sides hSl ?_)
    rcases hSr with hSr | hSr
    · exact absurd (hSl.trans hSr.symm) S.left_ne_right
    · exact hSr
  · refine Or.inr (eq_of_sides ?_ ?_)
    · rw [swapSides_left]; exact hSl
    · rcases hSr with hSr | hSr
      · rw [swapSides_right]; exact hSr
      · exact absurd (hSl.trans hSr.symm) S.left_ne_right

/-- The oriented rectangles between two states are contained in the pair `{R, R.swapSides}`. -/
theorem all_subset_pair : all x y ⊆ {R, R.swapSides} := by
  intro S _
  rcases R.eq_or_eq_swapSides S with h | h <;> simp [h]

/-- Given one oriented rectangle between two states, the oriented rectangles between them are
exactly the pair `{R, R.swapSides}`. -/
theorem all_eq_pair : all x y = {R, R.swapSides} := by
  refine Finset.Subset.antisymm R.all_subset_pair ?_
  intro S hS
  rcases Finset.mem_insert.mp hS with h | h
  · exact h ▸ mem_all R
  · exact (Finset.mem_singleton.mp h) ▸ mem_all R.swapSides

/-- There are at most two oriented rectangles between two grid states. -/
theorem card_all_le_two (x y : GridState n) : (all x y).card ≤ 2 := by
  rcases (all x y).eq_empty_or_nonempty with h | h
  · rw [h]; simp
  · obtain ⟨R, -⟩ := h
    calc (all x y).card
        ≤ ({R, R.swapSides} : Finset (GridRectangleBetween x y)).card :=
          Finset.card_le_card R.all_subset_pair
      _ = 2 := Finset.card_pair R.swapSides_ne_self.symm

/-- When there is at least one oriented rectangle between two states, there are exactly two: the
chosen one and its side swap. -/
theorem card_all_eq_two_of_nonempty (h : (all x y).Nonempty) : (all x y).card = 2 := by
  obtain ⟨R, -⟩ := h
  rw [R.all_eq_pair, Finset.card_pair R.swapSides_ne_self.symm]

/-- Any finite subcollection of oriented rectangles between two states has cardinality at most
two. -/
theorem card_le_two (s : Finset (GridRectangleBetween x y)) : s.card ≤ 2 :=
  (Finset.card_le_card (by intro R _; exact mem_all R)).trans (card_all_le_two x y)

/-- There are at most two empty oriented rectangles between two grid states. -/
theorem card_emptyRectangles_le_two (x y : GridState n) : (emptyRectangles x y).card ≤ 2 :=
  card_le_two (emptyRectangles x y)

end GridRectangleBetween

end TauCeti
