/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.KnotTheory.Grid.Complex
import TauCeti.KnotTheory.Grid.Rectangle.Count

/-!
# The fully blocked grid differential on grids of size at most two

This file records the first small-grid computation for the fully blocked grid differential.
In an `n × n` grid with `n ≤ 2`, every open cyclic interval in `Fin n` is empty. Consequently
every toroidal rectangle has empty interior, so every oriented rectangle is empty and avoids all
markings. Between two distinct grid states the two oriented rectangles therefore both contribute
to the fully blocked count, and their total is zero in `ZMod 2`; between a state and itself there
are no rectangles. Thus the whole fully blocked differential vanishes.

The cases `n = 0` and `n = 1` already follow from the column-swap support bound. The new content
here is the size-two cancellation, which is the first nontrivial sanity check for the rectangle
count defining the fully blocked grid complex.

## Main results

* `TauCeti.Grid.cIoo_eq_empty_of_le_two`: open cyclic intervals in grids of size at most two
  are empty.
* `TauCeti.GridDiagram.fullyBlockedRectangleCount_eq_zero_of_le_two`: every fully blocked
  rectangle coefficient vanishes in grid size at most two.
* `TauCeti.GridDiagram.fullyBlockedDifferential_eq_zero_of_le_two`: the fully blocked
  differential is the zero linear map in grid size at most two.
* `TauCeti.GridDiagram.fullyBlockedDifferential_eq_zero_of_two`: the explicit `2 × 2` form.

## References

This supplies a prerequisite for
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, "The complexes and `∂² = 0`",
and for the standing convention that the grid complexes compute on explicit small grids. The
rectangle-count convention follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Chapter 3.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- In grid size at most two, the fully blocked rectangles are exactly all oriented rectangles:
all rectangle interiors are empty, so emptiness and marking avoidance impose no extra condition. -/
theorem fullyBlockedRectangles_eq_all_of_le_two (hn : n ≤ 2) (x y : GridState n) :
    G.fullyBlockedRectangles x y = GridRectangleBetween.all x y := by
  ext R
  rw [mem_fullyBlockedRectangles]
  constructor
  · intro _
    exact GridRectangleBetween.mem_all R
  · intro _
    exact ⟨GridRectangleBetween.isEmpty_of_le_two hn R,
      R.toGridRectangle.avoidsMarkings_of_le_two hn G⟩

/-- Every fully blocked rectangle coefficient vanishes in grid size at most two. If there are no
rectangles the count is zero; otherwise there are exactly two oriented rectangles, which cancel
over `ZMod 2`. -/
theorem fullyBlockedRectangleCount_eq_zero_of_le_two (hn : n ≤ 2) (x y : GridState n) :
    G.fullyBlockedRectangleCount x y = 0 := by
  rw [fullyBlockedRectangleCount_def, G.fullyBlockedRectangles_eq_all_of_le_two hn]
  rcases (GridRectangleBetween.all x y).eq_empty_or_nonempty with h | h
  · simp [h]
  · rw [GridRectangleBetween.card_all_eq_two_of_nonempty h]
    exact ZMod.natCast_self 2

/-- Every fully blocked rectangle coefficient vanishes on every `2 × 2` grid. -/
@[simp]
theorem fullyBlockedRectangleCount_eq_zero_of_two (G : GridDiagram 2) (x y : GridState 2) :
    G.fullyBlockedRectangleCount x y = 0 :=
  G.fullyBlockedRectangleCount_eq_zero_of_le_two le_rfl x y

/-- The fully blocked differential of one generator vanishes in grid size at most two. -/
theorem fullyBlockedDifferentialOnGenerator_eq_zero_of_le_two (hn : n ≤ 2) (x : GridState n) :
    G.fullyBlockedDifferentialOnGenerator x = 0 := by
  ext y
  simp [fullyBlockedRectangleCount_eq_zero_of_le_two G hn x y]

/-- The fully blocked differential of one generator vanishes on every `2 × 2` grid. -/
@[simp]
theorem fullyBlockedDifferentialOnGenerator_eq_zero_of_two (G : GridDiagram 2) (x : GridState 2) :
    G.fullyBlockedDifferentialOnGenerator x = 0 :=
  G.fullyBlockedDifferentialOnGenerator_eq_zero_of_le_two le_rfl x

/-- The fully blocked differential is zero on every chain in grid size at most two. -/
theorem fullyBlockedDifferential_eq_zero_of_le_two (hn : n ≤ 2) :
    G.fullyBlockedDifferential = (0 : GridChain (ZMod 2) n →ₗ[ZMod 2] GridChain (ZMod 2) n) := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring ?_
  simp [fullyBlockedDifferentialOnGenerator_eq_zero_of_le_two G hn x]

/-- The fully blocked differential is zero on every `2 × 2` grid. This is the first
nontrivial cancellation sanity check for the rectangle-count definition. -/
@[simp]
theorem fullyBlockedDifferential_eq_zero_of_two (G : GridDiagram 2) :
    G.fullyBlockedDifferential =
      (0 : GridChain (ZMod 2) 2 →ₗ[ZMod 2] GridChain (ZMod 2) 2) :=
  G.fullyBlockedDifferential_eq_zero_of_le_two le_rfl

end GridDiagram

end TauCeti
