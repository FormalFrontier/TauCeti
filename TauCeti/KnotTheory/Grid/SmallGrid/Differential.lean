/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Complex
public import TauCeti.KnotTheory.Grid.Differential.Square.Annulus
import TauCeti.KnotTheory.Grid.StateCardinality

/-!
# The grid differentials on grids of size at most two

This file records the small-grid computations for the grid differentials.

For the fully blocked differential the whole differential vanishes. An oriented rectangle needs
two distinct side columns, so grids of size at most one have no rectangles at all. On a `2 × 2`
grid, an oriented rectangle covers a single square, and the four markings of the diagram occupy
all four squares — two `O` markings and two `X` markings on the two diagonals — so every oriented
rectangle contains a marking and no rectangle is fully blocked. In either case every fully
blocked count vanishes, hence so does the whole differential.

The cases `n = 0` and `n = 1` already follow from the column-swap support bound. The new content
here is the size-two computation, which is the first sanity check for the marking-avoidance
condition defining the fully blocked grid complex: on the `2 × 2` unknot grid every square is
marked, so the fully blocked theory sees no rectangles at all.

The unblocked differential `∂⁻` need not vanish, but it does square to zero, and on these grids
the annular case of `Differential/Square/Annulus.lean` settles that on its own. At most two grid
states are available, which leaves no room for the disjoint and overlapping juxtaposition cases:
if the source and the target of a two-step term are distinct they exhaust the grid states, so
every intermediate state is one of them and its term carries a diagonal matrix coefficient, while
if the source and the target coincide the term is annular.

## Main results

* `TauCeti.GridDiagram.fullyBlockedRectangles_eq_empty_of_le_two`: no rectangle is fully
  blocked in grid size at most two.
* `TauCeti.GridDiagram.fullyBlockedRectangleCount_eq_zero_of_le_two`: every fully blocked
  rectangle coefficient vanishes in grid size at most two.
* `TauCeti.GridDiagram.fullyBlockedDifferential_eq_zero_of_le_two`: the fully blocked
  differential is the zero linear map in grid size at most two.
* `TauCeti.GridDiagram.fullyBlockedDifferential_eq_zero_of_two`: the explicit `2 × 2` form.
* `TauCeti.GridDiagram.unblockedDifferential_comp_self_eq_zero_of_le_two`: in grid size at most
  two the unblocked differential squares to zero.

## References

This supplies a prerequisite for
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, "The complexes and `∂² = 0`",
and for the standing convention that the grid complexes compute on explicit small grids. The
rectangle-count convention follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Chapter 3; the marking-avoidance condition defining the fully blocked complex is in
Chapter 4, Section 4.4.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- In grid size at most two, no oriented rectangle is fully blocked. A rectangle needs two
distinct side columns and two distinct side rows, so it covers exactly the one square at its
initial corner; that square holds a point of the source state, and in a column of only two
squares the two distinct markings of that column leave no unmarked square for it. -/
theorem fullyBlockedRectangles_eq_empty_of_le_two (hn : n ≤ 2) (x y : GridState n) :
    G.fullyBlockedRectangles x y = ∅ := by
  ext R
  simp only [mem_fullyBlockedRectangles, Finset.notMem_empty, iff_false, not_and]
  intro _ havoid
  have hpair : x R.left = G.O R.left ∨ x R.left = G.X R.left := by
    by_contra hcon
    push Not at hcon
    have hOX : G.O R.left ≠ G.X R.left := G.disjoint R.left
    have h1 := (G.O R.left).isLt
    have h2 := (G.X R.left).isLt
    have h3 := (x R.left).isLt
    rw [← Fin.val_ne_iff] at hOX
    obtain ⟨hO, hX⟩ := hcon
    rw [← Fin.val_ne_iff] at hO hX
    omega
  have hsq : (R.left, x R.left) ∈ R.toGridRectangle.squares := by
    simpa only [GridRectangleBetween.bottom] using R.left_bottom_mem_squares
  rcases hpair with h | h
  · exact Finset.disjoint_left.mp (R.disjoint_squares_OSet_of_avoidsMarkings havoid) hsq
      ((G.mk_mem_OSet R.left (x R.left)).mpr h.symm)
  · exact Finset.disjoint_left.mp (R.disjoint_squares_XSet_of_avoidsMarkings havoid) hsq
      ((G.mk_mem_XSet R.left (x R.left)).mpr h.symm)

/-- Every fully blocked rectangle coefficient vanishes in grid size at most two: no rectangle is
fully blocked. -/
theorem fullyBlockedRectangleCount_eq_zero_of_le_two (hn : n ≤ 2) (x y : GridState n) :
    G.fullyBlockedRectangleCount x y = 0 := by
  rw [fullyBlockedRectangleCount_def, G.fullyBlockedRectangles_eq_empty_of_le_two hn]
  simp

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

/-- The fully blocked differential is zero on every `2 × 2` grid. This is the first sanity
check for the marking-avoidance condition: every square of a `2 × 2` grid is marked. -/
@[simp]
theorem fullyBlockedDifferential_eq_zero_of_two (G : GridDiagram 2) :
    G.fullyBlockedDifferential =
      (0 : GridChain (ZMod 2) 2 →ₗ[ZMod 2] GridChain (ZMod 2) 2) :=
  G.fullyBlockedDifferential_eq_zero_of_le_two le_rfl

section Unblocked

variable (R : Type*) [CommSemiring R]

/-- On a grid of size at most two the unblocked differential squares to zero.

At most two grid states are available. If the source and the target of a two-step term are
distinct they exhaust those states, so every intermediate state coincides with the source or with
the target and its term is killed by the vanishing of the diagonal matrix coefficient. If instead
the source and the target coincide, the term returns to its source and the annular argument
applies. This is the first instance of the roadmap's square-zero milestone for `GC⁻`; the general
case still needs the disjoint and overlapping juxtaposition cases. -/
theorem unblockedDifferential_comp_self_eq_zero_of_le_two (hn : n ≤ 2) :
    G.unblockedDifferential R ∘ₗ G.unblockedDifferential R =
      (0 : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n) := by
  have hcard : Fintype.card (GridState n) ≤ 2 := by
    rw [GridState.card]
    simpa [Nat.factorial] using Nat.factorial_le hn
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_comp,
    LinearMap.zero_apply]
  refine Finsupp.ext fun z => ?_
  rw [G.unblockedDifferential_sq_single_apply R x z, Finsupp.coe_zero, Pi.zero_apply]
  refine Finset.sum_eq_zero fun y _ => ?_
  by_cases hyx : y = x
  · rw [hyx, unblockedCoefficient_self, zero_mul]
  by_cases hyz : y = z
  · rw [hyz, unblockedCoefficient_self, mul_zero]
  by_cases hzx : z = x
  · rw [hzx]
    exact G.unblockedCoefficient_mul_unblockedCoefficient_eq_zero R x y
  have h3 : ({x, y, z} : Finset (GridState n)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hyx, Ne.symm hzx]),
      Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
  have hle : 3 ≤ Fintype.card (GridState n) := by
    simpa [Finset.card_univ, h3] using Finset.card_le_univ ({x, y, z} : Finset (GridState n))
  omega

end Unblocked

end GridDiagram

end TauCeti
