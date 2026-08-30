/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Rectangle.Annulus
public import TauCeti.KnotTheory.Grid.Unblocked

/-!
# The annular terms of the unblocked grid differential square vanish

The square of the unblocked grid differential `∂⁻` of `Unblocked.lean` is a sum over pairs of
composable rectangles. The juxtaposition argument for `∂⁻ ∘ ∂⁻ = 0` splits those pairs according
to how the two rectangles meet, and the *annular* case is the one in which the second rectangle
returns to the source of the first. This file closes that case.

The mechanism is that a returning pair covers a full toroidal annulus,
`GridRectangleBetween.coveredSquares_union_coveredSquares`, and a grid diagram has an
`X`-marking in every column and in every row. So a returning pair always covers an `X`-marking,
and the unblocked differential counts only rectangles that cover none: between two grid states,
at most one of the two directions contributes at all
(`GridDiagram.unblockedRectangles_eq_empty_or_unblockedRectangles_eq_empty`). The unblocked
differential therefore has no two-step return, and the diagonal entries of the matrix of
`∂⁻ ∘ ∂⁻` are zero.

The argument never inspects the `O`-markings, so it is insensitive to the weights `V^{O(r)}` and
runs over an arbitrary commutative coefficient ring, characteristic two included. This is the
first case of the square-zero argument to be settled for the unblocked complex; the disjoint and
overlapping cases, where two distinct decompositions must be paired against each other, remain.
On a grid of size at most two the annular case already suffices, because there is no room for the
other two: that consequence is
`GridDiagram.unblockedDifferential_comp_self_eq_zero_of_le_two` in `SmallGrid/Differential.lean`.

## Main results

* `TauCeti.GridDiagram.unblockedRectangles_eq_empty_or_unblockedRectangles_eq_empty`: between two
  grid states, one of the two directions carries no rectangle the unblocked differential counts.
* `TauCeti.GridDiagram.unblockedCoefficient_mul_unblockedCoefficient_eq_zero`: the product of the
  two matrix coefficients of `∂⁻` between a pair of grid states vanishes.
* `TauCeti.GridDiagram.unblockedDifferential_sq_single_apply`: the matrix of `∂⁻ ∘ ∂⁻`, as a sum
  over intermediate grid states of products of matrix coefficients.
* `TauCeti.GridDiagram.unblockedDifferential_sq_single_apply_self`: its diagonal entries vanish.

## References

This supplies the annular case for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane
G.3, "The complexes and `∂² = 0`", specifically the "annular pairs of empty rectangles" clause of
its juxtaposition case analysis. The argument follows Ozsváth--Stipsicz--Szabó, *Grid Homology
for Knots and Links*, Chapter 4.6.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommSemiring R]

/-- Between two grid states, the unblocked differential counts rectangles in at most one of the
two directions: a rectangle from `x` to `y` and a rectangle from `y` back to `x` would cover a
full toroidal annulus between them, and every annulus carries an `X`-marking. -/
theorem unblockedRectangles_eq_empty_or_unblockedRectangles_eq_empty (x y : GridState n) :
    G.unblockedRectangles x y = ∅ ∨ G.unblockedRectangles y x = ∅ := by
  by_cases hxy : G.unblockedRectangles x y = ∅
  · exact Or.inl hxy
  obtain ⟨r, hr⟩ := Finset.nonempty_iff_ne_empty.mpr hxy
  refine Or.inr (Finset.eq_empty_iff_forall_notMem.mpr fun s hs => ?_)
  rcases r.not_disjoint_coveredSquares_or_not_disjoint_coveredSquares s G.X with hc | hc
  · exact hc (G.disjoint_XSet_of_mem_unblockedRectangles hr)
  · exact hc (G.disjoint_XSet_of_mem_unblockedRectangles hs)

/-- A nonzero matrix coefficient of the unblocked differential forces the opposite coefficient to
vanish. -/
theorem unblockedCoefficient_eq_zero_of_ne_zero {x y : GridState n}
    (h : G.unblockedCoefficient R x y ≠ 0) : G.unblockedCoefficient R y x = 0 := by
  rcases G.unblockedRectangles_eq_empty_or_unblockedRectangles_eq_empty x y with he | he
  · exact absurd (by rw [G.unblockedCoefficient_def R x y, he, Finset.sum_empty]) h
  · rw [G.unblockedCoefficient_def R y x, he, Finset.sum_empty]

/-- The two matrix coefficients of the unblocked differential between a pair of grid states have
zero product: the unblocked differential admits no two-step return. -/
@[simp]
theorem unblockedCoefficient_mul_unblockedCoefficient_eq_zero (x y : GridState n) :
    G.unblockedCoefficient R x y * G.unblockedCoefficient R y x = 0 := by
  by_cases h : G.unblockedCoefficient R x y = 0
  · rw [h, zero_mul]
  · rw [G.unblockedCoefficient_eq_zero_of_ne_zero R h, mul_zero]

/-- The matrix of the square of the unblocked differential: its `(x, z)` entry is the sum over
intermediate grid states of the products of the two matrix coefficients. -/
theorem unblockedDifferential_sq_single_apply (x z : GridState n) :
    G.unblockedDifferential R (G.unblockedDifferential R (Finsupp.single x 1)) z =
      ∑ y : GridState n, G.unblockedCoefficient R x y * G.unblockedCoefficient R y z := by
  rw [unblockedDifferential_single, unblockedDifferential_apply_apply,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _]
  exact Finset.sum_congr rfl fun y _ => by
    rw [unblockedDifferentialOnGenerator_apply]

/-- The diagonal entries of the matrix of `∂⁻ ∘ ∂⁻` vanish: every annular term of the square of
the unblocked grid differential is individually zero, for every coefficient ring. -/
@[simp↓]
theorem unblockedDifferential_sq_single_apply_self (x : GridState n) :
    G.unblockedDifferential R (G.unblockedDifferential R (Finsupp.single x 1)) x = 0 := by
  rw [G.unblockedDifferential_sq_single_apply R x x]
  exact Finset.sum_eq_zero fun y _ =>
    G.unblockedCoefficient_mul_unblockedCoefficient_eq_zero R x y

/-- The source generator does not survive two applications of the unblocked differential. -/
@[simp↓]
theorem notMem_support_unblockedDifferential_sq_single (x : GridState n) :
    x ∉ (G.unblockedDifferential R (G.unblockedDifferential R (Finsupp.single x 1))).support := by
  rw [Finsupp.notMem_support_iff]
  exact G.unblockedDifferential_sq_single_apply_self R x

/-- The support of the unblocked differential contains no two-step return: if `y` occurs in
`∂⁻ x`, then `x` does not occur in `∂⁻ y`. -/
theorem notMem_support_unblockedDifferentialOnGenerator_of_mem_support {x y : GridState n}
    (h : y ∈ (G.unblockedDifferentialOnGenerator R x).support) :
    x ∉ (G.unblockedDifferentialOnGenerator R y).support := by
  rw [Finsupp.mem_support_iff, unblockedDifferentialOnGenerator_apply] at h
  rw [Finsupp.notMem_support_iff, unblockedDifferentialOnGenerator_apply]
  exact G.unblockedCoefficient_eq_zero_of_ne_zero R h

end GridDiagram

end TauCeti
