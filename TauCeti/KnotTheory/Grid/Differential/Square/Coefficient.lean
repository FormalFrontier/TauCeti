/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.Support

/-!
# Coefficients of the square of the fully blocked grid differential

This file expands the coefficient of `∂ (∂ x)` for the fully blocked grid differential as the
finite sum over intermediate grid states. It is the algebraic handoff from the matrix
coefficient definition of the differential to the rectangle-pairing argument: proving `∂² = 0`
on a generator is exactly proving that this sum of length-two rectangle counts vanishes.

The statements here do not assert square-zero. They isolate the coefficient formula and combine
it with the existing two-step support bound, so later files can work coefficient-by-coefficient
inside the finite set of states reached by two column swaps.

## Main results

* `TauCeti.GridDiagram.fullyBlockedDifferential_sq_single_apply`: the coefficient of
  `∂ (∂ x)` at `z` is `∑ y, count(x, y) * count(y, z)`.
* `TauCeti.GridDiagram.sum_fullyBlockedRectangleCount_mul_eq_zero_of_notMem_twoStep`: the same
  finite sum vanishes off the two-step column-swap neighbour set.
* `TauCeti.GridDiagram.fullyBlockedDifferential_sq_single_eq_zero_iff`: square-zero on a
  generator is equivalent to vanishing of all of those coefficient sums.
* `TauCeti.GridDiagram.fullyBlockedDifferential_comp_self_eq_zero_iff`: the global square-zero
  statement is equivalent to the same coefficient vanishing for every pair of states.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane
G.3, "The complexes and `∂² = 0`": the fully blocked differential over `𝔽₂` and the later
juxtaposition case analysis pairing two-step rectangle decompositions. The coefficient
interpretation follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The coefficient of `∂ (∂ x)` at `z` is the finite sum over all intermediate grid states
`y` of the product of the two rectangle-count coefficients. This is the matrix multiplication
formula for the fully blocked differential. -/
@[simp]
theorem fullyBlockedDifferential_sq_single_apply (x z : GridState n) :
    (Finsupp.sum (G.fullyBlockedDifferentialOnGenerator x) fun y a =>
        a * G.fullyBlockedRectangleCount y z) =
      ∑ y : GridState n, G.fullyBlockedRectangleCount x y *
        G.fullyBlockedRectangleCount y z := by
  classical
  rw [Finsupp.sum_fintype]
  · simp
  · simp

/-- If `z` is not reachable from `x` by two column swaps, the length-two rectangle-count sum
from `x` to `z` vanishes. -/
theorem sum_fullyBlockedRectangleCount_mul_eq_zero_of_notMem_twoStep
    (x : GridState n) {z : GridState n} (hz : z ∉ x.twoStepColumnSwapNeighbors) :
    (∑ y : GridState n, G.fullyBlockedRectangleCount x y *
      G.fullyBlockedRectangleCount y z) = 0 := by
  rw [← G.fullyBlockedDifferential_sq_single_apply x z]
  simpa [fullyBlockedDifferential_apply_apply, fullyBlockedDifferential_single] using
    G.fullyBlockedDifferential_sq_single_apply_eq_zero_of_notMem_twoStep x hz

/-- The square of the fully blocked differential vanishes on a generator exactly when every
length-two rectangle-count coefficient sum out of that generator vanishes. -/
theorem fullyBlockedDifferential_sq_single_eq_zero_iff (x : GridState n) :
    G.fullyBlockedDifferential
        (G.fullyBlockedDifferential (Finsupp.single x (1 : ZMod 2))) = 0 ↔
      ∀ z : GridState n,
        (∑ y : GridState n, G.fullyBlockedRectangleCount x y *
          G.fullyBlockedRectangleCount y z) = 0 := by
  constructor
  · intro h z
    rw [← G.fullyBlockedDifferential_sq_single_apply x z]
    rw [← fullyBlockedDifferential_apply_apply, ← fullyBlockedDifferential_single]
    exact congrArg (fun c : GridChain (ZMod 2) n => c z) h
  · intro h
    ext z
    rw [fullyBlockedDifferential_apply_apply, fullyBlockedDifferential_single]
    rw [G.fullyBlockedDifferential_sq_single_apply x z, h z]
    rfl

/-- The global square-zero statement for the fully blocked differential is equivalent to
vanishing of every length-two rectangle-count coefficient sum. -/
theorem fullyBlockedDifferential_comp_self_eq_zero_iff :
    G.fullyBlockedDifferential.comp G.fullyBlockedDifferential = 0 ↔
      ∀ x z : GridState n,
        (∑ y : GridState n, G.fullyBlockedRectangleCount x y *
          G.fullyBlockedRectangleCount y z) = 0 := by
  constructor
  · intro h x z
    have hx :
        G.fullyBlockedDifferential
          (G.fullyBlockedDifferential (Finsupp.single x (1 : ZMod 2))) = 0 := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun f : GridChain (ZMod 2) n →ₗ[ZMod 2] GridChain (ZMod 2) n =>
          f (Finsupp.single x (1 : ZMod 2))) h
    exact (G.fullyBlockedDifferential_sq_single_eq_zero_iff x).mp hx z
  · intro h
    refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring ?_
    simpa [LinearMap.comp_apply] using
      (G.fullyBlockedDifferential_sq_single_eq_zero_iff x).mpr (h x)

end GridDiagram

end TauCeti
