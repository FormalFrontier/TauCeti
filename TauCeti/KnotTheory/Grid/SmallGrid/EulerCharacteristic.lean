/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.EulerCharacteristic
public import TauCeti.KnotTheory.Grid.SmallGrid.Gradings

/-!
# The graded Euler characteristic of the standard two-by-two grid

This file evaluates the state sum and graded Euler characteristic of the standard `2 × 2`
unknot grid using the general Euler-characteristic theory and the explicit small-grid grading
computations.

## Main results

* `TauCeti.GridDiagram.stateSum_twoByTwo`: the state sum of the standard `2 × 2` grid is
  `1 - T⁻²`.
* `TauCeti.OddComponentGridDiagram.gradedEulerChar_twoByTwo`: the graded Euler characteristic of
  the standard `2 × 2` unknot grid is `1 - T⁻²`.

## References

This advances the computation acceptance criteria in
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md` and Lane G.4. The conventions follow
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 3.3 and 4.
-/

public section

open LaurentPolynomial

namespace TauCeti

namespace GridDiagram

/-- The alternating Alexander state sum of the standard `2 × 2` unknot grid is `1 - T⁻²`. -/
theorem stateSum_twoByTwo : twoByTwo.stateSum = 1 - T (-2) := by
  have huniv : (Finset.univ : Finset (GridState 2)) =
      {GridState.twoByTwoId, GridState.twoByTwoSwap} := by
    ext x
    simpa using GridState.eq_twoByTwoId_or_eq_twoByTwoSwap x
  rw [stateSum_def, huniv,
    Finset.sum_insert (by
      simp only [Finset.mem_singleton]
      exact GridState.twoByTwoId_ne_twoByTwoSwap), Finset.sum_singleton]
  simp only [
    maslovOℤ_twoByTwo_twoByTwoId, alexanderTwoℤ_twoByTwo_twoByTwoId,
    maslovOℤ_twoByTwo_twoByTwoSwap, alexanderTwoℤ_twoByTwo_twoByTwoSwap]
  simp [Int.negOnePow_neg, Units.smul_def, sub_eq_add_neg, add_comm]

end GridDiagram

namespace OddComponentGridDiagram

/-- The graded Euler characteristic of the standard `2 × 2` unknot grid is `1 - T⁻²`.

Its two grid states sit in bidegrees `(-1, -1)` and `(0, 0)`, so each of the two occupied
Alexander degrees contributes a single generator, and the two Maslov parities are opposite. In the
Alexander variable `t = T²` the answer reads `1 - t⁻¹`, which is the Euler characteristic of one
copy of the stabilization factor `W = 𝔽 ⊕ 𝔽` in bidegrees `(0, 0)` and `(-1, -1)`: the grid-size
dependence of the fully blocked theory is already visible in its Euler characteristic. -/
theorem gradedEulerChar_twoByTwo (R : Type*) [Semiring R] [StrongRankCondition R] :
    twoByTwo.gradedEulerChar R = 1 - T (-2) := by
  rw [gradedEulerChar_eq_stateSum, GridDiagram.stateSum_twoByTwo]

end OddComponentGridDiagram

end TauCeti
