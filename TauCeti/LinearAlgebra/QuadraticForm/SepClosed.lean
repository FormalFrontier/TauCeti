/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Quadratic forms over a separably closed field

This file proves that a finite-dimensional nondegenerate quadratic form over a separably closed
field of characteristic different from two is equivalent to a sum of squares.

## Main result

* `QuadraticForm.equivalent_weightedSumSquares_of_isSepClosed`: a nondegenerate quadratic form is
  equivalent to the standard sum of squares.

## References

* [Tau Ceti Roadmap](https://github.com/TauCetiProject/TauCetiRoadmap), Representation Theory /
  Spin Representations, Layer 4, "The spin module".
* Mathlib's `QuadraticForm.isometryEquivSumSquaresUnits` and
  `QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed` supply the normalization argument
  adapted here from algebraically closed to separably closed fields.
-/

public section

open QuadraticMap

namespace QuadraticForm

variable {ι : Type*} [Fintype ι] {K : Type*} [Field K] [IsSepClosed K]

private noncomputable def isometryEquivSumSquaresUnits [NeZero (2 : K)] (w : ι → Kˣ) :
    IsometryEquiv (weightedSumSquares K fun i ↦ (w i : K))
      (weightedSumSquares K (1 : ι → K)) := by
  classical
  refine isometryEquivWeightedSumSquaresWeightedSumSquares
    (fun i ↦ Units.mk0 (IsSepClosed.exists_eq_mul_self (w i : K)).choose ?_) ?_
  · rw [← mul_self_eq_zero.ne, ← (IsSepClosed.exists_eq_mul_self (w i : K)).choose_spec]
    exact (w i).ne_zero
  · intro i
    simp [pow_two, ← (IsSepClosed.exists_eq_mul_self (w i : K)).choose_spec]

/-- A finite-dimensional nondegenerate quadratic form over a separably closed field of
characteristic different from two is equivalent to the standard sum of squares. -/
theorem equivalent_weightedSumSquares_of_isSepClosed [Invertible (2 : K)] {M : Type*}
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (Q : QuadraticForm K M) (hQ : (associated Q).SeparatingLeft) :
    Equivalent Q (weightedSumSquares K (1 : Fin (Module.finrank K M) → K)) := by
  classical
  let ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hQ
  exact ⟨e.trans (isometryEquivSumSquaresUnits w)⟩

end QuadraticForm
