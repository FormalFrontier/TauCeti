/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Quadratic forms over separably closed fields

A finite-dimensional quadratic form over a separably closed field of characteristic different
from two whose associated bilinear form is left-separating is equivalent to the standard
sum-of-squares form. Consequently, any two such forms on the same vector space are equivalent.

## Main results

* `TauCeti.QuadraticForm.equivalent_weightedSumSquares_of_isSepClosed`: normalizes a form to the
  standard sum-of-squares form.
* `TauCeti.QuadraticForm.equivalent_of_isSepClosed`: identifies two such forms.

## References

* `Mathlib.LinearAlgebra.QuadraticForm.AlgClosed`, whose square-root normalization argument is
  adapted below from algebraically closed to separably closed fields.
-/

public section

open QuadraticMap

namespace TauCeti.QuadraticForm

noncomputable section

variable {K V : Type*} [Field K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

private def isometryEquivSumSquaresUnits [IsSepClosed K] {I : Type*} [Fintype I]
    (w : I → Kˣ) :
    (QuadraticMap.weightedSumSquares K fun i ↦ (w i : K)).IsometryEquiv
      (QuadraticMap.weightedSumSquares K (1 : I → K)) := by
  classical
  refine QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares
    (fun i ↦ Units.mk0 (IsSepClosed.exists_eq_mul_self (w i : K)).choose ?_) ?_
  · rw [← mul_self_eq_zero.ne, ← (IsSepClosed.exists_eq_mul_self (w i : K)).choose_spec]
    exact (w i).ne_zero
  · intro i
    simp [pow_two, ← (IsSepClosed.exists_eq_mul_self (w i : K)).choose_spec]

/-- A quadratic form over a separably closed field of characteristic different from two whose
associated bilinear form is left-separating is equivalent to the standard sum-of-squares form. -/
theorem equivalent_weightedSumSquares_of_isSepClosed [IsSepClosed K]
    (Q : QuadraticForm K V) (hQ : (QuadraticMap.associated Q).SeparatingLeft) :
    Q.Equivalent
      (QuadraticMap.weightedSumSquares K (1 : Fin (Module.finrank K V) → K)) := by
  classical
  let ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hQ
  exact ⟨e.trans (isometryEquivSumSquaresUnits w)⟩

/-- Two quadratic forms with left-separating associated bilinear forms on the same
finite-dimensional vector space over a separably closed field of characteristic different from
two are equivalent. -/
theorem equivalent_of_isSepClosed [IsSepClosed K]
    (Q₁ Q₂ : QuadraticForm K V) (hQ₁ : (QuadraticMap.associated Q₁).SeparatingLeft)
    (hQ₂ : (QuadraticMap.associated Q₂).SeparatingLeft) : Q₁.Equivalent Q₂ :=
  (equivalent_weightedSumSquares_of_isSepClosed Q₁ hQ₁).trans
    (equivalent_weightedSumSquares_of_isSepClosed Q₂ hQ₂).symm

end

end TauCeti.QuadraticForm
