/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.KnotTheory.Grid.Grading.Parity

/-!
# The grid determinant formula

The alternating Alexander *state sum* of a grid diagram is

`∑_{x ∈ S(G)} (-1)^{M_O(x)} T^{2 A(x)}`,

one term for each of the `n!` grid states. For odd-component diagrams, this corresponds to the
graded Euler characteristic of the grid chain module after identifying `T` with a square root of
the usual Alexander variable; that identification with `Grading/Chain.lean` is not formalized
here. This file evaluates the state sum in closed form: it is a sign times a monomial times the
determinant of an explicit `n × n` matrix of monomials read off the diagram. Two facts combine to
produce the determinant.

*The sign is the sign of a permutation.* A grid state is a permutation of the columns, and
`GridDiagram.negOnePow_maslovOℤ` says that `(-1)^{M_O(x)}` is that permutation's sign, up to a
factor depending only on the diagram. So the alternating sum over states is an alternating sum
over the symmetric group.

*The Alexander grading is a sum of local weights.* Twice the Alexander grading is
`2 A(x) = M_O(x) - M_X(x) - (n - 1)`, in which the two `J`-self-pairings of `x` cancel and only
the numerators of the two pairings of `x` against the markings survive. Each is a count of column
pairs, so fibring it over the column of its grid-state entry writes it as a sum over the
columns of `x` of a quantity `GridState.JNumCenterAt` depending only on the grid point occupied
there. Twice the Alexander grading is therefore `∑_c w(c, x c) + K` for the weight
`GridDiagram.alexanderTwoWeight` and a constant `GridDiagram.alexanderTwoShift`.

Together these turn the state sum into `∑_σ sgn(σ) ∏_c T^{w(c, σ c)}`, which is by definition the
determinant of `GridDiagram.weightMatrix`, the weight matrix whose `(c, r)` entry is the monomial
`T^{w(c, r)}`. That is `GridDiagram.stateSum_eq_smul_T_mul_det_weightMatrix`, the grid
determinant formula.

The grading variable `T` is a square root of the Alexander variable: the exponents are values of
`GridDiagram.alexanderTwoℤ`, which is twice the Alexander grading, because the Alexander grading
itself is only a half-integer unless the diagram presents an odd number of components. Working
with the doubled grading keeps every statement here free of that hypothesis; specialising to a
knot grid, where `2 A(x)` is even, costs nothing.

A first consequence, and a check that the formula is not vacuous: setting `T = 1` makes every
entry of the weight matrix equal to `1`, so its determinant vanishes as soon as the grid has two
columns. Hence `∑_x (-1)^{M_O(x)} = 0`, that is, on any grid of size at least two exactly half of
the states have even `O`-Maslov grading (`GridDiagram.sum_negOnePow_maslovOℤ_eq_zero`).

## Main definitions

* `TauCeti.GridDiagram.alexanderTwoWeight`, `TauCeti.GridDiagram.alexanderTwoShift`: the local
  weight of a grid point and the constant in the decomposition of twice the Alexander grading.
* `TauCeti.GridDiagram.weightMatrix`: the weight matrix, with monomial entries `T^{w(c, r)}`.
* `TauCeti.GridDiagram.stateSum`: the alternating state sum with exponents given by twice the
  Alexander grading.

## Main results

* `TauCeti.GridDiagram.alexanderTwoℤ_eq_sum_alexanderTwoWeight_add_shift`: twice the Alexander
  grading is a sum of local weights plus a constant.
* `TauCeti.GridDiagram.stateSum_eq_smul_T_mul_det_weightMatrix`: the grid determinant formula.
* `TauCeti.GridDiagram.sum_negOnePow_maslovOℤ_eq_zero`: the alternating sign sum over grid states
  vanishes on every grid of size at least two.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.4, "Euler
characteristic = Alexander polynomial, via the grid determinant formula". The determinant formula
is Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.3; identifying the
determinant with the Alexander polynomial of the link the diagram presents is the remaining half
of that milestone.
-/

public section

open LaurentPolynomial

namespace TauCeti

variable {n : ℕ}

/-- The monomial of a finite sum of exponents is the product of the monomials. -/
private theorem T_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    (T (∑ i ∈ s, f i) : ℤ[T;T⁻¹]) = ∏ i ∈ s, T (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, T_add, ih]

namespace GridDiagram

variable (G : GridDiagram n)

/-- The local weight of the grid point `(c, r)` in a grid diagram: the local `X`-marking-pairing
numerator minus the local `O`-marking-pairing numerator.

Twice the Alexander grading of a grid state is the sum of these weights over the grid points the
state occupies, up to the constant `GridDiagram.alexanderTwoShift`. -/
def alexanderTwoWeight (c r : Fin n) : ℤ :=
  (G.X.JNumCenterAt c r : ℤ) - (G.O.JNumCenterAt c r : ℤ)

/-- The local weight restated as its defining difference of marking-pairing numerators. -/
theorem alexanderTwoWeight_def (c r : Fin n) :
    G.alexanderTwoWeight c r = (G.X.JNumCenterAt c r : ℤ) - (G.O.JNumCenterAt c r : ℤ) := by
  rw [alexanderTwoWeight]

/-- The constant term in the decomposition of twice the Alexander grading: it involves only the
markings of the diagram and the grid size, not the grid state. -/
def alexanderTwoShift : ℤ :=
  (GridPoint.I G.OSet G.OSet : ℤ) - (GridPoint.I G.XSet G.XSet : ℤ) - ((n : ℤ) - 1)

/-- The constant term restated as its defining formula. -/
theorem alexanderTwoShift_def :
    G.alexanderTwoShift =
      (GridPoint.I G.OSet G.OSet : ℤ) - (GridPoint.I G.XSet G.XSet : ℤ) - ((n : ℤ) - 1) := by
  rw [alexanderTwoShift]

/-- Twice the Alexander grading of a grid state is the sum of the local weights of the grid points
it occupies, plus a constant depending only on the diagram.

The two `J`-self-pairings of the state cancel in `2 A = M_O - M_X - (n - 1)`, and each surviving
marking-pairing numerator fibres over the columns. -/
theorem alexanderTwoℤ_eq_sum_alexanderTwoWeight_add_shift (x : GridState n) :
    G.alexanderTwoℤ x = (∑ c : Fin n, G.alexanderTwoWeight c (x c)) + G.alexanderTwoShift := by
  simp only [alexanderTwoℤ_def, maslovOℤ_def, maslovXℤ_def, alexanderTwoShift_def,
    alexanderTwoWeight_def, OSet, XSet, GridState.JNumCenter_pointSet_eq_sum,
    Finset.sum_sub_distrib]
  push_cast
  ring

/-- The weight matrix of a grid diagram: the `(c, r)` entry is the monomial whose exponent is the
local Alexander weight of the grid point in column `c` and row `r`. -/
noncomputable def weightMatrix : Matrix (Fin n) (Fin n) ℤ[T;T⁻¹] :=
  Matrix.of fun c r => T (G.alexanderTwoWeight c r)

/-- The entries of the weight matrix are the monomials of the local Alexander weights. -/
@[simp]
theorem weightMatrix_apply (c r : Fin n) :
    G.weightMatrix c r = T (G.alexanderTwoWeight c r) := by
  rw [weightMatrix, Matrix.of_apply]

/-- The alternating Alexander state sum over the `n!` grid states, with monomial exponents given
by twice their Alexander gradings.

The exponents are values of `GridDiagram.alexanderTwoℤ`, so the variable `T` is a square root of
the usual Alexander variable. For odd-component diagrams, this state sum corresponds to the
graded Euler characteristic of the grid chain module after that change of variable; the
identification with `Grading/Chain.lean` is not formalized here. -/
noncomputable def stateSum : ℤ[T;T⁻¹] :=
  ∑ x : GridState n, (G.maslovOℤ x).negOnePow • T (G.alexanderTwoℤ x)

/-- The state sum restated as its defining alternating sum. -/
theorem stateSum_def :
    G.stateSum = ∑ x : GridState n, (G.maslovOℤ x).negOnePow • T (G.alexanderTwoℤ x) := by
  rw [stateSum]

/-- **The grid determinant formula.** The alternating Alexander state sum is a sign times a
monomial times the determinant of the weight matrix.

The sign and the monomial depend only on the markings and the grid size, so the determinant of
`GridDiagram.weightMatrix` carries all of the state-sum information. -/
theorem stateSum_eq_smul_T_mul_det_weightMatrix :
    G.stateSum =
      (Equiv.Perm.sign G.O.toPerm * ((n : ℤ) + 1).negOnePow) •
        (T G.alexanderTwoShift * G.weightMatrix.det) := by
  classical
  have hdet : G.weightMatrix.det =
      ∑ x : GridState n, ((Equiv.Perm.sign x.toPerm : ℤ) : ℤ[T;T⁻¹]) *
        ∏ c : Fin n, T (G.alexanderTwoWeight c (x c)) := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    refine (Fintype.sum_equiv (GridState.equivPerm n) _ _ fun x => ?_).symm
    simp only [GridState.equivPerm_apply, Matrix.transpose_apply, weightMatrix_apply]
  rw [stateSum_def, hdet, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [G.negOnePow_maslovOℤ x, G.alexanderTwoℤ_eq_sum_alexanderTwoWeight_add_shift x,
    T_add, T_sum]
  simp only [Units.smul_def, Units.val_mul, zsmul_eq_mul, Int.cast_mul]
  ring

/-- The alternating sign sum over grid states vanishes on every grid of size at least two: exactly
half of the `n!` grid states have even `O`-Maslov grading.

This is the grid determinant formula evaluated at `T = 1`, where every entry of the weight matrix
becomes `1` and the determinant has two equal rows. -/
theorem sum_negOnePow_maslovOℤ_eq_zero (hn : 2 ≤ n) :
    ∑ x : GridState n, ((G.maslovOℤ x).negOnePow : ℤ) = 0 := by
  set f : ℤ[T;T⁻¹] →+* ℤ := LaurentPolynomial.eval₂ (RingHom.id ℤ) 1 with hf
  have hT : ∀ m : ℤ, f (T m) = 1 := by
    intro m
    rw [hf, LaurentPolynomial.eval₂_T, one_zpow, Units.val_one]
  have hA : f G.stateSum = ∑ x : GridState n, ((G.maslovOℤ x).negOnePow : ℤ) := by
    rw [stateSum_def, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Units.smul_def, zsmul_eq_mul, map_mul, map_intCast, hT, mul_one, Int.cast_id]
  have hB : f G.stateSum = 0 := by
    rw [G.stateSum_eq_smul_T_mul_det_weightMatrix, Units.smul_def, zsmul_eq_mul, map_mul,
      map_intCast, map_mul, hT, RingHom.map_det, RingHom.mapMatrix_apply]
    have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
      simp
    have hrow : (G.weightMatrix.map f) ⟨0, by omega⟩ = (G.weightMatrix.map f) ⟨1, by omega⟩ := by
      funext r
      simp only [Matrix.map_apply, weightMatrix_apply, hT]
    rw [Matrix.det_zero_of_row_eq hne hrow, one_mul, mul_zero]
  rw [← hA, hB]

end GridDiagram

end TauCeti
