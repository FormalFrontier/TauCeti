/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Basic
public import Mathlib.Algebra.Polynomial.Laurent

/-!
# A Laurent-polynomial path in the special linear group

A unit in a commutative ring defines a determinant-one diagonal matrix by placing the unit and
its inverse in two distinct diagonal positions. Over a field, specializing the Laurent variable
recovers Mathlib's `Matrix.SpecialLinearGroup.diag2n` matrix. This supplies the diagonal
one-parameter family used to prove connectedness of `SLₙ`.

## Main declarations

* `TauCeti.SpecialLinear.diag2nUnit`: the two-coordinate diagonal matrix attached to a unit.
* `TauCeti.SpecialLinear.map_diag2nUnit_laurent`: specialization of the generic Laurent matrix.
-/

public section

open scoped LaurentPolynomial

namespace TauCeti.SpecialLinear

universe u v

noncomputable section

/-- The Laurent variable regarded as a unit of the Laurent-polynomial ring. -/
def laurentVariableUnit {K : Type u} [Field K] : (LaurentPolynomial K)ˣ :=
  unitOfInvertible (LaurentPolynomial.T 1)

@[simp]
theorem laurentVariableUnit_val {K : Type u} [Field K] :
    (laurentVariableUnit (K := K) : LaurentPolynomial K) = LaurentPolynomial.T 1 := by
  simp [laurentVariableUnit]

/-- The determinant-one diagonal matrix with a unit in position `i`, its inverse in position
`j`, and ones in every other position. -/
noncomputable def diag2nUnit {R : Type u} [CommRing R]
    {m : Type v} [Fintype m] [DecidableEq m] {i j : m} (hij : i ≠ j)
    (a : Rˣ) : Matrix.SpecialLinearGroup m R :=
  ⟨Matrix.diagonal (fun r ↦
      if r = i then (a : R) else if r = j then ((a⁻¹ : Rˣ) : R) else 1), by
    rw [Matrix.det_diagonal]
    simp [Finset.prod_ite, hij.symm,
      Finset.card_eq_one (s := {r : m | r = i}).2 ⟨i, by grind⟩]⟩

private theorem point_diag2nUnit_laurent_apply
    {K : Type u} [Field K] {n : ℕ} {i j : Fin n} (hij : i ≠ j) (b : Kˣ)
    (r s : Fin n) :
    MultiplicativeGroup.point (R := K) b
        ((diag2nUnit hij (laurentVariableUnit (K := K))).1 r s) =
      (Matrix.SpecialLinearGroup.diag2n hij (b : K) (Units.ne_zero b)).1 r s := by
  let eval : LaurentPolynomial K →ₐ[K] K := MultiplicativeGroup.point b
  have hunit : Units.map eval.toMonoidHom (laurentVariableUnit (K := K)) = b := by
    apply Units.ext
    simp [eval]
  have hinv : eval
      (((laurentVariableUnit (K := K))⁻¹ : (LaurentPolynomial K)ˣ) : LaurentPolynomial K) =
        ((b⁻¹ : Kˣ) : K) := by
    change ((Units.map eval.toMonoidHom ((laurentVariableUnit (K := K))⁻¹) : Kˣ) : K) = _
    rw [map_inv, hunit]
  rw [Matrix.SpecialLinearGroup.diag2n_coe, Matrix.diagonal_apply]
  change eval ((diag2nUnit hij (laurentVariableUnit (K := K))).1 r s) = _
  dsimp only [diag2nUnit]
  rw [Matrix.diagonal_apply]
  by_cases hrs : r = s
  · subst s
    by_cases hri : r = i
    · simp [hri, eval]
    · by_cases hrj : r = j
      · simpa [hri, hrj, hij.symm] using hinv
      · simp [hri, hrj]
  · simp [hrs]

/-- Evaluating the generic Laurent diagonal matrix at a unit `b` gives the ordinary
two-coordinate diagonal matrix with entries `b` and `b⁻¹`. -/
theorem map_diag2nUnit_laurent
    {K : Type u} [Field K] {n : ℕ} {i j : Fin n} (hij : i ≠ j) (b : Kˣ) :
    Matrix.SpecialLinearGroup.map
        (MultiplicativeGroup.point (R := K) b).toRingHom
        (diag2nUnit hij (laurentVariableUnit (K := K))) =
      Matrix.SpecialLinearGroup.diag2n hij (b : K) (Units.ne_zero b) := by
  ext r s
  change MultiplicativeGroup.point (R := K) b
      ((diag2nUnit hij (laurentVariableUnit (K := K))).1 r s) =
    (Matrix.SpecialLinearGroup.diag2n hij (b : K) (Units.ne_zero b)).1 r s
  exact point_diag2nUnit_laurent_apply hij b r s

end

end TauCeti.SpecialLinear
