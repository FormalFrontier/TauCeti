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

/-- Mapping the coefficients of a unit diagonal matrix maps its defining unit. -/
theorem map_diag2nUnit {R S : Type u} [CommRing R] [CommRing S]
    {m : Type v} [Fintype m] [DecidableEq m] {i j : m} (hij : i ≠ j)
    (f : R →+* S) (a : Rˣ) :
    Matrix.SpecialLinearGroup.map f (diag2nUnit hij a) =
      diag2nUnit hij (Units.map f a) := by
  apply Subtype.ext
  change f.mapMatrix (Matrix.diagonal fun r ↦
      if r = i then (a : R) else if r = j then ((a⁻¹ : Rˣ) : R) else 1) =
    Matrix.diagonal fun r ↦
      if r = i then ((Units.map f a : Sˣ) : S) else
        if r = j then (((Units.map f a)⁻¹ : Sˣ) : S) else 1
  rw [RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero f)]
  congr 1
  funext r
  rw [apply_ite (f := f), apply_ite (f := f), map_one]
  congr 1

/-- Over a field, the unit construction specializes to Mathlib's two-coordinate diagonal
matrix. -/
theorem diag2nUnit_mk0 {K : Type u} [Field K]
    {m : Type v} [Fintype m] [DecidableEq m] {i j : m} (hij : i ≠ j)
    (b : K) (hb : b ≠ 0) :
    diag2nUnit hij (Units.mk0 b hb) = Matrix.SpecialLinearGroup.diag2n hij b hb := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.diag2n_coe]
  rfl

/-- Evaluating the generic Laurent diagonal matrix at a unit `b` gives the ordinary
two-coordinate diagonal matrix with entries `b` and `b⁻¹`. -/
theorem map_diag2nUnit_laurent
    {K : Type u} [Field K] {n : ℕ} {i j : Fin n} (hij : i ≠ j) (b : Kˣ) :
    Matrix.SpecialLinearGroup.map
        (MultiplicativeGroup.point (R := K) b).toRingHom
        (diag2nUnit hij (Cocharacter.genericUnit K)) =
      Matrix.SpecialLinearGroup.diag2n hij (b : K) (Units.ne_zero b) := by
  rw [map_diag2nUnit]
  have hunit : Units.map
      (MultiplicativeGroup.point (R := K) b).toRingHom.toMonoidHom
      (Cocharacter.genericUnit K) = b := by
    apply Units.ext
    simp
  have hb : Units.mk0 (b : K) (Units.ne_zero b) = b := Units.ext rfl
  calc
    diag2nUnit hij
        (Units.map (MultiplicativeGroup.point (R := K) b).toRingHom.toMonoidHom
          (Cocharacter.genericUnit K)) = diag2nUnit hij b := congrArg (diag2nUnit hij) hunit
    _ = diag2nUnit hij (Units.mk0 (b : K) (Units.ne_zero b)) :=
      congrArg (diag2nUnit hij) hb.symm
    _ = Matrix.SpecialLinearGroup.diag2n hij (b : K) (Units.ne_zero b) :=
      diag2nUnit_mk0 hij (b : K) (Units.ne_zero b)

end

end TauCeti.SpecialLinear
