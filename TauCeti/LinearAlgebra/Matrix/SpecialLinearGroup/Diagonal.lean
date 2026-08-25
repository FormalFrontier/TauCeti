/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Diagonal matrices in the special linear group

A unit in a commutative ring defines a determinant-one diagonal matrix by placing the unit and
its inverse in two distinct diagonal positions. This generalizes Mathlib's field-valued
`Matrix.SpecialLinearGroup.diag2n` construction.

## Main declarations

* `Matrix.SpecialLinearGroup.diag2nUnit`: the two-coordinate diagonal matrix attached to a unit.
* `Matrix.SpecialLinearGroup.map_diag2nUnit`: naturality under a ring homomorphism.

## References

The definition of `diag2nUnit` and its determinant proof generalize and are adapted from Mathlib's
`Matrix.SpecialLinearGroup.diag2n`.
-/

public section

namespace TauCeti

universe u v w

noncomputable section

/-- The determinant-one diagonal matrix with a unit in position `i`, its inverse in position
`j`, and ones in every other position. This generalizes Mathlib's
`Matrix.SpecialLinearGroup.diag2n`; the determinant proof is adapted from that construction. -/
noncomputable def _root_.Matrix.SpecialLinearGroup.diag2nUnit {R : Type u} [CommRing R]
    {m : Type v} [Fintype m] [DecidableEq m] {i j : m} (hij : i ≠ j)
    (a : Rˣ) : Matrix.SpecialLinearGroup m R :=
  ⟨Matrix.diagonal (fun r ↦
      if r = i then (a : R) else if r = j then ((a⁻¹ : Rˣ) : R) else 1), by
    rw [Matrix.det_diagonal]
    simp [Finset.prod_ite, hij.symm,
      Finset.card_eq_one (s := {r : m | r = i}).2 ⟨i, by grind⟩]⟩

/-- The matrix underlying `diag2nUnit` is its defining diagonal matrix. -/
@[simp]
theorem _root_.Matrix.SpecialLinearGroup.diag2nUnit_coe {R : Type u} [CommRing R]
    {m : Type v} [Fintype m] [DecidableEq m] {i j : m} (hij : i ≠ j) (a : Rˣ) :
    (Matrix.SpecialLinearGroup.diag2nUnit hij a).1 = Matrix.diagonal (fun r ↦
      if r = i then (a : R) else if r = j then ((a⁻¹ : Rˣ) : R) else 1) :=
  by rw [Matrix.SpecialLinearGroup.diag2nUnit]

/-- Mapping the coefficients of a unit diagonal matrix maps its defining unit. -/
@[simp]
theorem _root_.Matrix.SpecialLinearGroup.map_diag2nUnit
    {R : Type u} {S : Type w} [CommRing R] [CommRing S]
    {m : Type v} [Fintype m] [DecidableEq m] {i j : m} (hij : i ≠ j)
    (f : R →+* S) (a : Rˣ) :
    Matrix.SpecialLinearGroup.map f (Matrix.SpecialLinearGroup.diag2nUnit hij a) =
      Matrix.SpecialLinearGroup.diag2nUnit hij (Units.map f a) := by
  ext r s
  simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.diagonal_apply, apply_ite f]

/-- The unit diagonal family takes the identity unit to the identity matrix. -/
@[simp]
theorem _root_.Matrix.SpecialLinearGroup.diag2nUnit_one {R : Type u} [CommRing R]
    {m : Type v} [Fintype m] [DecidableEq m] {i j : m} (hij : i ≠ j) :
    Matrix.SpecialLinearGroup.diag2nUnit hij (1 : Rˣ) = 1 := by
  ext r s
  simp [Matrix.SpecialLinearGroup.diag2nUnit_coe, Matrix.diagonal_apply, Matrix.one_apply]

/-- Over a field, the unit construction specializes to Mathlib's two-coordinate diagonal
matrix. -/
@[simp]
theorem _root_.Matrix.SpecialLinearGroup.diag2nUnit_mk0 {K : Type u} [Field K]
    {m : Type v} [Fintype m] [DecidableEq m] {i j : m} (hij : i ≠ j)
    (b : K) (hb : b ≠ 0) :
    Matrix.SpecialLinearGroup.diag2nUnit hij (Units.mk0 b hb) =
      Matrix.SpecialLinearGroup.diag2n hij b hb := by
  apply Subtype.ext
  simp [Matrix.SpecialLinearGroup.diag2nUnit_coe, Matrix.SpecialLinearGroup.diag2n_coe,
    Units.val_mk0, Units.val_inv_eq_inv_val]

end

end TauCeti
