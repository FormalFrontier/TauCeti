/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The matrices `1 - u ⊗ v`

This file develops the matrix calculus for the rank-one perturbations `1 - vecMulVec u v` of the
identity: their products, the commutation and braid relations, the quadratic relation, the
inverse, the determinant, and the resulting element of the general linear group. Everything is
stated for plain pairs of vectors, and every hypothesis is a value of one of the pairings
`v ⬝ᵥ u` of the vectors involved.

## Main definitions

* `TauCeti.oneSubVecMulVecGL`: `1 - vecMulVec u v` as an element of the general linear group, when
  its self-pairing `v ⬝ᵥ u` is `t + 1` for a unit `t`.

## Main results

* `TauCeti.one_sub_vecMulVec_mul_comm` and `TauCeti.one_sub_vecMulVec_braid`: the commutation and
  braid relations, from the values of the pairings.
* `TauCeti.one_sub_vecMulVec_mul_self`: the quadratic relation.
* `TauCeti.det_one_sub_vecMulVec` and `TauCeti.inv_one_sub_vecMulVec`: the determinant and the
  inverse.
-/

public section

open Matrix

namespace TauCeti

variable {R α : Type*} [CommRing R] [Fintype α] [DecidableEq α]

/-- The product of two rank-one perturbations of the identity. -/
theorem one_sub_vecMulVec_mul_one_sub_vecMulVec (u₁ v₁ u₂ v₂ : α → R) :
    (1 - vecMulVec u₁ v₁) * (1 - vecMulVec u₂ v₂) =
      1 - vecMulVec u₁ v₁ - vecMulVec u₂ v₂ + (v₁ ⬝ᵥ u₂) • vecMulVec u₁ v₂ := by
  simp only [sub_mul, mul_sub, one_mul, mul_one, vecMulVec_mul_vecMulVec, vecMulVec_smul]
  abel

/-- Two rank-one perturbations of the identity commute when their cross-pairings vanish. -/
theorem one_sub_vecMulVec_mul_comm {u₁ v₁ u₂ v₂ : α → R} (h₁₂ : v₁ ⬝ᵥ u₂ = 0)
    (h₂₁ : v₂ ⬝ᵥ u₁ = 0) :
    (1 - vecMulVec u₁ v₁) * (1 - vecMulVec u₂ v₂) =
      (1 - vecMulVec u₂ v₂) * (1 - vecMulVec u₁ v₁) := by
  rw [one_sub_vecMulVec_mul_one_sub_vecMulVec, one_sub_vecMulVec_mul_one_sub_vecMulVec, h₁₂, h₂₁]
  simp only [zero_smul, add_zero]
  abel

/-- Two rank-one perturbations of the identity obey the braid relation when both self-pairings
equal one plus the product of the cross-pairings. -/
theorem one_sub_vecMulVec_braid {u₁ v₁ u₂ v₂ : α → R}
    (h₁ : v₁ ⬝ᵥ u₁ = 1 + (v₁ ⬝ᵥ u₂) * (v₂ ⬝ᵥ u₁))
    (h₂ : v₂ ⬝ᵥ u₂ = 1 + (v₁ ⬝ᵥ u₂) * (v₂ ⬝ᵥ u₁)) :
    (1 - vecMulVec u₁ v₁) * (1 - vecMulVec u₂ v₂) * (1 - vecMulVec u₁ v₁) =
      (1 - vecMulVec u₂ v₂) * (1 - vecMulVec u₁ v₁) * (1 - vecMulVec u₂ v₂) := by
  simp only [sub_mul, mul_sub, one_mul, mul_one, vecMulVec_mul_vecMulVec,
    vecMulVec_smul, smul_mul_assoc, smul_smul, h₁, h₂]
  module

/-- The quadratic relation for a rank-one perturbation of the identity whose self-pairing is
`t + 1`. -/
theorem one_sub_vecMulVec_mul_self (t : R) {u v : α → R} (h : v ⬝ᵥ u = t + 1) :
    (1 - vecMulVec u v) * (1 - vecMulVec u v) = (1 - t) • (1 - vecMulVec u v) + t • 1 := by
  rw [one_sub_vecMulVec_mul_one_sub_vecMulVec, h]
  module

/-- A right inverse for a rank-one perturbation of the identity whose self-pairing is `t + 1`. -/
theorem one_sub_vecMulVec_mul_inv (t : Rˣ) {u v : α → R} (h : v ⬝ᵥ u = (t : R) + 1) :
    (1 - vecMulVec u v) * (1 - ((t⁻¹ : Rˣ) : R) • vecMulVec u v) = 1 := by
  have hb : vecMulVec u v * vecMulVec u v = ((t : R) + 1) • vecMulVec u v := by
    rw [vecMulVec_mul_vecMulVec, h, vecMulVec_smul]
  have hc : ((t⁻¹ : Rˣ) : R) * ((t : R) + 1) = 1 + ((t⁻¹ : Rˣ) : R) := by
    rw [mul_add, mul_one, Units.inv_mul]
  simp only [sub_mul, mul_sub, one_mul, mul_one, mul_smul_comm, hb, smul_sub]
  rw [smul_smul, hc, add_smul, one_smul]
  abel

/-- A left inverse for a rank-one perturbation of the identity whose self-pairing is `t + 1`. -/
theorem one_sub_vecMulVec_inv_mul (t : Rˣ) {u v : α → R} (h : v ⬝ᵥ u = (t : R) + 1) :
    (1 - ((t⁻¹ : Rˣ) : R) • vecMulVec u v) * (1 - vecMulVec u v) = 1 :=
  mul_eq_one_comm.mp (one_sub_vecMulVec_mul_inv t h)

/-- The determinant of a rank-one perturbation of the identity in terms of its self-pairing. -/
@[simp]
theorem det_one_sub_vecMulVec (u v : α → R) : (1 - vecMulVec u v).det = 1 - v ⬝ᵥ u := by
  rw [sub_eq_add_neg, ← neg_vecMulVec, vecMulVec_eq Unit,
    det_one_add_replicateCol_mul_replicateRow, dotProduct_neg]
  ring

/-- A rank-one perturbation of the identity as an element of the general linear group, when its
self-pairing is `t + 1`. -/
def oneSubVecMulVecGL (t : Rˣ) (u v : α → R) (h : v ⬝ᵥ u = (t : R) + 1) : GL α R where
  val := 1 - vecMulVec u v
  inv := 1 - ((t⁻¹ : Rˣ) : R) • vecMulVec u v
  val_inv := one_sub_vecMulVec_mul_inv t h
  inv_val := one_sub_vecMulVec_inv_mul t h

/-- The matrix underlying `TauCeti.oneSubVecMulVecGL`. -/
@[simp]
theorem coe_oneSubVecMulVecGL (t : Rˣ) (u v : α → R) (h : v ⬝ᵥ u = (t : R) + 1) :
    (oneSubVecMulVecGL t u v h : Matrix α α R) = 1 - vecMulVec u v :=
  (rfl)

/-- The inverse of a rank-one perturbation of the identity whose self-pairing is `t + 1`.

This is not a `simp` lemma: the unit `t` occurs only in the right-hand side and in the
hypothesis, so `simp` cannot infer it from the left-hand side. Consumers that fix `t` — such as
`TauCeti.KnotTheory.inv_reducedBurauColMatrix` — carry the `simp` attribute instead. -/
theorem inv_one_sub_vecMulVec (t : Rˣ) {u v : α → R} (h : v ⬝ᵥ u = (t : R) + 1) :
    (1 - vecMulVec u v)⁻¹ = 1 - ((t⁻¹ : Rˣ) : R) • vecMulVec u v :=
  Matrix.inv_eq_right_inv (one_sub_vecMulVec_mul_inv t h)

end TauCeti
