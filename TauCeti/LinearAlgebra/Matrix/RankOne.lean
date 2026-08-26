/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Rank-one matrix families

This file develops the matrix calculus for families of the form `1 - u i ⊗ v i`. It gives
their products, braid and quadratic relations, inverses, determinants, and units.

## Main definitions

* `TauCeti.RankOneMatrix.family`: the family of matrices `1 - u i ⊗ v i`.
* `TauCeti.RankOneMatrix.unit`: a member of the family as an element of the general linear group
  when its self-pairing has the Burau value.

## Main results

* `TauCeti.RankOneMatrix.family_mul_comm` and
  `TauCeti.RankOneMatrix.family_braid_of_adjacent`: the braid relations.
* `TauCeti.RankOneMatrix.family_mul_self`: the quadratic relation.
-/

public section

open Matrix

namespace TauCeti

variable {R : Type*} {n : ℕ}

namespace RankOneMatrix

variable {ι α : Type*}

section Ring

variable [Ring R] [DecidableEq α]

/-- The family of matrices `1 - u i ⊗ v i` associated to two families of vectors. -/
def family (u v : ι → α → R) (i : ι) : Matrix α α R :=
  1 - vecMulVec (u i) (v i)

/-- The defining formula for a rank-one matrix family. -/
lemma family_def (u v : ι → α → R) (i : ι) :
    family u v i = 1 - vecMulVec (u i) (v i) :=
  (rfl)

end Ring

section CommRing

variable [CommRing R] [Fintype α] [DecidableEq α]

/-- The product of two members of a rank-one matrix family. -/
theorem family_mul_family (u v : ι → α → R) (i j : ι) :
    family u v i * family u v j =
      1 - vecMulVec (u i) (v i) - vecMulVec (u j) (v j) +
        (v i ⬝ᵥ u j) • vecMulVec (u i) (v j) := by
  simp only [family, sub_mul, mul_sub, one_mul, mul_one, vecMulVec_mul_vecMulVec,
    vecMulVec_smul]
  abel

/-- Two members of a rank-one matrix family commute when their cross-pairings vanish. -/
theorem family_mul_comm (u v : ι → α → R) {i j : ι} (hij : v i ⬝ᵥ u j = 0)
    (hji : v j ⬝ᵥ u i = 0) : family u v i * family u v j = family u v j * family u v i := by
  rw [family_mul_family, family_mul_family, hij, hji]
  simp only [zero_smul, add_zero]
  abel

/-- Two members of a rank-one matrix family obey the braid relation when their four pairings have
the values occurring in the Burau representation. -/
theorem family_braid (t : R) (u v : ι → α → R) {i j : ι} (hii : v i ⬝ᵥ u i = t + 1)
    (hjj : v j ⬝ᵥ u j = t + 1) (hij : v i ⬝ᵥ u j = -t) (hji : v j ⬝ᵥ u i = -1) :
    family u v i * family u v j * family u v i =
      family u v j * family u v i * family u v j := by
  simp only [family, sub_mul, mul_sub, one_mul, mul_one, vecMulVec_mul_vecMulVec,
    vecMulVec_smul, smul_mul_assoc, smul_smul, hii, hjj, hij, hji]
  module

/-- The braid relation for two members of a rank-one matrix family indexed by adjacent generators,
in the symmetric form: the two possible adjacency orders are covered at once. -/
theorem family_braid_of_adjacent (t : R) (u v : Fin (n - 1) → α → R)
    (hself : ∀ i, v i ⬝ᵥ u i = t + 1)
    (hbraid : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 1 = j → v i ⬝ᵥ u j = -t ∧ v j ⬝ᵥ u i = -1)
    {i j : Fin (n - 1)} (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    family u v i * family u v j * family u v i =
      family u v j * family u v i * family u v j := by
  rcases h with h | h
  · exact family_braid t u v (hself i) (hself j) (hbraid h).1 (hbraid h).2
  · exact (family_braid t u v (hself j) (hself i) (hbraid h).1 (hbraid h).2).symm

/-- The quadratic relation for a member of a rank-one matrix family whose self-pairing is
`t + 1`. -/
theorem family_mul_self (t : R) (u v : ι → α → R) (i : ι) (hii : v i ⬝ᵥ u i = t + 1) :
    family u v i * family u v i = (1 - t) • family u v i + t • 1 := by
  rw [family_mul_family, hii, family]
  module

/-- A right inverse for a member of a rank-one matrix family whose self-pairing is `t + 1`. -/
theorem family_mul_inv (t : Rˣ) (u v : ι → α → R) (i : ι)
    (hii : v i ⬝ᵥ u i = (t : R) + 1) :
    family u v i * (1 - ((t⁻¹ : Rˣ) : R) • vecMulVec (u i) (v i)) = 1 := by
  have hb : vecMulVec (u i) (v i) * vecMulVec (u i) (v i) =
      ((t : R) + 1) • vecMulVec (u i) (v i) := by
    rw [vecMulVec_mul_vecMulVec, hii, vecMulVec_smul]
  have hc : ((t⁻¹ : Rˣ) : R) * ((t : R) + 1) = 1 + ((t⁻¹ : Rˣ) : R) := by
    rw [mul_add, mul_one, Units.inv_mul]
  simp only [family, sub_mul, mul_sub, one_mul, mul_one, mul_smul_comm, hb, smul_sub]
  rw [smul_smul, hc, add_smul, one_smul]
  abel

/-- A left inverse for a member of a rank-one matrix family whose self-pairing is `t + 1`. -/
theorem family_inv_mul (t : Rˣ) (u v : ι → α → R) (i : ι)
    (hii : v i ⬝ᵥ u i = (t : R) + 1) :
    (1 - ((t⁻¹ : Rˣ) : R) • vecMulVec (u i) (v i)) * family u v i = 1 :=
  mul_eq_one_comm.mp (family_mul_inv t u v i hii)

/-- The determinant of a member of a rank-one matrix family in terms of its self-pairing. -/
theorem det_family (u v : ι → α → R) (i : ι) :
    (family u v i).det = 1 - v i ⬝ᵥ u i := by
  rw [family, sub_eq_add_neg, ← neg_vecMulVec, vecMulVec_eq Unit,
    det_one_add_replicateCol_mul_replicateRow, dotProduct_neg]
  ring

/-- A member of a rank-one matrix family as an element of the general linear group, when its
self-pairing is `t + 1`. -/
def unit (t : Rˣ) (u v : ι → α → R) (hself : ∀ i, v i ⬝ᵥ u i = (t : R) + 1) (i : ι) :
    GL α R where
  val := family u v i
  inv := 1 - ((t⁻¹ : Rˣ) : R) • vecMulVec (u i) (v i)
  val_inv := family_mul_inv t u v i (hself i)
  inv_val := family_inv_mul t u v i (hself i)

/-- The matrix underlying `TauCeti.RankOneMatrix.unit`. -/
@[simp]
theorem coe_unit (t : Rˣ) (u v : ι → α → R) (hself : ∀ i, v i ⬝ᵥ u i = (t : R) + 1)
    (i : ι) : (unit t u v hself i : Matrix α α R) = family u v i :=
  (rfl)

/-- The inverse of a member of a rank-one matrix family whose self-pairing is `t + 1`. -/
theorem inv_family (t : Rˣ) (u v : ι → α → R) (i : ι)
    (hii : v i ⬝ᵥ u i = (t : R) + 1) :
    (family u v i)⁻¹ = 1 - ((t⁻¹ : Rˣ) : R) • vecMulVec (u i) (v i) :=
  Matrix.inv_eq_right_inv (family_mul_inv t u v i hii)

end CommRing

end RankOneMatrix

end TauCeti
