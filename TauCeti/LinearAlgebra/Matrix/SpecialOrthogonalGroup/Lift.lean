/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Lifting special orthogonal matrices

When `2` is invertible, a special orthogonal matrix lifts across a quotient by a square-zero
ideal. Starting from arbitrary lifts of its entries, let `E = M Mᵀ - 1` be the error in the
orthogonality equation. Its entries lie in the ideal and `E` is symmetric. Multiplication by
`1 - E / 2` corrects the error; all quadratic terms vanish because the ideal is square-zero.

The corrected matrix is orthogonal. Its determinant squares to one and is congruent to one
modulo the ideal. Invertibility of `2` then forces its determinant to equal one, so the lift is
special orthogonal.

## Main declarations

* `Matrix.SpecialOrthogonalGroup.map`: entrywise mapping of special orthogonal matrices.
* `Matrix.SpecialOrthogonalGroup.map_quotient_mk_surjective_of_sq_eq_bot`: special orthogonal
  matrices lift across square-zero quotients when `2` is invertible.

## References

* The Stacks Project, Tag 00TH, for the infinitesimal lifting criterion for formal smoothness.
* SGA 3, Exposé XXIII, for the split special orthogonal group away from characteristic two.
-/

public section

open Matrix

namespace Matrix.SpecialOrthogonalGroup

universe u v

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type u} [CommRing R]

attribute [local instance] starRingOfComm

/-- A ring homomorphism maps special orthogonal matrices to special orthogonal matrices. -/
theorem map_mem {S : Type v} [CommRing S] (f : R →+* S)
    {M : Matrix n n R} (hM : M ∈ Matrix.specialOrthogonalGroup n R) :
    M.map f ∈ Matrix.specialOrthogonalGroup n S := by
  rw [Matrix.mem_specialOrthogonalGroup_iff] at hM ⊢
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff n S]
    calc
      M.map f * (M.map f)ᵀ = (M * Mᵀ).map f := by
        rw [← Matrix.transpose_map]
        exact Matrix.map_mul.symm
      _ = 1 := by
        rw [(Matrix.mem_orthogonalGroup_iff n R).mp hM.1]
        exact Matrix.map_one f f.map_zero f.map_one
  · calc
      (M.map f).det = f M.det := (RingHom.map_det f M).symm
      _ = 1 := by rw [hM.2, map_one]

/-- A ring homomorphism maps special orthogonal matrices entrywise. -/
def map {S : Type v} [CommRing S] (f : R →+* S) :
    Matrix.specialOrthogonalGroup n R →* Matrix.specialOrthogonalGroup n S where
  toFun M := ⟨M.1.map f, map_mem f M.2⟩
  map_one' := Subtype.ext (Matrix.map_one f f.map_zero f.map_one)
  map_mul' _ _ := Subtype.ext Matrix.map_mul

/-- Entrywise mapping of a special orthogonal matrix has the expected underlying matrix. -/
@[simp]
theorem coe_map {S : Type v} [CommRing S] (f : R →+* S)
    (M : Matrix.specialOrthogonalGroup n R) :
    (map f M : Matrix n n S) = M.1.map f :=
  by simp [map]

private theorem matrix_mul_eq_zero_of_entries_mem {m : Type*} [Fintype m]
    (I : Ideal R) (hI : I ^ 2 = (⊥ : Ideal R)) (A B : Matrix m m R)
    (hA : ∀ i j, A i j ∈ I) (hB : ∀ i j, B i j ∈ I) : A * B = 0 := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [← Ideal.mem_bot]
  exact hI ▸ (by simpa only [pow_two] using Ideal.mul_mem_mul (hA i k) (hB k j))

/-- Every special orthogonal matrix modulo a square-zero ideal lifts to a special orthogonal
matrix when `2` is invertible in the coefficient ring. -/
theorem map_quotient_mk_surjective_of_sq_eq_bot [Invertible (2 : R)]
    (I : Ideal R) (hI : I ^ 2 = (⊥ : Ideal R)) :
    Function.Surjective
      (map (n := n) (Ideal.Quotient.mk I)) := by
  intro g
  choose m hm using fun i j ↦ Ideal.Quotient.mk_surjective (g.1 i j)
  let M : Matrix n n R := m
  let qMat : Matrix n n R →+* Matrix n n (R ⧸ I) :=
    RingHom.mapMatrix (Ideal.Quotient.mk I)
  have hM_map : qMat M = g.1 := by
    ext i j
    simpa only [qMat, RingHom.mapMatrix_apply, Matrix.map_apply] using hm i j
  let E : Matrix n n R := M * Mᵀ - 1
  have hE_map : qMat E = 0 := by
    dsimp only [E]
    have hM_transpose_map : qMat Mᵀ = (qMat M)ᵀ := by
      simpa only [qMat, RingHom.mapMatrix_apply] using
        (Matrix.transpose_map (f := Ideal.Quotient.mk I) (M := M))
    rw [map_sub, map_mul, hM_transpose_map, hM_map,
      (Matrix.mem_orthogonalGroup_iff n (R ⧸ I)).mp g.2.1, map_one, sub_self]
  have hE_mem : ∀ i j, E i j ∈ I := by
    intro i j
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa only [qMat, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply] using
      congrFun (congrFun hE_map i) j
  have hE_transpose : Eᵀ = E := by
    dsimp only [E]
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_one]
  let X : Matrix n n R := -(⅟(2 : R)) • E
  have hX_mem : ∀ i j, X i j ∈ I := by
    intro i j
    exact I.smul_mem _ (hE_mem i j)
  have hX_transpose : Xᵀ = X := by
    dsimp only [X]
    rw [Matrix.transpose_smul, hE_transpose]
  have hX_add : X + Xᵀ = -E := by
    rw [hX_transpose]
    dsimp only [X]
    rw [← add_smul]
    simp only [← neg_add, invOf_two_add_invOf_two, neg_smul, one_smul]
  have hXX : X * Xᵀ = 0 :=
    matrix_mul_eq_zero_of_entries_mem I hI X Xᵀ hX_mem (fun i j ↦ hX_mem j i)
  have hXE : X * E = 0 :=
    matrix_mul_eq_zero_of_entries_mem I hI X E hX_mem hE_mem
  have hEX : E * Xᵀ = 0 :=
    matrix_mul_eq_zero_of_entries_mem I hI E Xᵀ hE_mem (fun i j ↦ hX_mem j i)
  let N : Matrix n n R := (1 + X) * M
  have hM_mul : M * Mᵀ = 1 + E := by
    dsimp only [E]
    abel
  have hN_orthogonal : N * Nᵀ = 1 := by
    dsimp only [N]
    rw [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_one]
    calc
      (1 + X) * M * (Mᵀ * (1 + Xᵀ)) =
          (1 + X) * (M * Mᵀ) * (1 + Xᵀ) := by noncomm_ring
      _ = (1 + X) * (1 + E) * (1 + Xᵀ) := by rw [hM_mul]
      _ = 1 + E + X + X * E + Xᵀ + E * Xᵀ + X * Xᵀ +
          (X * E) * Xᵀ := by noncomm_ring
      _ = 1 := by
        rw [hXE, hEX, hXX, zero_mul]
        simp only [add_zero]
        calc
          1 + E + X + Xᵀ = 1 + (E + (X + Xᵀ)) := by abel
          _ = 1 := by rw [hX_add]; abel
  have hX_map : qMat X = 0 := by
    ext i j
    dsimp only [qMat]
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hX_mem i j
  have hN_map : qMat N = g.1 := by
    dsimp only [N]
    rw [map_mul, map_add, map_one, hX_map, add_zero, one_mul, hM_map]
  have hdet_map : Ideal.Quotient.mk I N.det = 1 := by
    calc
      Ideal.Quotient.mk I N.det = (qMat N).det := by
        simpa only [qMat, RingHom.mapMatrix_apply] using
          (RingHom.map_det (Ideal.Quotient.mk I) N)
      _ = 1 := by rw [hN_map]; exact g.2.2
  have hdet_sub_mem : N.det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hdet_map, map_one, sub_self]
  have hdet_sub_sq : (N.det - 1) ^ 2 = 0 := by
    rw [← Ideal.mem_bot, ← hI]
    simpa only [pow_two] using Ideal.mul_mem_mul hdet_sub_mem hdet_sub_mem
  have hdet_sq : N.det ^ 2 = 1 := by
    have hdet := congrArg Matrix.det hN_orthogonal
    simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, pow_two] using hdet
  have htwo : (2 : R) * (N.det - 1) = 0 := by
    calc
      (2 : R) * (N.det - 1) = N.det ^ 2 - 1 - (N.det - 1) ^ 2 := by ring
      _ = 0 := by rw [hdet_sq, hdet_sub_sq]; ring
  have hdet : N.det = 1 := by
    apply sub_eq_zero.mp
    apply (isUnit_of_invertible (2 : R)).mul_left_cancel
    simpa only [mul_zero] using htwo
  let lift : Matrix.specialOrthogonalGroup n R :=
    ⟨N, (Matrix.mem_specialOrthogonalGroup_iff).mpr
      ⟨(Matrix.mem_orthogonalGroup_iff n R).mpr hN_orthogonal, hdet⟩⟩
  refine ⟨lift, ?_⟩
  apply Subtype.ext
  simpa only [coe_map, RingHom.mapMatrix_apply, lift, qMat] using hN_map

end Matrix.SpecialOrthogonalGroup
