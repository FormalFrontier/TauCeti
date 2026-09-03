/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Lifting symplectic matrices

A symplectic matrix lifts across a quotient by a square-zero ideal. Starting with arbitrary
lifts of its entries, the failure to preserve the standard alternating form is an alternating
matrix with entries in the ideal. Its strict upper triangle gives an integral solution of the
linearized symplectic equation; this avoids division by two and therefore works in characteristic
two. The quadratic correction terms vanish because the ideal is square-zero.

## Main declaration

* `TauCeti.GLSymplectic.map_quotient_mk_surjective_of_sq_eq_bot`: entrywise reduction modulo a
  square-zero ideal is surjective on symplectic groups.

## References

* The Stacks Project, Tag 00TH, for the infinitesimal lifting criterion for formal smoothness.
* SGA 3, Exposé XXII, for the smooth split symplectic group scheme over `ℤ`.

This is the infinitesimal lifting input for the smoothness of the symplectic group scheme, a
prerequisite for the `Sp_{2n}` reductivity example in Layer 6 of the ReductiveGroups roadmap.
-/

public section

open Matrix

namespace TauCeti.GLSymplectic

universe u

noncomputable section

variable {l : Type*} [DecidableEq l] [Fintype l]
variable {R : Type u} [CommRing R]

private theorem matrix_mul_eq_zero_of_entries_mem
    (I : Ideal R) (hI : I ^ 2 = (⊥ : Ideal R)) {n : Type*} [Fintype n]
    (A B : Matrix n n R) (hA : forall i j, A i j ∈ I) (hB : forall i j, B i j ∈ I) :
    A * B = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [← Ideal.mem_bot]
  exact hI ▸ (by simpa only [pow_two] using Ideal.mul_mem_mul (hA i k) (hB k j))

/-- The strict upper-triangular part of a matrix. -/
private def upperPart {n : Type*} [LinearOrder n] (A : Matrix n n R) : Matrix n n R :=
  fun i j => if i < j then A i j else 0

private theorem upperPart_sub_transpose_eq {n : Type*} [LinearOrder n]
    (A : Matrix n n R) (hdiag : forall i, A i i = 0) (htranspose : A.transpose = -A) :
    upperPart A - (upperPart A).transpose = A := by
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [upperPart, hij, hij.not_gt]
  · simp [upperPart, hdiag]
  · have hskew : -(A j i) = A i j := by
      have := congrFun (congrFun htranspose j) i
      simpa using this.symm
    simp [upperPart, hji, hji.not_gt, hskew]

private theorem isAlt_toBilin'_J :
    (Matrix.toBilin' (Matrix.J l R)).IsAlt := by
  intro v
  simp [Matrix.toBilin'_apply', Matrix.J, Matrix.fromBlocks_mulVec, dotProduct, mul_comm,
    Matrix.neg_mulVec]

private theorem mul_J_mul_transpose_sub_J_diagonal
    (M : Matrix (l ⊕ l) (l ⊕ l) R) (i : l ⊕ l) :
    (M * Matrix.J l R * M.transpose - Matrix.J l R) i i = 0 := by
  let B := Matrix.toBilin' (Matrix.J l R)
  have hcomp :
      Matrix.toBilin' (M * Matrix.J l R * M.transpose) =
        B.comp M.transpose.mulVecLin M.transpose.mulVecLin := by
    simpa only [B, Matrix.toLin'_apply', Matrix.transpose_transpose] using
      (Matrix.toBilin'_comp (Matrix.J l R) M.transpose M.transpose).symm
  have hAltComp :
      (Matrix.toBilin' (M * Matrix.J l R * M.transpose)).IsAlt := by
    rw [hcomp]
    intro v
    exact isAlt_toBilin'_J (M.transpose.mulVecLin v)
  have hAlt :
      (Matrix.toBilin' (M * Matrix.J l R * M.transpose - Matrix.J l R)).IsAlt := by
    rw [map_sub]
    exact hAltComp.sub isAlt_toBilin'_J
  have hi := hAlt (Pi.single i 1)
  simpa only [Matrix.toBilin'_single] using hi

/-- Every symplectic matrix modulo a square-zero ideal lifts to a symplectic matrix.

The result is valid over an arbitrary commutative ring, in every characteristic, and for the
zero-dimensional symplectic group. -/
theorem map_quotient_mk_surjective_of_sq_eq_bot
    (I : Ideal R) (hI : I ^ 2 = (⊥ : Ideal R)) :
    Function.Surjective (GLSymplectic.map l (Ideal.Quotient.mk I)) := by
  classical
  let _ : LinearOrder (l ⊕ l) := (Fintype.equivFin (l ⊕ l)).linearOrder
  intro g
  choose m hm using fun i j => Ideal.Quotient.mk_surjective
    (((g : GL (l ⊕ l) (R ⧸ I)) : Matrix (l ⊕ l) (l ⊕ l) (R ⧸ I)) i j)
  let M : Matrix (l ⊕ l) (l ⊕ l) R := m
  let J : Matrix (l ⊕ l) (l ⊕ l) R := Matrix.J l R
  let E : Matrix (l ⊕ l) (l ⊕ l) R := M * J * M.transpose - J
  let qMat : Matrix (l ⊕ l) (l ⊕ l) R →+*
      Matrix (l ⊕ l) (l ⊕ l) (R ⧸ I) :=
    RingHom.mapMatrix (Ideal.Quotient.mk I)
  have hM_map : qMat M =
      ((g : GL (l ⊕ l) (R ⧸ I)) : Matrix (l ⊕ l) (l ⊕ l) (R ⧸ I)) := by
    ext i j
    simpa only [qMat, RingHom.mapMatrix_apply, Matrix.map_apply] using hm i j
  have hJ_map : qMat J = Matrix.J l (R ⧸ I) := by
    simpa only [qMat, RingHom.mapMatrix_apply, J] using
      Matrix.map_J (l := l) (Ideal.Quotient.mk I)
  have hM_transpose_map : qMat M.transpose = (qMat M).transpose := by
    simpa only [qMat, RingHom.mapMatrix_apply] using
      (Matrix.transpose_map (f := Ideal.Quotient.mk I) (M := M))
  have hE_map : qMat E = 0 := by
    dsimp only [E]
    rw [map_sub, map_mul, map_mul, hM_transpose_map, hM_map, hJ_map]
    rw [(GLSymplectic.mem_iff).mp g.2]
    exact sub_self _
  have hE_mem : forall i j, E i j ∈ I := by
    intro i j
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa only [qMat, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply] using
      congrFun (congrFun hE_map i) j
  have hE_transpose : E.transpose = -E := by
    dsimp only [E]
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.J_transpose]
    noncomm_ring
  have hE_diag : forall i, E i i = 0 := by
    intro i
    exact mul_J_mul_transpose_sub_J_diagonal M i
  let Y : Matrix (l ⊕ l) (l ⊕ l) R := upperPart (-E)
  have hY_mem : forall i j, Y i j ∈ I := by
    intro i j
    by_cases hij : i < j
    · simp only [Y, upperPart, hij, ite_true, Matrix.neg_apply]
      exact I.neg_mem (hE_mem i j)
    · simp only [Y, upperPart, hij, ite_false]
      exact I.zero_mem
  have hY_sub : Y - Y.transpose = -E := by
    apply upperPart_sub_transpose_eq
    · intro i
      simp [hE_diag]
    · rw [Matrix.transpose_neg, hE_transpose]
  let X : Matrix (l ⊕ l) (l ⊕ l) R := -(Y * J)
  have hX_mem : forall i j, X i j ∈ I := by
    intro i j
    simp only [X, Matrix.neg_apply]
    apply I.neg_mem
    apply I.sum_mem
    intro k _
    exact I.mul_mem_right _ (hY_mem i k)
  have hXt_mem : forall i j, X.transpose i j ∈ I := by
    intro i j
    exact hX_mem j i
  have hX_mul_J : X * J = Y := by
    dsimp only [X]
    rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.J_squared]
    simp
  have hJ_mul_Xt : J * X.transpose = -Y.transpose := by
    dsimp only [J]
    have hXt : X.transpose = J * Y.transpose := by
      dsimp only [X]
      rw [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.J_transpose]
      simp only [J]
      simp
    rw [hXt, ← Matrix.mul_assoc, Matrix.J_squared]
    simp
  have hX_mul_E : X * E = 0 :=
    matrix_mul_eq_zero_of_entries_mem I hI X E hX_mem hE_mem
  have hE_mul_Xt : E * X.transpose = 0 :=
    matrix_mul_eq_zero_of_entries_mem I hI E X.transpose hE_mem hXt_mem
  have hY_mul_Xt : Y * X.transpose = 0 :=
    matrix_mul_eq_zero_of_entries_mem I hI Y X.transpose hY_mem hXt_mem
  let N : Matrix (l ⊕ l) (l ⊕ l) R := (1 + X) * M
  have hM_form : M * J * M.transpose = J + E := by
    dsimp only [E]
    abel
  have hN_mem : N ∈ Matrix.symplecticGroup l R := by
    rw [SymplecticGroup.mem_iff]
    dsimp only [N]
    calc
      (1 + X) * M * J * ((1 + X) * M).transpose =
          (1 + X) * (M * J * M.transpose) * (1 + X.transpose) := by
            rw [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_one]
            noncomm_ring
      _ = (1 + X) * (J + E) * (1 + X.transpose) := by rw [hM_form]
      _ =
          J + E + X * J + X * E + J * X.transpose + E * X.transpose +
            (X * J) * X.transpose + (X * E) * X.transpose := by noncomm_ring
      _ = J := by
        rw [hX_mul_E, hE_mul_Xt, hX_mul_J, hJ_mul_Xt, hY_mul_Xt, zero_mul]
        have hlinear : E + Y - Y.transpose = 0 := by
          calc
            E + Y - Y.transpose = E + (Y - Y.transpose) := by abel
            _ = E + -E := by rw [hY_sub]
            _ = 0 := add_neg_cancel E
        calc
          J + E + Y + 0 + -Y.transpose + 0 + 0 + 0 =
              J + (E + Y - Y.transpose) := by abel
          _ = J := by rw [hlinear]; simp
  let s : Matrix.symplecticGroup l R := ⟨N, hN_mem⟩
  let lift : GLSymplectic l R :=
    ⟨ofSymplecticGroup l R s, ofSymplecticGroup_mem l R s⟩
  have hX_map : qMat X = 0 := by
    ext a b
    dsimp only [qMat]
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hX_mem a b
  have hN_map : qMat N =
      ((g : GL (l ⊕ l) (R ⧸ I)) : Matrix (l ⊕ l) (l ⊕ l) (R ⧸ I)) := by
    dsimp only [N]
    rw [map_mul, map_add, map_one, hX_map, add_zero, one_mul, hM_map]
  refine ⟨lift, ?_⟩
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hij := congrFun (congrFun hN_map i) j
  simpa only [coe_map, Matrix.GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, lift, coe_ofSymplecticGroup, s, qMat] using hij

end

end TauCeti.GLSymplectic
