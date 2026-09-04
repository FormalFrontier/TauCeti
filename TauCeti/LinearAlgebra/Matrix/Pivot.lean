/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# A symmetric matrix pivot for Gaussian elimination

Let `A` and `C` be two square matrices over a field. If their kernels meet trivially and
`Aᵀ C = Cᵀ A`, then some symmetric matrix `X` makes `A + X C` invertible. Applied to the
left blocks of a symplectic matrix, this says that multiplication by an upper symplectic
unipotent can make the upper-left block invertible. This is the pivot step in the Gaussian
decomposition of the symplectic group.

## Main result

* `TauCeti.exists_isSymm_isUnit_add_mul_of_ker_inter_eq_bot_of_transpose_mul_comm` constructs the
  symmetric pivot.

## References

* J. Dieudonné, *La géométrie des groupes classiques*, Chapter II, §1.

The proof is adapted from Mathlib's private lemma
`Matrix.SymplecticGroup.exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot` in
`Mathlib.LinearAlgebra.SymplecticGroup` (Apache-2.0). It is made public here because symplectic
Gaussian generation needs the constructed symmetric pivot, while Mathlib uses it only internally
to prove that symplectic matrices have determinant one.
-/

public section

open Matrix

namespace TauCeti

universe u

/-- Given square matrices `A` and `C` over a field, if the only vector annihilated by both is
zero and `Aᵀ C = Cᵀ A`, then a symmetric left multiplier makes `A + X C` invertible. -/
theorem exists_isSymm_isUnit_add_mul_of_ker_inter_eq_bot_of_transpose_mul_comm
    {K : Type u} [Field K] {l : Type*} [Fintype l] [DecidableEq l]
    {A C : Matrix l l K}
    (hker : ∀ x : l → K, A • x = 0 → C • x = 0 → x = 0)
    (hcomm : Aᵀ * C = Cᵀ * A) :
    ∃ X : Matrix l l K, X.IsSymm ∧ IsUnit (A + X * C) := by
  -- Put `C` into rank normal form and transport `A` by the same basis changes.
  rcases Matrix.exists_rank_normal_form C with ⟨V, U, s, hV, hU, heq⟩
  set P := V * C * U with P_def
  set Q := Vᵀ⁻¹ * A * U with Q_def
  set f := fun x : Matrix l l K ↦ x.submatrix s.symm s.symm
  have hf (x : Matrix l l K) : f x = x.submatrix s.symm s.symm := rfl
  have f_unit {x : Matrix l l K} : IsUnit x → IsUnit (f x) :=
    (isUnit_submatrix_equiv ..).2
  have f_mul (x y : Matrix l l K) : f (x * y) = f x * f y :=
    submatrix_mul _ _ _ _ _ s.symm.bijective
  have _ : Invertible V := hV.invertible
  have _ : Invertible U := hU.invertible
  have _ : Invertible (f Vᵀ) := (f_unit (V.isUnit_transpose.2 hV)).invertible
  have con1 (x : Fin C.rank ⊕ Fin (Fintype.card l - C.rank) → K)
      (heq1 : f Q • x = 0) (heq2 : f P • x = 0) : x = 0 := by
    refine (f_unit hU).smul_left_cancel.1 ?_
    rw [f_mul, f_mul, mul_assoc, mul_smul, IsUnit.smul_eq_zero, mul_smul, hf,
      smul_eq_mulVec, submatrix_mulVec_equiv, Equiv.symm_symm] at heq1 heq2
    · rw [Equiv.comp_symm_eq, Pi.zero_comp] at heq1 heq2
      exact s.surjective.injective_comp_right <| by simpa using hker _ heq1 heq2
    · exact f_unit hV
    · exact f_unit <| isUnit_nonsing_inv_iff.2 <| V.isUnit_transpose.2 hV
  have con2 : Qᵀ * P = Pᵀ * Q := by
    simp only [P_def, mul_assoc, transpose_mul, transpose_nonsing_inv, transpose_transpose, Q_def,
      inv_mul_cancel_left_of_invertible, mul_inv_cancel_left_of_invertible]
    rw [← mul_assoc Aᵀ, hcomm, mul_assoc]
  -- The commutation equation makes the leading block of `Q` symmetric and its
  -- upper-right block zero in the decomposition selected by the rank of `C`.
  replace con2 : (f Q).toBlocks₁₁ᵀ = (f Q).toBlocks₁₁ ∧ (f Q).toBlocks₁₂ = 0 := by
    apply_fun reindex s s at con2
    rw [reindex_apply, reindex_apply, ← hf, ← hf, f_mul, f_mul Pᵀ, heq, hf,
      ← transpose_submatrix, ← hf Q, ← (f Q).fromBlocks_toBlocks, hf _ᵀ,
      hf ((fromBlocks 1 0 0 0).submatrix _ _)] at con2
    simp [fromBlocks_transpose, fromBlocks_multiply] at con2
    tauto
  have con3 : IsUnit (f Q).toBlocks₂₂ := by
    refine mulVec_injective_iff_isUnit.1 ?_
    rw [← coe_mulVecLin, ← LinearMap.ker_eq_bot]
    refine ker_mulVecLin_eq_bot_iff.2 fun x hx ↦ Sum.elim_injective' <|
      (con1 _ ?_ ?_).trans Sum.elim_zero_zero.symm
    · rw [← (f Q).fromBlocks_toBlocks]
      simp [hx, con2.2, fromBlocks_mulVec]
    · simp [hf, heq, fromBlocks_mulVec]
  set Y : Matrix (Fin C.rank ⊕ Fin (Fintype.card l - C.rank))
      (Fin C.rank ⊕ Fin (Fintype.card l - C.rank)) K :=
    fromBlocks (1 - (f Q).toBlocks₁₁) 0 0 0 with Y_def
  have hY : Y.IsSymm := by
    rw [Y_def, isSymm_fromBlocks_iff]
    exact ⟨IsSymm.sub isSymm_one con2.1, by simp⟩
  set X := f Vᵀ * Y * f V with X_def
  -- Conjugating the block correction `Y` back through `V` preserves symmetry;
  -- the corrected matrix is block triangular with invertible diagonal blocks.
  refine ⟨X.submatrix s s, IsSymm.submatrix ?_ s, (isUnit_submatrix_equiv s.symm s.symm).1 ?_⟩
  · simp_rw [X_def, Matrix.IsSymm, transpose_mul, hY.eq, hf, transpose_submatrix,
      transpose_transpose, mul_assoc]
  · have heq' : f (A + X.submatrix s s * C) =
        f Vᵀ * (f Q + Y * f P) * f U⁻¹ := by
      simp_rw [hf, submatrix_add, Pi.add_apply, Q_def, P_def, ← hf, f_mul, hf, mul_add,
        ← mul_assoc, ← inv_submatrix_equiv, add_mul, mul_assoc _ (U.submatrix _ _),
        mul_inv_of_invertible]
      simp [X_def]
      -- The remaining equality is definitional: `f` is the local abbreviation for
      -- submatrix reindexing, so both sides now apply the same reindexed matrices.
      rfl
    rw [← hf, heq', IsUnit.mul_iff, IsUnit.mul_iff]
    refine ⟨⟨isUnit_of_invertible _, ?_⟩, ?_⟩
    · nth_rw 1 [Y_def, heq, ← (f Q).fromBlocks_toBlocks, con2.2]
      simpa [hf, fromBlocks_multiply, fromBlocks_add]
    · exact f_unit <| isUnit_nonsing_inv_iff.2 hU

end TauCeti
