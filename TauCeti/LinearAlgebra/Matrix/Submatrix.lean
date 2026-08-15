/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `Matrix.submatrix` and `Matrix.submatrix_submatrix` occur in the statements and proofs below.
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Permutations preserving a square matrix

A permutation `σ` of the index set of a square matrix `M` *preserves* `M` when
`M.submatrix σ σ = M`. Such permutations form a subgroup of `Equiv.Perm`, and this file records the
three closure properties: `TauCeti.submatrix_perm_refl`, `TauCeti.submatrix_perm_trans` and
`TauCeti.submatrix_perm_symm`.

For the Cartan matrix of a Dynkin diagram these permutations are the diagram symmetries.
-/

public section

namespace TauCeti

variable {B α : Type*} {M : Matrix B B α} {σ τ : Equiv.Perm B}

/-- The identity permutation preserves every square matrix.

This is Mathlib's `Matrix.submatrix_id_id` with the reindexing spelled as `Equiv.refl` rather than
as `id`. The two are equal only by unfolding the coercion `⇑(Equiv.refl B) = id`, which `rw` and
`simp` do not do: a statement carrying `Matrix.submatrix_id_id` where a proof about
`⇑(Equiv.refl B)` is expected is not type-correct at their `implicit` transparency, so no such
statement can be rewritten with. -/
theorem submatrix_perm_refl (M : Matrix B B α) :
    M.submatrix (Equiv.refl B) (Equiv.refl B) = M := by
  rw [Equiv.coe_refl, Matrix.submatrix_id_id]

/-- If `σ` and `τ` preserve a square matrix then so does `σ.trans τ`. -/
theorem submatrix_perm_trans (hσ : M.submatrix σ σ = M) (hτ : M.submatrix τ τ = M) :
    M.submatrix (σ.trans τ) (σ.trans τ) = M := by
  rw [Equiv.coe_trans, ← Matrix.submatrix_submatrix, hτ, hσ]

/-- If `σ` preserves a square matrix then so does `σ.symm`. -/
theorem submatrix_perm_symm (hσ : M.submatrix σ σ = M) : M.submatrix σ.symm σ.symm = M :=
  calc M.submatrix ⇑σ.symm ⇑σ.symm
      = (M.submatrix ⇑σ ⇑σ).submatrix ⇑σ.symm ⇑σ.symm := by rw [hσ]
    _ = M := by rw [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]

end TauCeti
