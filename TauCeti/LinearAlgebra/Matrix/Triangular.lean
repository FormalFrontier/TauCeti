/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Triangular matrices

Mathlib's `Matrix.BlockTriangular` API computes determinants and inverses of triangular
matrices, but not their individual diagonal entries. This file supplies the one fact that
consumers keep needing: on the diagonal, a product of upper-triangular matrices multiplies
entrywise, because `∑ k, A i k * B k i` has a single surviving term.

The result previously lived in `TauCeti.Algebra.Lie.GeneralLinear.Borel`, phrased through
membership in the Borel subalgebra. It is a statement about matrices with no Lie theory in it,
so it is stated here for `Matrix.IsUpperTriangular` and consumed there; that also lets modules
which have no business importing Lie-algebra theory use it.

## Main results

* `Matrix.mul_apply_diag_of_isUpperTriangular` — the diagonal of a product of upper-triangular
  matrices is the pointwise product of the diagonals.
* `TauCeti.vecMul_injective_of_submatrix_isUpperTriangular` — a rectangular matrix has injective
  row multiplication when a square column selection is upper triangular with nonzero diagonal.
-/

public section

namespace Matrix

variable {R : Type*} [NonUnitalNonAssocSemiring R] {n : Type*} [Fintype n] [LinearOrder n]
  {A B : Matrix n n R}

/-- The diagonal of a product of upper-triangular matrices is the pointwise product of the
diagonals. -/
theorem mul_apply_diag_of_isUpperTriangular (hA : A.IsUpperTriangular)
    (hB : B.IsUpperTriangular) (i : n) : (A * B) i i = A i i * B i i := by
  -- the only surviving term of `∑ k, A i k * B k i` is the one with `k = i`
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · exact fun h ↦ absurd (Finset.mem_univ i) h

end Matrix

open scoped Matrix

namespace TauCeti

/-- **A triangular selection of coordinates makes the rows independent.** If some choice `e` of a
coordinate for each row makes the matrix upper triangular - `M i (e j) = 0` for `j < i` - with a
nonzero diagonal, then the rows are independent: the selected columns form a square submatrix whose
determinant is the product of that diagonal. -/
theorem vecMul_injective_of_submatrix_isUpperTriangular {K ι κ : Type*} [Field K]
    [Fintype ι] [LinearOrder ι] {M : Matrix ι κ K}
    (e : ι → κ) (hlt : ∀ i j, j < i → M i (e j) = 0) (hdiag : ∀ i, M i (e i) ≠ 0) :
    Function.Injective M.vecMul := by
  have hsub : Function.Injective (M.submatrix id e).vecMul := by
    refine Matrix.vecMul_injective_of_isUnit ?_
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
      Matrix.det_of_isUpperTriangular (M := M.submatrix id e) fun i j hji ↦ hlt i j hji]
    exact Finset.prod_ne_zero_iff.2 fun i _ ↦ hdiag i
  refine fun x y hxy ↦ hsub (funext fun j ↦ ?_)
  have hcol : ∀ z : ι → K,
      (fun v ↦ v ᵥ* M.submatrix id e) z j = (fun v ↦ v ᵥ* M) z (e j) := by
    intro z
    simp [Matrix.vecMul, dotProduct]
  rw [hcol x, hcol y]
  exact congrFun hxy (e j)

end TauCeti
