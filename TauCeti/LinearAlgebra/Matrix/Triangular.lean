/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block

public section

/-!
# Injectivity from a triangular submatrix

This file records an injectivity criterion for a rectangular matrix whose rows become an
upper-triangular square matrix after selecting suitable columns.

## Main results

* `TauCeti.vecMul_injective_of_isUpperTriangular_comp`: a rectangular matrix has injective row
  multiplication when a square column selection is upper triangular with nonzero diagonal.
-/

open scoped Matrix

namespace TauCeti

variable {r c : ℕ}

/-- **A triangular selection of coordinates makes the rows independent.** If some choice `e` of a
coordinate for each row makes the matrix upper triangular - `M i (e j) = 0` for `j < i` - with a
nonzero diagonal, then the rows are independent: the selected columns form a square submatrix whose
determinant is the product of that diagonal. -/
theorem vecMul_injective_of_isUpperTriangular_comp {K : Type*} [Field K]
    {M : Matrix (Fin r) (Fin c) K}
    (e : Fin r → Fin c) (hlt : ∀ i j, j < i → M i (e j) = 0) (hdiag : ∀ i, M i (e i) ≠ 0) :
    Function.Injective M.vecMul := by
  have hsub : Function.Injective (M.submatrix id e).vecMul := by
    refine Matrix.vecMul_injective_of_isUnit ?_
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
      Matrix.det_of_isUpperTriangular (M := M.submatrix id e) fun i j hji ↦ hlt i j hji]
    exact Finset.prod_ne_zero_iff.2 fun i _ ↦ hdiag i
  refine fun x y hxy ↦ hsub (funext fun j ↦ ?_)
  have hcol : ∀ z : Fin r → K,
      (fun v ↦ v ᵥ* M.submatrix id e) z j = (fun v ↦ v ᵥ* M) z (e j) := by
    intro z
    simp [Matrix.vecMul, dotProduct]
  rw [hcol x, hcol y]
  exact congrFun hxy (e j)

end TauCeti
