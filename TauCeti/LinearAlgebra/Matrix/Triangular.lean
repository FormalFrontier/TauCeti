/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Diagonal entries of triangular matrices

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
