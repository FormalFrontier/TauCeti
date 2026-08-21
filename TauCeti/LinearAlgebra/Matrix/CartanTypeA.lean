/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Triangular
public import TauCeti.LinearAlgebra.RootSystem.Chain

/-!
# Row combinations and the determinant of the type `A` Cartan matrix

Mathlib's `CartanMatrix.A n` is the tridiagonal matrix carrying `2` on the diagonal and `-1` on the
two neighbouring diagonals. Using its identification with `TauCeti.chainEntry`, this file computes

```text
(CartanMatrix.A n).det = n + 1.
```

No two-step recursion is needed. Weighting row `k` by `k + 1` and summing over `k ≤ i` turns
`CartanMatrix.A n` into an upper triangular matrix whose `i`-th diagonal entry is `i + 2`, while
the weights themselves assemble into a lower triangular matrix whose `i`-th diagonal entry is
`i + 1`. Comparing the two triangular determinants across that product gives
`n ! * det = (n + 1)!`, and `n !` cancels.

## Main declarations

* `CartanMatrix.A_det`: the determinant of `CartanMatrix.A n` is `n + 1`.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters IV--VI, Plate I.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §13.
-/

public section

namespace CartanMatrix

open Finset TauCeti

/-! ## The determinant -/

/-- The lower triangular matrix of row weights: row `i` collects the weight `k + 1` on every
row index `k ≤ i` of the type `A` Cartan matrix. -/
private def rowWeightMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j ↦ if j.val ≤ i.val then (j.val : ℤ) + 1 else 0

/-- The upper triangular matrix that the weighted row combinations produce. -/
private def weightedRowMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j ↦
    if j.val = i.val then (i.val : ℤ) + 2
    else if j.val = i.val + 1 then -((i.val : ℤ) + 1) else 0

private theorem rowWeightMatrix_mul_cartanMatrixA (n : ℕ) :
    rowWeightMatrix n * CartanMatrix.A n = weightedRowMatrix n := by
  classical
  ext i j
  have hsum : (rowWeightMatrix n * CartanMatrix.A n) i j =
      ∑ k ∈ range n, chainEntry j.val k * (if k ≤ i.val then (k : ℤ) + 1 else 0) := by
    rw [Matrix.mul_apply, ← Fin.sum_univ_eq_sum_range
      (fun k ↦ chainEntry j.val k * (if k ≤ i.val then (k : ℤ) + 1 else 0)) n]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← chainEntry_eq_cartanMatrix_A, chainEntry_comm]
    simp only [rowWeightMatrix, Matrix.of_apply]
    ring
  have hrow := sum_range_chainEntry_mul (R := ℤ) j.isLt
    (fun u ↦ if u - 1 ≤ i.val then ((u - 1 : ℕ) : ℤ) + 1 else 0)
  simp only [Int.cast_id, Nat.add_sub_cancel] at hrow
  rw [hsum, hrow]
  simp only [weightedRowMatrix, Matrix.of_apply]
  have hj : j.val < n := j.isLt
  split_ifs <;> push_cast <;> omega

private theorem det_rowWeightMatrix (n : ℕ) :
    (rowWeightMatrix n).det = ∏ i ∈ range n, ((i : ℤ) + 1) := by
  classical
  have htri : (rowWeightMatrix n).IsLowerTriangular := by
    intro i j hij
    have hnot : ¬ (j.val ≤ i.val) := by
      have : i.val < j.val := Fin.lt_def.mp hij
      omega
    simp only [rowWeightMatrix, Matrix.of_apply, hnot, ite_false]
  have hdiag : (∏ i : Fin n, rowWeightMatrix n i i) = ∏ i : Fin n, ((i.val : ℤ) + 1) :=
    Finset.prod_congr rfl fun i _ ↦ by simp [rowWeightMatrix]
  rw [Matrix.det_of_isLowerTriangular _ htri, hdiag]
  exact Fin.prod_univ_eq_prod_range (fun i ↦ ((i : ℤ) + 1)) n

private theorem det_weightedRowMatrix (n : ℕ) :
    (weightedRowMatrix n).det = ∏ i ∈ range n, ((i : ℤ) + 2) := by
  classical
  have htri : (weightedRowMatrix n).IsUpperTriangular := by
    intro i j hij
    have hlt : j.val < i.val := Fin.lt_def.mp hij
    have h1 : ¬ (j.val = i.val) := by omega
    have h2 : ¬ (j.val = i.val + 1) := by omega
    simp only [weightedRowMatrix, Matrix.of_apply, h1, h2, ite_false]
  have hdiag : (∏ i : Fin n, weightedRowMatrix n i i) = ∏ i : Fin n, ((i.val : ℤ) + 2) :=
    Finset.prod_congr rfl fun i _ ↦ by simp [weightedRowMatrix]
  rw [Matrix.det_of_isUpperTriangular htri, hdiag]
  exact Fin.prod_univ_eq_prod_range (fun i ↦ ((i : ℤ) + 2)) n

private theorem prod_range_add_two (m : ℕ) :
    (∏ i ∈ range m, ((i : ℤ) + 2)) = ((m : ℤ) + 1) * ∏ i ∈ range m, ((i : ℤ) + 1) := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ih]
      push_cast
      ring

private theorem prod_range_add_one_ne_zero (m : ℕ) :
    (∏ i ∈ range m, ((i : ℤ) + 1)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun i _ ↦ ?_
  positivity

/-- **The determinant of the type `A` Cartan matrix of rank `n` is `n + 1`.** -/
@[simp]
theorem A_det (n : ℕ) : (A n).det = (n : ℤ) + 1 := by
  have hmul := congrArg Matrix.det (rowWeightMatrix_mul_cartanMatrixA n)
  rw [Matrix.det_mul, det_rowWeightMatrix, det_weightedRowMatrix, prod_range_add_two] at hmul
  exact mul_left_cancel₀ (prod_range_add_one_ne_zero n) (by linarith [hmul])

end CartanMatrix
