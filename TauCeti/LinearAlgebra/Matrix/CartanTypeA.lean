/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan
public import TauCeti.LinearAlgebra.Matrix.Triangular

/-!
# Row combinations and the determinant of the type `A` Cartan matrix

Mathlib's `CartanMatrix.A n` is the tridiagonal matrix carrying `2` on the diagonal and `-1` on the
two neighbouring diagonals. This file evaluates the combination `∑ j, CartanMatrix.A n i j * w j`
of its `i`-th row against an arbitrary weight vector, and uses the resulting formula to compute

```text
(CartanMatrix.A n).det = n + 1.
```

No two-step recursion is needed. Weighting row `k` by `k + 1` and summing over `k ≤ i` turns
`CartanMatrix.A n` into an upper triangular matrix whose `i`-th diagonal entry is `i + 2`, while
the weights themselves assemble into a lower triangular matrix whose `i`-th diagonal entry is
`i + 1`. Comparing the two triangular determinants across that product gives
`n ! * det = (n + 1)!`, and `n !` cancels.

## Main declarations

* `TauCeti.cartanTypeAEntry`: the entries of `CartanMatrix.A n` as a function of the underlying
  natural-number indices.
* `TauCeti.cartanTypeAEntry_eq`: those entries as a combination of three indicator functions.
* `TauCeti.sum_cartanTypeAEntry_mul`: the combination of a row against an arbitrary weight vector.
* `TauCeti.det_cartanMatrixA`: the determinant of `CartanMatrix.A n` is `n + 1`.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters IV--VI, Plate I.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §13.
-/

public section

namespace TauCeti

open Finset

/-- The entry of the type `A` Cartan matrix at a pair of natural-number indices: `2` on the
diagonal, `-1` at the two neighbours, and `0` elsewhere. -/
def cartanTypeAEntry (i j : ℕ) : ℤ :=
  if i = j then 2 else if i + 1 = j ∨ j + 1 = i then -1 else 0

/-- The type `A` Cartan matrix depends only on the natural numbers underlying its indices. -/
theorem cartanMatrixA_apply (n : ℕ) (i j : Fin n) :
    CartanMatrix.A n i j = cartanTypeAEntry i.val j.val := by
  simp only [CartanMatrix.A, Matrix.of_apply, cartanTypeAEntry, Fin.ext_iff]

/-- The diagonal entries of the type `A` Cartan matrix are `2`. -/
@[simp]
theorem cartanTypeAEntry_self (i : ℕ) : cartanTypeAEntry i i = 2 := by
  simp [cartanTypeAEntry]

/-- The entry function of the type `A` Cartan matrix, written as a combination of the three
indicator functions of its diagonal and its two neighbouring diagonals. -/
theorem cartanTypeAEntry_eq (i j : ℕ) :
    cartanTypeAEntry i j =
      2 * (if j = i then 1 else 0) - (if j = i + 1 then 1 else 0) -
        (if j + 1 = i then 1 else 0) := by
  simp only [cartanTypeAEntry]
  split_ifs <;> omega

/-- The natural-number entry function of the type `A` Cartan matrix is symmetric. -/
theorem cartanTypeAEntry_comm (i j : ℕ) : cartanTypeAEntry i j = cartanTypeAEntry j i := by
  simp only [cartanTypeAEntry]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- **A row of the type `A` Cartan matrix combined against a weight vector.** The two conditional
terms are the neighbours of `i` that stay inside the index range `range n`. -/
theorem sum_cartanTypeAEntry_mul {R : Type*} [Ring R] (n i : ℕ) (hin : i < n) (w : ℕ → R) :
    ∑ j ∈ range n, ((cartanTypeAEntry i j : ℤ) : R) * w j =
      2 * w i - (if i + 1 < n then w (i + 1) else 0) - (if 0 < i then w (i - 1) else 0) := by
  classical
  have hsplit : ∀ j ∈ range n, ((cartanTypeAEntry i j : ℤ) : R) * w j =
      (if j = i then 2 * w j else 0) + (if j = i + 1 then -w j else 0) +
        (if j + 1 = i then -w j else 0) := by
    intro j _
    rw [cartanTypeAEntry_eq]
    split_ifs <;> push_cast <;> simp [two_mul]
  have hlast : ∑ j ∈ range n, (if j + 1 = i then -w j else 0) =
      if 0 < i then -w (i - 1) else 0 := by
    obtain _ | k := i
    · simp
    · have hcond : ∀ j : ℕ, (j + 1 = k + 1) ↔ (j = k) := fun j ↦ by omega
      have hk : k < n := by omega
      rw [show (∑ j ∈ range n, if j + 1 = k + 1 then -w j else 0) =
          ∑ j ∈ range n, if j = k then -w j else 0 from
        Finset.sum_congr rfl fun j _ ↦ by simp only [hcond j],
        Finset.sum_ite_eq' (range n) k fun j ↦ -w j]
      simp [hk]
  rw [sum_congr rfl hsplit, sum_add_distrib, sum_add_distrib,
    Finset.sum_ite_eq' (range n) i fun j ↦ 2 * w j,
    Finset.sum_ite_eq' (range n) (i + 1) fun j ↦ -w j, hlast]
  simp only [mem_range]
  split_ifs <;> simp [two_mul] <;> abel

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
      ∑ k ∈ range n, cartanTypeAEntry j.val k * (if k ≤ i.val then (k : ℤ) + 1 else 0) := by
    rw [Matrix.mul_apply, ← Fin.sum_univ_eq_sum_range
      (fun k ↦ cartanTypeAEntry j.val k * (if k ≤ i.val then (k : ℤ) + 1 else 0)) n]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [cartanMatrixA_apply, cartanTypeAEntry_comm]
    simp only [rowWeightMatrix, Matrix.of_apply]
    ring
  have hrow := sum_cartanTypeAEntry_mul (R := ℤ) n j.val j.isLt
    (fun k ↦ if k ≤ i.val then (k : ℤ) + 1 else 0)
  simp only [Int.cast_id] at hrow
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
  rw [Matrix.det_of_isLowerTriangular _ htri,
    show (∏ i : Fin n, rowWeightMatrix n i i) = ∏ i : Fin n, ((i.val : ℤ) + 1) from
      Finset.prod_congr rfl fun i _ ↦ by simp [rowWeightMatrix]]
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
  rw [Matrix.det_of_isUpperTriangular htri,
    show (∏ i : Fin n, weightedRowMatrix n i i) = ∏ i : Fin n, ((i.val : ℤ) + 2) from
      Finset.prod_congr rfl fun i _ ↦ by simp [weightedRowMatrix]]
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
theorem det_cartanMatrixA (n : ℕ) : (CartanMatrix.A n).det = (n : ℤ) + 1 := by
  have hmul := congrArg Matrix.det (rowWeightMatrix_mul_cartanMatrixA n)
  rw [Matrix.det_mul, det_rowWeightMatrix, det_weightedRowMatrix, prod_range_add_two] at hmul
  exact mul_left_cancel₀ (prod_range_add_one_ne_zero n) (by linarith [hmul])

end TauCeti
