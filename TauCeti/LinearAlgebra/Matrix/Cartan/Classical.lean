/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Triangular
public import TauCeti.LinearAlgebra.RootSystem.Chain

/-!
# The determinants of the classical Cartan matrices of types `A`, `B` and `C`

Mathlib computes the determinant of `CartanMatrix.E n`, and hence of the three exceptional
matrices `E₆`, `E₇` and `E₈`, and evaluates `F₄` and `G₂` directly, but leaves the classical
families untouched. This file computes

```text
(CartanMatrix.A n).det = n + 1,   (CartanMatrix.B n).det = 2,   (CartanMatrix.C n).det = 2,
```

the last two for `0 < n`. The remaining classical family is type `D`, whose determinant is
`CartanMatrix.D_det` in
`TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots`, where it is read off the
checkerboard lattice.

No recursion in the rank is needed for any of the three. Weighting row `k` by `k + 1` and summing
over `k ≤ i` turns `CartanMatrix.A n` into an upper triangular matrix whose `i`-th diagonal entry
is `i + 2`, while the weights themselves assemble into a lower triangular matrix whose `i`-th
diagonal entry is `i + 1`. Comparing the two triangular determinants across that product gives
`n ! * det = (n + 1)!`, and `n !` cancels.

The same weights triangularize `CartanMatrix.B n`, which differs from `CartanMatrix.A n` in the
single entry carrying the double bond at the end of the diagram. That entry contributes only to
the last column, where it cuts the final diagonal entry `n + 1` down to `2`, so the weighted
determinant is `2 * n !` instead of `(n + 1)!`. Type `C` is the transpose of type `B`.

## Main declarations

* `CartanMatrix.A_det`: the determinant of `CartanMatrix.A n` is `n + 1`.
* `CartanMatrix.B_det` and `CartanMatrix.C_det`: the determinants of `CartanMatrix.B n` and
  `CartanMatrix.C n` are `2`.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters IV--VI, Plates I--III.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §13.
-/

public section

namespace CartanMatrix

open Finset TauCeti

/-! ## Weighted row combinations -/

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

/-! ## Type `A` -/

/-- **The determinant of the type `A` Cartan matrix of rank `n` is `n + 1`.** -/
@[simp]
theorem A_det (n : ℕ) : (A n).det = (n : ℤ) + 1 := by
  have hmul := congrArg Matrix.det (rowWeightMatrix_mul_cartanMatrixA n)
  rw [Matrix.det_mul, det_rowWeightMatrix, det_weightedRowMatrix, prod_range_add_two] at hmul
  exact mul_left_cancel₀ (prod_range_add_one_ne_zero n) (by linarith [hmul])

/-! ## Types `B` and `C` -/

/-- The double bond at the end of the type `B` diagram, as the difference between the type `B` and
the type `A` Cartan matrices of the same rank. -/
private def lastArrowMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j ↦ if i.val + 1 = j.val ∧ j.val + 1 = n then -1 else 0

private theorem cartanMatrixB_eq_add (n : ℕ) : B n = A n + lastArrowMatrix n := by
  ext i j
  have hj : j.val < n := j.isLt
  simp only [B, A, lastArrowMatrix, Matrix.of_apply, Matrix.add_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- The upper triangular matrix that the same weighted row combinations produce from the type `B`
Cartan matrix: the double bond cuts the last diagonal entry down to `2`. -/
private def weightedRowMatrixB (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j ↦
    if j.val = i.val then (if i.val + 1 = n then 2 else (i.val : ℤ) + 2)
    else if j.val = i.val + 1 then
      (if j.val + 1 = n then -2 * ((i.val : ℤ) + 1) else -((i.val : ℤ) + 1))
    else 0

private theorem rowWeightMatrix_mul_lastArrowMatrix {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) :
    (rowWeightMatrix n * lastArrowMatrix n) i j =
      if j.val + 1 = n ∧ j.val ≤ i.val + 1 then -(j.val : ℤ) else 0 := by
  classical
  rw [Matrix.mul_apply]
  by_cases hj : j.val + 1 = n
  · have hjpos : 0 < j.val := by omega
    have hmem : j.val - 1 < n := by omega
    have hval : ((⟨j.val - 1, hmem⟩ : Fin n) : ℕ) = j.val - 1 := rfl
    rw [Finset.sum_eq_single (⟨j.val - 1, hmem⟩ : Fin n)]
    · have hentry : lastArrowMatrix n (⟨j.val - 1, hmem⟩ : Fin n) j = -1 := by
        simp only [lastArrowMatrix, Matrix.of_apply]
        split_ifs
        · rfl
        · omega
      have hweight : rowWeightMatrix n i (⟨j.val - 1, hmem⟩ : Fin n) =
          if j.val ≤ i.val + 1 then (j.val : ℤ) else 0 := by
        simp only [rowWeightMatrix, Matrix.of_apply]
        split_ifs <;> omega
      rw [hentry, hweight]
      simp only [hj, true_and]
      split_ifs <;> ring
    · intro k _ hk
      have hkne : ¬ (k.val + 1 = j.val ∧ j.val + 1 = n) := by
        rintro ⟨h, -⟩
        exact hk (Fin.ext (by omega))
      simp only [lastArrowMatrix, Matrix.of_apply, ite_eq_right hkne, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [ite_eq_right (by tauto)]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    simp only [lastArrowMatrix, Matrix.of_apply, ite_eq_right (by tauto : ¬ (k.val + 1 = j.val ∧
      j.val + 1 = n)), mul_zero]

private theorem rowWeightMatrix_mul_cartanMatrixB {n : ℕ} (hn : 2 ≤ n) :
    rowWeightMatrix n * B n = weightedRowMatrixB n := by
  rw [cartanMatrixB_eq_add, Matrix.mul_add, rowWeightMatrix_mul_cartanMatrixA]
  ext i j
  have hj : j.val < n := j.isLt
  rw [Matrix.add_apply, rowWeightMatrix_mul_lastArrowMatrix hn]
  simp only [weightedRowMatrix, weightedRowMatrixB, Matrix.of_apply]
  split_ifs <;> push_cast <;> omega

private theorem det_weightedRowMatrixB {n : ℕ} (hn : 2 ≤ n) :
    (weightedRowMatrixB n).det = 2 * ∏ i ∈ range n, ((i : ℤ) + 1) := by
  classical
  have htri : (weightedRowMatrixB n).IsUpperTriangular := by
    intro i j hij
    have hlt : j.val < i.val := Fin.lt_def.mp hij
    have h1 : ¬ (j.val = i.val) := by omega
    have h2 : ¬ (j.val = i.val + 1) := by omega
    simp only [weightedRowMatrixB, Matrix.of_apply, h1, h2, ite_false]
  have hdiag : (∏ i : Fin n, weightedRowMatrixB n i i) =
      ∏ k ∈ range n, (if k + 1 = n then (2 : ℤ) else (k : ℤ) + 2) := by
    rw [← Fin.prod_univ_eq_prod_range (fun k ↦ if k + 1 = n then (2 : ℤ) else (k : ℤ) + 2) n]
    exact Finset.prod_congr rfl fun i _ ↦ by simp [weightedRowMatrixB]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hlast : (∏ k ∈ range (m + 1), (if k + 1 = m + 1 then (2 : ℤ) else (k : ℤ) + 2)) =
      (∏ k ∈ range m, ((k : ℤ) + 2)) * 2 := by
    rw [Finset.prod_range_succ, ite_eq_left rfl]
    refine congrArg (· * (2 : ℤ)) (Finset.prod_congr rfl fun k hk ↦ ?_)
    rw [Finset.mem_range] at hk
    exact ite_eq_right (by omega)
  have hshift : (∏ k ∈ range m, ((k : ℤ) + 2)) = ∏ k ∈ range (m + 1), ((k : ℤ) + 1) := by
    rw [Finset.prod_range_succ' (fun k ↦ ((k : ℤ) + 1)) m, Nat.cast_zero, zero_add, mul_one]
    exact Finset.prod_congr rfl fun k _ ↦ by push_cast; ring
  rw [Matrix.det_of_isUpperTriangular htri, hdiag, hlast, hshift]
  ring

/-- **The determinant of the type `B` Cartan matrix of rank `n` is `2`.** The double bond at the
end of the diagram cuts the last weighted diagonal entry down from `n + 1` to `2`. -/
theorem B_det {n : ℕ} (hn : 0 < n) : (B n).det = 2 := by
  rcases Nat.lt_or_ge n 2 with h1 | hn2
  · have hn1 : n = 1 := by omega
    subst hn1
    rw [Matrix.det_fin_one]
    simp [B]
  · have hmul := congrArg Matrix.det (rowWeightMatrix_mul_cartanMatrixB hn2)
    rw [Matrix.det_mul, det_rowWeightMatrix, det_weightedRowMatrixB hn2] at hmul
    exact mul_left_cancel₀ (prod_range_add_one_ne_zero n) (by linarith [hmul])

/-- **The determinant of the type `C` Cartan matrix of rank `n` is `2`.** It is the transpose of
the type `B` Cartan matrix of the same rank. -/
theorem C_det {n : ℕ} (hn : 0 < n) : (C n).det = 2 := by
  rw [← B_transpose, Matrix.det_transpose]
  exact B_det hn

end CartanMatrix
