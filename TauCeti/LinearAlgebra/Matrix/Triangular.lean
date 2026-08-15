/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Triangular matrices

Mathlib's `Matrix.BlockTriangular` API computes determinants and inverses of triangular
matrices, but not their individual diagonal entries. This file supplies the facts that
consumers keep needing: on the diagonal, a product of upper-triangular matrices multiplies
entrywise, because `∑ k, A i k * B k i` has a single surviving term — and consequences of
that, such as the diagonal of an inverse. It also defines upper-unitriangular matrices and proves
that strictly upper-triangular matrices are nilpotent.

The result previously lived in `TauCeti.Algebra.Lie.GeneralLinear.Borel`, phrased through
membership in the Borel subalgebra. It is a statement about matrices with no Lie theory in it,
so it is stated here for `Matrix.IsUpperTriangular` and consumed there; that also lets modules
which have no business importing Lie-algebra theory use it.

## Main results

* `Matrix.mul_apply_diag_of_isUpperTriangular` — the diagonal of a product of upper-triangular
  matrices is the pointwise product of the diagonals.
* `Matrix.inv_apply_diag_mul_of_isUpperTriangular` — on the diagonal, the inverse inverts
  entrywise: `M⁻¹ i i * M i i = 1`.
* `Matrix.inv_apply_diag_of_isUpperTriangular` — where an upper-triangular matrix carries a `1`
  on the diagonal, so does its inverse.
* `Matrix.IsUpperUnitriangular` — an upper-triangular matrix with diagonal one.
* `Matrix.IsUpperUnitriangular.ext` — upper-unitriangular matrices are determined by their
  entries strictly above the diagonal.
* `Matrix.IsUpperUnitriangular.det_eq_one` — an upper-unitriangular matrix has determinant one.
* `Matrix.isNilpotent_of_isUpperTriangular_of_diag_eq_zero` — strict upper triangularity implies
  nilpotence.
* `TauCeti.vecMul_injective_of_submatrix_isUpperTriangular` — a rectangular matrix has injective
  row multiplication when a square column selection is upper triangular with nonzero diagonal.
-/

public section

namespace Matrix

variable {R : Type*} {m : Type*}

/-- A square matrix is upper unitriangular when it is upper triangular and every diagonal entry
is one. -/
def IsUpperUnitriangular [LT m] [Zero R] [One R] (M : Matrix m m R) : Prop :=
  M.IsUpperTriangular ∧ ∀ i, M i i = 1

/-- Upper unitriangularity consists of upper triangularity and diagonal entries equal to one. -/
theorem isUpperUnitriangular_def [LT m] [Zero R] [One R] (M : Matrix m m R) :
    M.IsUpperUnitriangular ↔ M.IsUpperTriangular ∧ ∀ i, M i i = 1 :=
  Iff.rfl

/-- An upper-unitriangular matrix is upper triangular. -/
theorem IsUpperUnitriangular.isUpperTriangular [LT m] [Zero R] [One R]
    {M : Matrix m m R} (hM : M.IsUpperUnitriangular) : M.IsUpperTriangular :=
  (isUpperUnitriangular_def M).1 hM |>.1

/-- Every diagonal entry of an upper-unitriangular matrix is one. -/
theorem IsUpperUnitriangular.apply_diag [LT m] [Zero R] [One R]
    {M : Matrix m m R} (hM : M.IsUpperUnitriangular) (i : m) : M i i = 1 :=
  ((isUpperUnitriangular_def M).1 hM).2 i

/-- Two upper-unitriangular matrices are equal if their entries strictly above the diagonal
agree. -/
theorem IsUpperUnitriangular.ext [LinearOrder m] [Zero R] [One R] {M N : Matrix m m R}
    (hM : M.IsUpperUnitriangular) (hN : N.IsUpperUnitriangular)
    (h : ∀ i j, i < j → M i j = N i j) : M = N := by
  ext i j
  by_cases hij : i < j
  · exact h i j hij
  · obtain hji | rfl := lt_or_eq_of_le (le_of_not_gt hij)
    · exact (hM.isUpperTriangular hji).trans (hN.isUpperTriangular hji).symm
    · exact (hM.apply_diag _).trans (hN.apply_diag _).symm

/-- The determinant of an upper-unitriangular matrix is one. -/
theorem IsUpperUnitriangular.det_eq_one [Fintype m] [LinearOrder m] [CommRing R]
    {M : Matrix m m R} (hM : M.IsUpperUnitriangular) : M.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular hM.isUpperTriangular]
  exact Finset.prod_eq_one fun i _ ↦ hM.apply_diag i

/-- The determinant of an upper-unitriangular matrix is a unit. -/
theorem IsUpperUnitriangular.isUnit_det [Fintype m] [LinearOrder m] [CommRing R]
    {M : Matrix m m R} (hM : M.IsUpperUnitriangular) : IsUnit M.det := by
  rw [hM.det_eq_one]
  exact isUnit_one

/-- The identity matrix is upper unitriangular. -/
@[simp]
theorem isUpperUnitriangular_one [Preorder m] [DecidableEq m] [Zero R] [One R] :
    IsUpperUnitriangular (1 : Matrix m m R) := by
  refine ⟨blockTriangular_one, ?_⟩
  simp

/-- Applying a zero- and one-preserving map entrywise preserves upper-unitriangular matrices. -/
theorem IsUpperUnitriangular.map {S F : Type*} [LT m] [Zero R] [One R] [Zero S] [One S]
    [FunLike F R S] [ZeroHomClass F R S] [OneHomClass F R S] (f : F)
    {M : Matrix m m R} (hM : M.IsUpperUnitriangular) :
    (M.map f).IsUpperUnitriangular := by
  refine ⟨hM.1.map f, fun i ↦ ?_⟩
  simp [hM.2 i]

section Nilpotence

variable {S : Type*} [Semiring S] {n : ℕ}

/-- For a strictly upper-triangular matrix, `(M ^ k) i j = 0` whenever `j < i + k`. -/
theorem pow_apply_eq_zero_of_isUpperTriangular_of_diag_eq_zero
    {M : Matrix (Fin n) (Fin n) S} (htri : M.IsUpperTriangular)
    (hdiag : ∀ i, M i i = 0) (k : ℕ) (i j : Fin n)
    (hji : j.1 < i.1 + k) : (M ^ k) i j = 0 := by
  have hstrict : ∀ a b : Fin n, b ≤ a → M a b = 0 := by
    intro a b hba
    obtain hba | rfl := hba.lt_or_eq
    · exact htri hba
    · exact hdiag b
  induction k generalizing i j with
  | zero =>
      simp only [pow_zero]
      rw [one_apply_ne]
      intro hij
      subst j
      omega
  | succ k ih =>
      rw [pow_succ, mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hil : i.1 + k ≤ l.1
      · rw [hstrict l j (by omega), mul_zero]
      · rw [ih (i := i) (j := l) (by omega), zero_mul]

/-- A strictly upper-triangular matrix has power equal to zero at the cardinality of its index
type. -/
theorem pow_card_eq_zero_of_isUpperTriangular_of_diag_eq_zero [Fintype m] [LinearOrder m]
    {M : Matrix m m S} (htri : M.IsUpperTriangular) (hdiag : ∀ i, M i i = 0) :
    M ^ Fintype.card m = 0 := by
  let e : Fin (Fintype.card m) ≃o m := Fintype.orderIsoFinOfCardEq m rfl
  let reindexEquiv := Matrix.reindexRingEquiv S e.symm.toEquiv
  apply reindexEquiv.injective
  rw [map_pow, map_zero]
  apply Matrix.ext
  intro i j
  apply pow_apply_eq_zero_of_isUpperTriangular_of_diag_eq_zero
  · intro a b hba
    exact htri (e.lt_iff_lt.2 hba)
  · intro i
    exact hdiag (e i)
  · omega

/-- A strictly upper-triangular square matrix is nilpotent. -/
theorem isNilpotent_of_isUpperTriangular_of_diag_eq_zero [Fintype m] [LinearOrder m]
    {M : Matrix m m S} (htri : M.IsUpperTriangular) (hdiag : ∀ i, M i i = 0) :
    _root_.IsNilpotent M :=
  ⟨Fintype.card m, pow_card_eq_zero_of_isUpperTriangular_of_diag_eq_zero htri hdiag⟩

end Nilpotence

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

variable {S : Type*} [CommRing S] {M : Matrix n n S}

/-- On the diagonal, the inverse of an invertible upper-triangular matrix inverts entrywise:
`M⁻¹ i i * M i i = 1`. -/
theorem inv_apply_diag_mul_of_isUpperTriangular [Invertible M] (hM : M.IsUpperTriangular)
    (i : n) : M⁻¹ i i * M i i = 1 := by
  have hinv : M⁻¹.IsUpperTriangular := blockTriangular_inv_of_blockTriangular hM
  have h := congrFun (congrFun (nonsing_inv_mul M (isUnit_det_of_invertible M)) i) i
  rwa [mul_apply_diag_of_isUpperTriangular hinv hM i, one_apply_eq] at h

/-- Where an invertible upper-triangular matrix has a `1` on the diagonal, so does its inverse.
The hypothesis is needed only at the entry asked about. -/
theorem inv_apply_diag_of_isUpperTriangular [Invertible M] (hM : M.IsUpperTriangular) {i : n}
    (hdiag : M i i = 1) : M⁻¹ i i = 1 := by
  simpa [hdiag] using inv_apply_diag_mul_of_isUpperTriangular hM i

/-- A product of upper-unitriangular matrices is upper unitriangular. -/
theorem IsUpperUnitriangular.mul {T p : Type*} [NonAssocSemiring T] [Fintype p]
    [LinearOrder p] {M N : Matrix p p T} (hM : M.IsUpperUnitriangular)
    (hN : N.IsUpperUnitriangular) : (M * N).IsUpperUnitriangular := by
  refine ⟨hM.1.mul hN.1, fun i ↦ ?_⟩
  rw [mul_apply_diag_of_isUpperTriangular hM.1 hN.1, hM.2 i, hN.2 i, one_mul]

/-- The inverse of an invertible upper-unitriangular matrix is upper unitriangular. -/
theorem IsUpperUnitriangular.inv {T p : Type*} [CommRing T] [Fintype p] [LinearOrder p]
    {M : Matrix p p T} [Invertible M] (hM : M.IsUpperUnitriangular) :
    M⁻¹.IsUpperUnitriangular := by
  refine ⟨blockTriangular_inv_of_blockTriangular hM.1, fun i ↦ ?_⟩
  exact inv_apply_diag_of_isUpperTriangular hM.1 (hM.2 i)

/-- Subtracting the identity from an upper-unitriangular matrix gives a nilpotent matrix. -/
theorem IsUpperUnitriangular.isNilpotent_sub_one {T p : Type*} [Ring T] [Fintype p]
    [LinearOrder p] {M : Matrix p p T} (hM : M.IsUpperUnitriangular) :
    _root_.IsNilpotent (M - 1) := by
  apply isNilpotent_of_isUpperTriangular_of_diag_eq_zero
  · exact hM.1.sub blockTriangular_one
  · intro i
    simp [hM.2 i]

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
