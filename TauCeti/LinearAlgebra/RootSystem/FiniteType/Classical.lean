/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Fin.SuccPredOrder
public import Mathlib.Data.Rat.Star
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic

public section

/-!
# The classical Cartan matrices are of finite type

`TauCeti.IsFiniteType` asks of an integer matrix that it be a generalized Cartan matrix carrying a
positive rational symmetriser whose symmetrisation is positive definite. This file certifies the
four infinite families of the standard list, Mathlib's `CartanMatrix.A`, `CartanMatrix.B`,
`CartanMatrix.C` and `CartanMatrix.D`, uniformly in the rank and with no appeal to an already
constructed root system: only the matrices themselves are involved.

The proof is the Gram-matrix one. The symmetrisation `d i * A i j` of a Cartan matrix is the matrix
of inner products of the *simple coroots* `α_i^∨ = 2 α_i / (α_i, α_i)`, so it is positive definite
as soon as those vectors are linearly independent. Each family therefore gets an explicit rational
matrix whose rows are its simple coroots in the standard orthogonal coordinates, and two facts are
proved about it: that its Gram matrix is the symmetrisation, and that its rows are independent.
Positive definiteness is then Mathlib's `Matrix.PosDef.mul_conjTranspose_self`.

The coordinates are the classical ones, and the rows are listed in the Bourbaki order carried by
Mathlib's matrices, so that the last node is the one the `Bₙ`/`Cₙ` double edge ends at.

| type | simple coroots | ambient space |
| --- | --- | --- |
| `Aₙ` | `eᵢ - eᵢ₊₁` | `ℚ^{n+1}` |
| `Bₙ` | `eᵢ - eᵢ₊₁`, and `2 e_{n-1}` | `ℚ^n` |
| `Cₙ` | `eᵢ - eᵢ₊₁`, and `e_{n-1}` | `ℚ^n` |
| `Dₙ` | `eᵢ - eᵢ₊₁`, and `e_{n-2} + e_{n-1}` | `ℚ^n` |

Type `A` is the one family whose ambient space is larger than its rank. A square rational `M` with
`M Mᵀ = CartanMatrix.A n` would make the determinant of that matrix, which is `n + 1`, a rational
square, so no `n`-dimensional rational coordinate model exists whenever `n + 1` is not a square.
The sum-zero hyperplane of `ℚ^{n+1}` instead gives one uniform model for every `n`.

Independence of the rows is where the families part company, and it is why type `D` is handled
last. For `A`, `B` and `C` the matrix is triangular against an increasing choice of coordinates -
`TauCeti.vecMul_injective_of_isUpperTriangular_comp` - with a nonzero diagonal. No such choice
exists for `D`, whose two fork coordinates `e_{n-2}`, `e_{n-1}` support three rows between them, so
that family is treated in two steps: the sum of all coordinates annihilates every row but the fork
one, which pins the last coefficient to zero, and the rows that remain are the triangular chain
again.

## Main results

* `TauCeti.isFiniteType_cartanMatrix_A`, `TauCeti.isFiniteType_cartanMatrix_B`,
  `TauCeti.isFiniteType_cartanMatrix_C`, `TauCeti.isFiniteType_cartanMatrix_D`: the standard Cartan
  matrix of each classical family is of finite type, at every rank. No rank restriction is imposed:
  the low-rank coincidences `B 1 = C 1 = A 1`, `C 2 = B 2` and `D 3 = A 3` are finite-type matrices
  too, and it is `TauCeti.DynkinType.Valid`, not this file, that discards them.

Since `TauCeti.DynkinType.cartanMatrix` is Mathlib's matrix on each of these four constructors, a
consumer that needs the standard Cartan matrix of a classical Dynkin type to be nonsingular reaches
it through `TauCeti.DynkinType.cartanMatrix_A` and its siblings together with
`TauCeti.IsFiniteType.det_ne_zero`.

## Implementation notes

Every simple system above has each row supported on at most two coordinates, so all four are
instances of `TauCeti.twoTermRows`, and the Gram matrix of such a system is computed once and for
all in `TauCeti.twoTermRows_mul_conjTranspose_apply`. A row supported on a single coordinate is
written with a zero second coefficient rather than with a separate constructor, using the clamped
successor `Order.succ` for its second coordinate. `TauCeti.forkIndex` is the matching device for the
first coordinate of the type `D` fork row.

## References

This file supplies the classical half of the "finite-type condition" item of Layer 5 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. The coordinate models are the standard
ones of Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, plates I-IV, and of J. E. Humphreys,
*Introduction to Lie Algebras and Representation Theory*, section 12.1.
-/

open scoped Matrix

namespace TauCeti

variable {r c : ℕ}

/-! ### Simple systems supported on two coordinates -/

/-- The `r × c` rational matrix whose `i`-th row is `a i` in column `f i` plus `b i` in column
`g i`. Each classical simple system below is of this shape, a simple coroot being supported on at
most two of the standard coordinates. -/
@[expose] def twoTermRows (f g : Fin r → Fin c) (a b : Fin r → ℚ) : Matrix (Fin r) (Fin c) ℚ :=
  .of fun i j ↦ (if j = f i then a i else 0) + (if j = g i then b i else 0)

/-- The entries of a two-term system, in the shape the computations below consume. -/
@[simp]
lemma twoTermRows_apply (f g : Fin r → Fin c) (a b : Fin r → ℚ) (i : Fin r) (j : Fin c) :
    twoTermRows f g a b i j = (if j = f i then a i else 0) + (if j = g i then b i else 0) :=
  rfl

/-- **The Gram matrix of a two-term system.** The inner product of two rows is the sum of the four
products of coefficients whose columns agree. Nothing is assumed of `f` and `g`: a row supported on
a single column, written with `f i = g i` or with a vanishing coefficient, is covered as it
stands. -/
lemma twoTermRows_mul_conjTranspose_apply (f g : Fin r → Fin c) (a b : Fin r → ℚ) (i j : Fin r) :
    (twoTermRows f g a b * (twoTermRows f g a b)ᴴ) i j =
      ((if f i = f j then a i * a j else 0) + (if f i = g j then a i * b j else 0)) +
        ((if g i = f j then b i * a j else 0) + (if g i = g j then b i * b j else 0)) := by
  have key : ∀ k : Fin c,
      ((if k = f i then a i else 0) + (if k = g i then b i else 0)) *
          ((if k = f j then a j else 0) + (if k = g j then b j else 0)) =
        ((if k = f i then (if k = f j then a i * a j else 0) else 0) +
            (if k = f i then (if k = g j then a i * b j else 0) else 0)) +
          ((if k = g i then (if k = f j then b i * a j else 0) else 0) +
            (if k = g i then (if k = g j then b i * b j else 0) else 0)) := by
    intro k; split_ifs <;> ring
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, twoTermRows_apply, star_trivial, key]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Fintype.sum_ite_eq']

/-- **The coordinate sum of a row of a two-term system.** This is the linear functional that tells
the fork row of type `D` from the chain rows, all of which it kills. -/
lemma sum_twoTermRows_apply (f g : Fin r → Fin c) (a b : Fin r → ℚ) (i : Fin r) :
    ∑ j, twoTermRows f g a b i j = a i + b i := by
  simp only [twoTermRows_apply]
  rw [Finset.sum_add_distrib]
  simp only [Fintype.sum_ite_eq']

/-! ### Independence of the rows -/

/-- **A triangular selection of coordinates makes the rows independent.** If some choice `e` of a
coordinate for each row makes the matrix upper triangular - `M i (e j) = 0` for `j < i` - with a
nonzero diagonal, then the rows are independent: the selected columns form a square submatrix whose
determinant is the product of that diagonal. -/
theorem vecMul_injective_of_isUpperTriangular_comp {M : Matrix (Fin r) (Fin c) ℚ}
    (e : Fin r → Fin c) (hlt : ∀ i j, j < i → M i (e j) = 0) (hdiag : ∀ i, M i (e i) ≠ 0) :
    Function.Injective M.vecMul := by
  have hsub : Function.Injective (M.submatrix id e).vecMul := by
    refine Matrix.vecMul_injective_of_isUnit ?_
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
      Matrix.det_of_isUpperTriangular (M := M.submatrix id e) fun i j hji ↦ hlt i j hji]
    exact Finset.prod_ne_zero_iff.2 fun i _ ↦ hdiag i
  refine fun x y hxy ↦ hsub (funext fun j ↦ ?_)
  have hcol : ∀ z : Fin r → ℚ,
      (fun v ↦ v ᵥ* M.submatrix id e) z j = (fun v ↦ v ᵥ* M) z (e j) := by
    intro z; simp [Matrix.vecMul, dotProduct]
  rw [hcol x, hcol y]
  exact congrFun hxy (e j)

/-- The coordinate that the first term of a row of the type `Dₙ` system points at: `i` itself,
except at the last node, whose row is the fork one and starts two coordinates below the top. -/
def forkIndex {k : ℕ} (i : Fin (k + 2)) : Fin (k + 2) :=
  if i.val + 1 < k + 2 then i else (Fin.last k).castSucc

/-- The coordinate `TauCeti.forkIndex` selects, as a natural number. -/
lemma forkIndex_val {k : ℕ} (i : Fin (k + 2)) :
    (forkIndex i).val = if i.val + 1 < k + 2 then i.val else k := by
  unfold forkIndex; split_ifs <;> rfl

/-! ### Type `Aₙ` -/

/-- **The simple coroots of type `Aₙ`**: the `i`-th row is `eᵢ - eᵢ₊₁` in `ℚ^{n+1}`. -/
def simpleCorootsA (n : ℕ) : Matrix (Fin n) (Fin (n + 1)) ℚ :=
  twoTermRows Fin.castSucc Fin.succ (fun _ ↦ 1) (fun _ ↦ -1)

/-- The Gram matrix of the simple coroots of type `Aₙ` is the Cartan matrix itself: the family is
simply laced, so it is its own symmetrisation. -/
lemma simpleCorootsA_mul_conjTranspose (n : ℕ) :
    simpleCorootsA n * (simpleCorootsA n)ᴴ =
      Matrix.of fun i j ↦ (1 : ℚ) * ((CartanMatrix.A n i j : ℤ) : ℚ) := by
  ext i j
  rw [simpleCorootsA, twoTermRows_mul_conjTranspose_apply]
  simp only [Matrix.of_apply, CartanMatrix.A, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- The simple coroots of type `Aₙ` are independent: dropping the last coordinate leaves the
matrix upper triangular with unit diagonal. -/
lemma vecMul_injective_simpleCorootsA (n : ℕ) : Function.Injective (simpleCorootsA n).vecMul := by
  refine vecMul_injective_of_isUpperTriangular_comp Fin.castSucc (fun i j hji ↦ ?_) fun i ↦ ?_
  · have hji' : j.val < i.val := hji
    simp only [simpleCorootsA, twoTermRows_apply, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
    rw [if_neg (by omega), if_neg (by omega), add_zero]
  · simp [simpleCorootsA, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]

/-- **The Cartan matrix of type `Aₙ` is of finite type**, at every rank. -/
theorem isFiniteType_cartanMatrix_A (n : ℕ) : IsFiniteType (CartanMatrix.A n) := by
  refine isFiniteType_of (fun i ↦ by simp [CartanMatrix.A])
    (fun i j hij ↦ CartanMatrix.A_apply_le_zero_of_ne n i j hij) (d := fun _ ↦ 1)
    (fun _ ↦ one_pos) ?_
  rw [show (Matrix.of fun i j ↦ (1 : ℚ) * ((CartanMatrix.A n i j : ℤ) : ℚ)) =
      simpleCorootsA n * (simpleCorootsA n)ᴴ from (simpleCorootsA_mul_conjTranspose n).symm]
  exact Matrix.PosDef.mul_conjTranspose_self _ (vecMul_injective_simpleCorootsA n)

/-! ### Type `Bₙ` -/

/-- **The simple coroots of type `Bₙ`**: the `i`-th row is `eᵢ - eᵢ₊₁` in `ℚ^n`, except for the last
one, which is `2 e_{n-1}`, the coroot of the short simple root of the family. -/
def simpleCorootsB (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  twoTermRows id Order.succ (fun i ↦ if i.val + 1 < n then 1 else 2)
    (fun i ↦ if i.val + 1 < n then -1 else 0)

/-- The Gram matrix of the simple coroots of type `Bₙ` is the symmetrisation of the Cartan matrix
by `(1, …, 1, 2)`, the reciprocal squared root lengths of the family scaled to clear
denominators. -/
lemma simpleCorootsB_mul_conjTranspose (n : ℕ) :
    simpleCorootsB n * (simpleCorootsB n)ᴴ =
      Matrix.of fun i j ↦ (if i.val + 1 < n then 1 else 2) * ((CartanMatrix.B n i j : ℤ) : ℚ) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  have hsucc (a : Fin n) :
      (Order.succ a).val = if a.val + 1 < n then a.val + 1 else a.val := by
    cases n with
    | zero => exact Fin.elim0 a
    | succ n =>
      refine Fin.lastCases ?_ (fun j ↦ ?_) a <;> simp [Fin.orderSucc_apply]
  rw [simpleCorootsB, twoTermRows_mul_conjTranspose_apply]
  simp only [Matrix.of_apply, CartanMatrix.B, id_eq, Fin.ext_iff, hsucc]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- The simple coroots of type `Bₙ` are independent: the matrix is upper triangular, with
diagonal `(1, …, 1, 2)`. -/
lemma vecMul_injective_simpleCorootsB (n : ℕ) : Function.Injective (simpleCorootsB n).vecMul := by
  refine vecMul_injective_of_isUpperTriangular_comp id (fun i j hji ↦ ?_) fun i ↦ ?_
  · have hji' : j.val < i.val := hji
    have hle := Order.le_succ i
    simp only [simpleCorootsB, twoTermRows_apply, id_eq, Fin.ext_iff]
    rw [if_neg (by omega), if_neg (by omega), add_zero]
  · have hsucc :
        (Order.succ i).val = if i.val + 1 < n then i.val + 1 else i.val := by
      cases n with
      | zero => exact Fin.elim0 i
      | succ n =>
        refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [Fin.orderSucc_apply]
    simp only [simpleCorootsB, twoTermRows_apply, id_eq, Fin.ext_iff, hsucc]
    split_ifs <;> first | (exfalso; omega) | norm_num

/-- **The Cartan matrix of type `Bₙ` is of finite type**, at every rank. -/
theorem isFiniteType_cartanMatrix_B (n : ℕ) : IsFiniteType (CartanMatrix.B n) := by
  refine isFiniteType_of (fun i ↦ CartanMatrix.B_diag n i)
    (fun i j hij ↦ CartanMatrix.B_off_diag_nonpos n i j hij)
    (d := fun i ↦ if i.val + 1 < n then 1 else 2) (fun i ↦ by positivity) ?_
  rw [show (Matrix.of fun i j ↦ (if i.val + 1 < n then (1 : ℚ) else 2) *
      ((CartanMatrix.B n i j : ℤ) : ℚ)) = simpleCorootsB n * (simpleCorootsB n)ᴴ from
    (simpleCorootsB_mul_conjTranspose n).symm]
  exact Matrix.PosDef.mul_conjTranspose_self _ (vecMul_injective_simpleCorootsB n)

/-! ### Type `Cₙ` -/

/-- **The simple coroots of type `Cₙ`**: the `i`-th row is `eᵢ - eᵢ₊₁` in `ℚ^n`, except for the last
one, which is `e_{n-1}`, the coroot of the long simple root of the family. -/
def simpleCorootsC (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  twoTermRows id Order.succ (fun _ ↦ 1) (fun i ↦ if i.val + 1 < n then -1 else 0)

/-- The Gram matrix of the simple coroots of type `Cₙ` is the symmetrisation of the Cartan matrix
by `(1, …, 1, 1/2)`, the reciprocal squared root lengths of the family up to scale. Here a
denominator is unavoidable: the last node is the long one. -/
lemma simpleCorootsC_mul_conjTranspose (n : ℕ) :
    simpleCorootsC n * (simpleCorootsC n)ᴴ =
      Matrix.of fun i j ↦ (if i.val + 1 < n then 1 else 1 / 2) *
        ((CartanMatrix.C n i j : ℤ) : ℚ) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  have hsucc (a : Fin n) :
      (Order.succ a).val = if a.val + 1 < n then a.val + 1 else a.val := by
    cases n with
    | zero => exact Fin.elim0 a
    | succ n =>
      refine Fin.lastCases ?_ (fun j ↦ ?_) a <;> simp [Fin.orderSucc_apply]
  rw [simpleCorootsC, twoTermRows_mul_conjTranspose_apply]
  simp only [Matrix.of_apply, CartanMatrix.C, id_eq, Fin.ext_iff, hsucc]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- The simple coroots of type `Cₙ` are independent: the matrix is upper triangular, with unit
diagonal. -/
lemma vecMul_injective_simpleCorootsC (n : ℕ) : Function.Injective (simpleCorootsC n).vecMul := by
  refine vecMul_injective_of_isUpperTriangular_comp id (fun i j hji ↦ ?_) fun i ↦ ?_
  · have hji' : j.val < i.val := hji
    have hle := Order.le_succ i
    simp only [simpleCorootsC, twoTermRows_apply, id_eq, Fin.ext_iff]
    rw [if_neg (by omega), if_neg (by omega), add_zero]
  · have hsucc :
        (Order.succ i).val = if i.val + 1 < n then i.val + 1 else i.val := by
      cases n with
      | zero => exact Fin.elim0 i
      | succ n =>
        refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [Fin.orderSucc_apply]
    simp only [simpleCorootsC, twoTermRows_apply, id_eq, Fin.ext_iff, hsucc]
    split_ifs <;> first | (exfalso; omega) | norm_num

/-- **The Cartan matrix of type `Cₙ` is of finite type**, at every rank. -/
theorem isFiniteType_cartanMatrix_C (n : ℕ) : IsFiniteType (CartanMatrix.C n) := by
  refine isFiniteType_of (fun i ↦ CartanMatrix.C_diag n i)
    (fun i j hij ↦ CartanMatrix.C_off_diag_nonpos n i j hij)
    (d := fun i ↦ if i.val + 1 < n then 1 else 1 / 2) (fun i ↦ by positivity) ?_
  rw [show (Matrix.of fun i j ↦ (if i.val + 1 < n then (1 : ℚ) else 1 / 2) *
      ((CartanMatrix.C n i j : ℤ) : ℚ)) = simpleCorootsC n * (simpleCorootsC n)ᴴ from
    (simpleCorootsC_mul_conjTranspose n).symm]
  exact Matrix.PosDef.mul_conjTranspose_self _ (vecMul_injective_simpleCorootsC n)

/-! ### Type `Dₙ` -/

/-- **The simple coroots of type `Dₙ`**, for `n = k + 2`: the `i`-th row is `eᵢ - eᵢ₊₁` in `ℚ^n`,
except for the last one, which is `e_{n-2} + e_{n-1}`. The rank restriction `n ≥ 4` of the family
is not imposed: the model is still the right one at `D 3 = A 3`, and at `D 2`, whose two orthogonal
rows realize its two `A 1` components. -/
def simpleCorootsD (k : ℕ) : Matrix (Fin (k + 2)) (Fin (k + 2)) ℚ :=
  twoTermRows forkIndex Order.succ (fun _ ↦ 1) (fun i ↦ if i.val + 1 < k + 2 then -1 else 1)

/-- The Gram matrix of the simple coroots of type `Dₙ` is the Cartan matrix itself: the family is
simply laced, so it is its own symmetrisation. -/
lemma simpleCorootsD_mul_conjTranspose (k : ℕ) :
    simpleCorootsD k * (simpleCorootsD k)ᴴ =
      Matrix.of fun i j ↦ (1 : ℚ) * ((CartanMatrix.D (k + 2) i j : ℤ) : ℚ) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  have hsucc (a : Fin (k + 2)) :
      (Order.succ a).val = if a.val + 1 < k + 2 then a.val + 1 else a.val := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) a <;> simp [Fin.orderSucc_apply]; omega
  rw [simpleCorootsD, twoTermRows_mul_conjTranspose_apply]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Matrix.of_apply, CartanMatrix.D, Fin.ext_iff, forkIndex_val, hsucc,
      if_pos (show 0 + 2 ≤ 2 by omega)]
    split_ifs <;> first | (exfalso; omega) | norm_num
  · by_cases hin : i.val + 1 < k + 2 <;> by_cases hjn : j.val + 1 < k + 2 <;>
      simp only [Matrix.of_apply, CartanMatrix.D, hin, hjn, if_true, if_false, Fin.ext_iff,
        forkIndex_val, hsucc, if_neg (show ¬(k + 2 ≤ 2) by omega)] <;>
      split_ifs <;> first | (exfalso; omega) | norm_num

/-- **The simple coroots of type `Dₙ` are independent.** No coordinate makes the matrix
triangular, since the fork row shares both of its coordinates with earlier rows, so the argument
runs in two steps: the coordinate sum kills every chain row, so a relation has no fork term, and
the chain rows are then triangular on the coordinates below the top. -/
lemma vecMul_injective_simpleCorootsD (k : ℕ) : Function.Injective (simpleCorootsD k).vecMul := by
  refine (injective_iff_map_eq_zero (simpleCorootsD k).vecMulLinear.toAddMonoidHom).2 fun x hx ↦ ?_
  set M := simpleCorootsD k with hM
  have hx' : x ᵥ* M = 0 := by
    calc
      x ᵥ* M = M.vecMulLinear x := (Matrix.vecMulLinear_apply M x).symm
      _ = 0 := hx
  -- The coordinate sum annihilates every chain row and doubles the fork row.
  have hrow : ∀ i : Fin (k + 2), ∑ j, M i j = if i.val + 1 < k + 2 then 0 else 2 := by
    intro i
    rw [hM, simpleCorootsD, sum_twoTermRows_apply]
    by_cases h : i.val + 1 < k + 2 <;> norm_num [h]
  have hlast : x (Fin.last (k + 1)) = 0 := by
    have h0 : ∑ i, x i * ∑ j, M i j = 0 := by
      calc ∑ i, x i * ∑ j, M i j = ∑ i, ∑ j, x i * M i j := by simp [Finset.mul_sum]
        _ = ∑ j, ∑ i, x i * M i j := Finset.sum_comm
        _ = ∑ j, (x ᵥ* M) j := by simp [Matrix.vecMul, dotProduct]
        _ = 0 := by rw [hx']; simp
    rw [Fin.sum_univ_castSucc] at h0
    have hchain : ∀ i : Fin (k + 1), x i.castSucc * ∑ j, M i.castSucc j = 0 := by
      intro i
      have hi : (i.castSucc : Fin (k + 2)).val + 1 < k + 2 := by
        have := i.isLt; simp only [Fin.val_castSucc]; omega
      rw [hrow, if_pos hi, mul_zero]
    rw [Finset.sum_congr rfl fun i _ ↦ hchain i] at h0
    simp only [Finset.sum_const_zero, zero_add] at h0
    rw [hrow, if_neg (by simp only [Fin.val_last]; omega)] at h0
    linarith
  -- The chain rows are triangular on the first `k + 1` coordinates.
  have hblock : Function.Injective (M.submatrix Fin.castSucc Fin.castSucc).vecMul := by
    refine vecMul_injective_of_isUpperTriangular_comp id (fun i j hji ↦ ?_) fun i ↦ ?_
    · have hji' : j.val < i.val := hji
      have hci : ((i.castSucc : Fin (k + 2)) : ℕ) = (i : ℕ) := rfl
      have hcj : ((j.castSucc : Fin (k + 2)) : ℕ) = (j : ℕ) := rfl
      have hik := i.isLt
      have hjk := j.isLt
      simp only [Matrix.submatrix_apply, id_eq, hM, simpleCorootsD, twoTermRows_apply,
        Fin.ext_iff, forkIndex_val, Fin.orderSucc_castSucc, Fin.val_castSucc, Fin.val_succ]
      split_ifs <;> first | (exfalso; omega) | norm_num
    · have hci : ((i.castSucc : Fin (k + 2)) : ℕ) = (i : ℕ) := rfl
      have hik := i.isLt
      simp only [Matrix.submatrix_apply, id_eq, hM, simpleCorootsD, twoTermRows_apply,
        Fin.ext_iff, forkIndex_val, Fin.orderSucc_castSucc, Fin.val_castSucc, Fin.val_succ]
      split_ifs <;> first | (exfalso; omega) | norm_num
  have hrestrict : (fun i : Fin (k + 1) ↦ x i.castSucc) ᵥ*
      M.submatrix Fin.castSucc Fin.castSucc = 0 := by
    funext j
    have e1 : ((fun i : Fin (k + 1) ↦ x i.castSucc) ᵥ*
        M.submatrix Fin.castSucc Fin.castSucc) j =
        ∑ i : Fin (k + 1), x i.castSucc * M i.castSucc j.castSucc := by
      simp [Matrix.vecMul, dotProduct]
    have e2 : (x ᵥ* M) j.castSucc =
        ∑ i : Fin (k + 1), x i.castSucc * M i.castSucc j.castSucc +
          x (Fin.last (k + 1)) * M (Fin.last (k + 1)) j.castSucc := by
      rw [show (x ᵥ* M) j.castSucc = ∑ i, x i * M i j.castSucc by
        simp [Matrix.vecMul, dotProduct]]
      exact Fin.sum_univ_castSucc _
    have e3 : (x ᵥ* M) j.castSucc = 0 := by rw [hx']; simp
    rw [e3, hlast, zero_mul, add_zero] at e2
    rw [e1, ← e2]
    simp
  have hzero : (fun i : Fin (k + 1) ↦ x i.castSucc) = 0 := by
    refine hblock ?_
    have hzeroVecMul :
        (fun v ↦ v ᵥ* M.submatrix Fin.castSucc Fin.castSucc) (0 : Fin (k + 1) → ℚ) = 0 := by
      exact Matrix.zero_vecMul _
    exact hrestrict.trans hzeroVecMul.symm
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · exact hlast
  · exact congrFun hzero j

/-- **The Cartan matrix of type `Dₙ` is of finite type**, at every rank. The ranks `0` and `1`, at
which the family degenerates to the empty matrix and to `A 1`, are read off Mathlib's identities
rather than from the coordinate model, whose fork needs two coordinates. -/
theorem isFiniteType_cartanMatrix_D : ∀ n : ℕ, IsFiniteType (CartanMatrix.D n)
  | 0 => by
      rw [show CartanMatrix.D 0 = CartanMatrix.A 0 by ext i; exact i.elim0]
      exact isFiniteType_cartanMatrix_A 0
  | 1 => by rw [CartanMatrix.D_one]; exact isFiniteType_cartanMatrix_A 1
  | (k + 2) => by
      refine isFiniteType_of (fun i ↦ CartanMatrix.D_diag (k + 2) i)
        (fun i j hij ↦ CartanMatrix.D_off_diag_nonpos (k + 2) i j hij) (d := fun _ ↦ 1)
        (fun _ ↦ one_pos) ?_
      rw [show (Matrix.of fun i j ↦ (1 : ℚ) * ((CartanMatrix.D (k + 2) i j : ℤ) : ℚ)) =
          simpleCorootsD k * (simpleCorootsD k)ᴴ from (simpleCorootsD_mul_conjTranspose k).symm]
      exact Matrix.PosDef.mul_conjTranspose_self _ (vecMul_injective_simpleCorootsD k)

end TauCeti
