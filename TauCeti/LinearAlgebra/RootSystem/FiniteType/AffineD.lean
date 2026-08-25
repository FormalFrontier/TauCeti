/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic
public import TauCeti.LinearAlgebra.RootSystem.Chain

public section

/-!
# Affine type D̃ₘ for m ≥ 5 is not of finite type

The diagram of an indecomposable finite-type Cartan matrix is a tree of maximum degree three. To
finish the simply-laced part of the Cartan--Killing classification one must also show that such a
tree cannot have two branch vertices.  The path between two branch vertices, together with two
branches at either end, contains an affine diagram of type `D`.  This file supplies the uniform
matrix obstruction for that argument.

The matrix `doubleForkCartanMatrix n` has two fork vertices joined by a chain with `n` internal
vertices. Each fork vertex has two leaves. Thus it is the affine diagram `D̃ₘ` for
`m = n + 5`, so this construction covers exactly the family `D̃ₘ` for `m ≥ 5`. The vector which
is `1` on the four leaves and `2` on the middle chain is a nonzero null vector. Since a finite-type
matrix has positive-definite symmetrization, it cannot admit this vector.

The spine of the diagram is a chain, so its entries and the row sum along it come from
`TauCeti.LinearAlgebra.RootSystem.Chain`, which the star obstructions of
`TauCeti.LinearAlgebra.RootSystem.FiniteType.Star` share.

## Main definitions

* `TauCeti.DoubleForkIndex`: the four leaves and the vertices of the middle chain.
* `TauCeti.doubleForkCartanMatrix`: the simply-laced double-fork Cartan matrix.
* `TauCeti.doubleForkMark`: the affine marks, equal to `1` on leaves and `2` on the chain.

## Main results

* `TauCeti.sum_doubleForkCartanMatrix_mul_doubleForkMark_eq_zero` and
  `TauCeti.doubleForkCartanMatrix_mulVec_doubleForkMark_eq_zero`: the affine marks form a null
  vector, row by row and as a matrix-vector product.
* `TauCeti.doubleForkCartanMatrix_diag`, `TauCeti.isSimplyLaced_doubleForkCartanMatrix`,
  `TauCeti.doubleForkCartanMatrix_off_diag_nonpos`, `TauCeti.doubleForkCartanMatrix_isSymm` and
  `TauCeti.doubleForkCartanMatrix_transpose`: the shape of the matrix. Together they certify that
  it is a symmetric, simply-laced generalized Cartan matrix, which is what an argument embedding
  this obstruction into an arbitrary diagram has to match against.
* `TauCeti.not_isFiniteType_doubleForkCartanMatrix`: no affine `D̃ₘ` matrix for `m ≥ 5` is of
  finite type.

## References

This is the affine-`D` obstruction needed by the “chain/fork length constraints” step in Layer 5 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`.  See J. E. Humphreys,
*Introduction to Lie Algebras and Representation Theory*, §11.4, and Bourbaki, *Lie Groups and
Lie Algebras, Chapters 4--6*, Ch. VI, §4.
-/

namespace TauCeti

/-- The indices of the affine `D̃ₘ` diagram for `m = n + 5`, parameterized by its `n` internal
vertices between the two forks.

Each outer `Fin 2` is the pair of leaves attached to the left, resp. right, fork vertex, so the
diagram has four leaves in all. The middle `Fin (n + 2)` consists of the two fork vertices and the
`n` vertices between them. -/
abbrev DoubleForkIndex (n : ℕ) := Fin 2 ⊕ (Fin (n + 2) ⊕ Fin 2)

/-- The Cartan matrix of the affine `D̃ₘ` diagram for `m = n + 5`, parameterized by the `n`
internal chain vertices between its two forks. -/
def doubleForkCartanMatrix (n : ℕ) : Matrix (DoubleForkIndex n) (DoubleForkIndex n) ℤ
  | .inl i, .inl j => if i = j then 2 else 0
  | .inl _, .inr (.inl j) => if j.val = 0 then -1 else 0
  | .inl _, .inr (.inr _) => 0
  | .inr (.inl i), .inl _ => if i.val = 0 then -1 else 0
  | .inr (.inl i), .inr (.inl j) => CartanMatrix.A (n + 2) i j
  | .inr (.inl i), .inr (.inr _) => if i.val + 1 = n + 2 then -1 else 0
  | .inr (.inr _), .inl _ => 0
  | .inr (.inr _), .inr (.inl j) => if j.val + 1 = n + 2 then -1 else 0
  | .inr (.inr i), .inr (.inr j) => if i = j then 2 else 0

/-- The affine marks for `D̃ₘ`, where `m = n + 5`: `1` on each of the four leaves and `2` on
every vertex of the middle chain. -/
def doubleForkMark (n : ℕ) : DoubleForkIndex n → ℚ
  | .inl _ => 1
  | .inr (.inl _) => 2
  | .inr (.inr _) => 1

-- `(rfl)`, not `rfl`: the bodies of `doubleForkCartanMatrix` and `doubleForkMark` are deliberately
-- left unexposed, and the parenthesised form keeps these equations out of the exported
-- definitional-equality check.

/-- The entries between two left leaves. -/
@[simp]
theorem doubleForkCartanMatrix_inl_inl (n : ℕ) (i j : Fin 2) :
    doubleForkCartanMatrix n (.inl i) (.inl j) = if i = j then 2 else 0 := (rfl)

/-- The entries from a left leaf to the middle chain. -/
@[simp]
theorem doubleForkCartanMatrix_inl_inr_inl (n : ℕ) (i : Fin 2) (j : Fin (n + 2)) :
    doubleForkCartanMatrix n (.inl i) (.inr (.inl j)) =
      if j.val = 0 then -1 else 0 := (rfl)

/-- The entries from a left leaf to a right leaf. -/
@[simp]
theorem doubleForkCartanMatrix_inl_inr_inr (n : ℕ) (i j : Fin 2) :
    doubleForkCartanMatrix n (.inl i) (.inr (.inr j)) = 0 := (rfl)

/-- The entries from the middle chain to a left leaf. -/
@[simp]
theorem doubleForkCartanMatrix_inr_inl_inl (n : ℕ) (i : Fin (n + 2)) (j : Fin 2) :
    doubleForkCartanMatrix n (.inr (.inl i)) (.inl j) =
      if i.val = 0 then -1 else 0 := (rfl)

/-- The middle chain is Mathlib's Cartan matrix of type `A`. This is not a `simp` lemma, since
`CartanMatrix.A` has no entry lemma and `simp` would stall on it. -/
theorem doubleForkCartanMatrix_inr_inl_inr_inl_eq_cartanMatrix_A (n : ℕ) (i j : Fin (n + 2)) :
    doubleForkCartanMatrix n (.inr (.inl i)) (.inr (.inl j)) =
      CartanMatrix.A (n + 2) i j := (rfl)

/-- The entries within the middle chain: `2` on the diagonal, and `-1` between consecutive
vertices of the chain. -/
@[simp]
theorem doubleForkCartanMatrix_inr_inl_inr_inl (n : ℕ) (i j : Fin (n + 2)) :
    doubleForkCartanMatrix n (.inr (.inl i)) (.inr (.inl j)) =
      if i = j then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0 := by
  rw [doubleForkCartanMatrix_inr_inl_inr_inl_eq_cartanMatrix_A, ← chainEntry_eq_cartanMatrix_A,
    chainEntry_def]
  simp only [Fin.ext_iff]
  split_ifs <;> omega

/-- The entries from the middle chain to a right leaf. -/
@[simp]
theorem doubleForkCartanMatrix_inr_inl_inr_inr (n : ℕ) (i : Fin (n + 2)) (j : Fin 2) :
    doubleForkCartanMatrix n (.inr (.inl i)) (.inr (.inr j)) =
      if i.val + 1 = n + 2 then -1 else 0 := (rfl)

/-- The entries from a right leaf to a left leaf. -/
@[simp]
theorem doubleForkCartanMatrix_inr_inr_inl (n : ℕ) (i j : Fin 2) :
    doubleForkCartanMatrix n (.inr (.inr i)) (.inl j) = 0 := (rfl)

/-- The entries from a right leaf to the middle chain. -/
@[simp]
theorem doubleForkCartanMatrix_inr_inr_inr_inl (n : ℕ) (i : Fin 2) (j : Fin (n + 2)) :
    doubleForkCartanMatrix n (.inr (.inr i)) (.inr (.inl j)) =
      if j.val + 1 = n + 2 then -1 else 0 := (rfl)

/-- The entries between two right leaves. -/
@[simp]
theorem doubleForkCartanMatrix_inr_inr_inr_inr (n : ℕ) (i j : Fin 2) :
    doubleForkCartanMatrix n (.inr (.inr i)) (.inr (.inr j)) =
      if i = j then 2 else 0 := (rfl)

/-- Every left leaf has affine mark one. -/
@[simp]
theorem doubleForkMark_inl (n : ℕ) (i : Fin 2) : doubleForkMark n (.inl i) = 1 := (rfl)

/-- Every vertex of the middle chain has affine mark two. -/
@[simp]
theorem doubleForkMark_inr_inl (n : ℕ) (i : Fin (n + 2)) :
    doubleForkMark n (.inr (.inl i)) = 2 := (rfl)

/-- Every right leaf has affine mark one. -/
@[simp]
theorem doubleForkMark_inr_inr (n : ℕ) (i : Fin 2) :
    doubleForkMark n (.inr (.inr i)) = 1 := (rfl)

/-- The affine mark vector is nonzero: every leaf has mark `1`. -/
theorem doubleForkMark_ne_zero (n : ℕ) : doubleForkMark n ≠ 0 := by
  intro h
  have := congrFun h (Sum.inl (0 : Fin 2))
  simp at this

/-- Every diagonal entry of a double-fork Cartan matrix is `2`. -/
@[simp]
theorem doubleForkCartanMatrix_diag (n : ℕ) (i : DoubleForkIndex n) :
    doubleForkCartanMatrix n i i = 2 := by
  rcases i with i | i | i <;> simp

/-- A double-fork Cartan matrix is simply laced: every off-diagonal entry is `0` or `-1`. -/
theorem isSimplyLaced_doubleForkCartanMatrix (n : ℕ) :
    (doubleForkCartanMatrix n).IsSimplyLaced := by
  intro i j hij
  rcases i with i | i | i <;> rcases j with j | j | j <;> simp only
    [doubleForkCartanMatrix_inl_inl, doubleForkCartanMatrix_inl_inr_inl,
      doubleForkCartanMatrix_inl_inr_inr, doubleForkCartanMatrix_inr_inl_inl,
      doubleForkCartanMatrix_inr_inl_inr_inl, doubleForkCartanMatrix_inr_inl_inr_inr,
      doubleForkCartanMatrix_inr_inr_inl, doubleForkCartanMatrix_inr_inr_inr_inl,
      doubleForkCartanMatrix_inr_inr_inr_inr] <;> (try split_ifs) <;> simp_all

/-- Every off-diagonal entry of a double-fork Cartan matrix is nonpositive. -/
theorem doubleForkCartanMatrix_off_diag_nonpos (n : ℕ) {i j : DoubleForkIndex n} (hij : i ≠ j) :
    doubleForkCartanMatrix n i j ≤ 0 := by
  rcases isSimplyLaced_doubleForkCartanMatrix n hij with h | h <;> omega

/-- Every double-fork Cartan matrix is symmetric. -/
theorem doubleForkCartanMatrix_isSymm (n : ℕ) : (doubleForkCartanMatrix n).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rcases i with i | i | i <;> rcases j with j | j | j <;> simp [eq_comm, or_comm]

/-- Transposing a double-fork Cartan matrix leaves it unchanged. -/
@[simp]
theorem doubleForkCartanMatrix_transpose (n : ℕ) :
    (doubleForkCartanMatrix n).transpose = doubleForkCartanMatrix n :=
  (doubleForkCartanMatrix_isSymm n).eq

/-- **Every row of a double-fork Cartan matrix annihilates the affine marks.** At a leaf the row
meets its fork vertex only; at a fork vertex the two leaves cancel the end of the chain the row sum
from `TauCeti.sum_range_chainEntry_mul` leaves over; and in the interior of the chain the row sum
vanishes on its own.

This is the shape `TauCeti.IsFiniteType.eq_zero_of_forall_mul_sum_apply_mul_nonpos` consumes; it is
not a `simp` lemma, since `simp` dismantles the sum over `TauCeti.DoubleForkIndex` with the entry
lemmas above before this equation could fire. -/
theorem sum_doubleForkCartanMatrix_mul_doubleForkMark_eq_zero (n : ℕ) (i : DoubleForkIndex n) :
    ∑ j, (doubleForkCartanMatrix n i j : ℚ) * doubleForkMark n j = 0 := by
  rcases i with i | i | i
  · -- A left leaf: the diagonal `2` against the edge to the first vertex of the chain.
    simp [Fintype.sum_sum_type]
  · -- A vertex of the chain: the row sum of the chain, plus the leaves at whichever end it is.
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [doubleForkCartanMatrix_inr_inl_inl, doubleForkCartanMatrix_inr_inl_inr_inr,
      doubleForkCartanMatrix_inr_inl_inr_inl_eq_cartanMatrix_A, doubleForkMark_inl,
      doubleForkMark_inr_inl, doubleForkMark_inr_inr, Fin.sum_univ_two]
    have hmiddle : ∑ j, ((CartanMatrix.A (n + 2) i j : ℤ) : ℚ) * 2
        = 2 * 2 - (if (i : ℕ) = 0 then 0 else 2)
          - (if (i : ℕ) + 1 = n + 2 then 0 else 2) := by
      simp_rw [← chainEntry_eq_cartanMatrix_A]
      have key := sum_range_chainEntry_mul i.isLt fun _ ↦ (2 : ℚ)
      rw [← Fin.sum_univ_eq_sum_range (fun s ↦ (chainEntry i s : ℚ) * 2) (n + 2)] at key
      exact key
    rw [hmiddle]
    split_ifs <;> norm_num
  · -- A right leaf: the mirror image of the first case, at the far end of the chain.
    have hlast : ∀ j : Fin (n + 2), j.val + 1 = n + 2 ↔ j = Fin.last (n + 1) := by
      intro j
      rw [Fin.ext_iff]
      simp only [Fin.val_last]
      omega
    simp only [Fintype.sum_sum_type, doubleForkCartanMatrix_inr_inr_inl,
      doubleForkCartanMatrix_inr_inr_inr_inl, doubleForkCartanMatrix_inr_inr_inr_inr,
      doubleForkMark_inl, doubleForkMark_inr_inl, doubleForkMark_inr_inr, Fin.sum_univ_two, hlast]
    fin_cases i <;> norm_num

/-- The standard affine marks form a null vector for the double-fork Cartan matrix. -/
theorem doubleForkCartanMatrix_mulVec_doubleForkMark_eq_zero (n : ℕ) :
    (Matrix.map (doubleForkCartanMatrix n) Int.cast).mulVec (doubleForkMark n) = 0 := by
  funext i
  simpa only [Matrix.mulVec_apply_eq_sum, Matrix.map_apply, Pi.zero_apply] using
    sum_doubleForkCartanMatrix_mul_doubleForkMark_eq_zero n i

/-- **Affine Cartan matrices `D̃ₘ` for `m ≥ 5` are not of finite type.** The affine marks are a
nonzero null vector, contradicting positive definiteness of any finite-type symmetrization. -/
theorem not_isFiniteType_doubleForkCartanMatrix (n : ℕ) :
    ¬ IsFiniteType (doubleForkCartanMatrix n) := by
  intro h
  have hz : doubleForkMark n = 0 := h.eq_zero_of_forall_mul_sum_apply_mul_nonpos fun i => by
    rw [sum_doubleForkCartanMatrix_mul_doubleForkMark_eq_zero, mul_zero]
  exact doubleForkMark_ne_zero n hz

end TauCeti
