/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic

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

## Main definitions

* `TauCeti.DoubleForkIndex`: the four leaves and the vertices of the middle chain.
* `TauCeti.doubleForkCartanMatrix`: the simply-laced double-fork Cartan matrix.
* `TauCeti.doubleForkMark`: the affine marks, equal to `1` on leaves and `2` on the chain.

## Main results

* `TauCeti.doubleForkCartanMatrix_mulVec_doubleForkMark`: the affine marks form a null vector.
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

The outer `Fin 2` types are the two leaves at the left and right forks. The middle
`Fin (n + 2)` consists of the two fork vertices and the `n` vertices between them. -/
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

private lemma doubleForkCartanMatrix_inl_inl_aux (n : ℕ) (i j : Fin 2) :
    doubleForkCartanMatrix n (.inl i) (.inl j) = if i = j then 2 else 0 := rfl

/-- The entries between two left leaves. -/
@[simp]
theorem doubleForkCartanMatrix_inl_inl (n : ℕ) (i j : Fin 2) :
    doubleForkCartanMatrix n (.inl i) (.inl j) = if i = j then 2 else 0 :=
  doubleForkCartanMatrix_inl_inl_aux n i j

private lemma doubleForkCartanMatrix_inl_inr_inl_aux (n : ℕ) (i : Fin 2)
    (j : Fin (n + 2)) :
    doubleForkCartanMatrix n (.inl i) (.inr (.inl j)) =
      if j.val = 0 then -1 else 0 := rfl

/-- The entries from a left leaf to the middle chain. -/
@[simp]
theorem doubleForkCartanMatrix_inl_inr_inl (n : ℕ) (i : Fin 2) (j : Fin (n + 2)) :
    doubleForkCartanMatrix n (.inl i) (.inr (.inl j)) =
      if j.val = 0 then -1 else 0 :=
  doubleForkCartanMatrix_inl_inr_inl_aux n i j

private lemma doubleForkCartanMatrix_inl_inr_inr_aux (n : ℕ) (i j : Fin 2) :
    doubleForkCartanMatrix n (.inl i) (.inr (.inr j)) = 0 := rfl

/-- The entries from a left leaf to a right leaf. -/
@[simp]
theorem doubleForkCartanMatrix_inl_inr_inr (n : ℕ) (i j : Fin 2) :
    doubleForkCartanMatrix n (.inl i) (.inr (.inr j)) = 0 :=
  doubleForkCartanMatrix_inl_inr_inr_aux n i j

private lemma doubleForkCartanMatrix_inr_inl_inl_aux (n : ℕ) (i : Fin (n + 2))
    (j : Fin 2) :
    doubleForkCartanMatrix n (.inr (.inl i)) (.inl j) =
      if i.val = 0 then -1 else 0 := rfl

/-- The entries from the middle chain to a left leaf. -/
@[simp]
theorem doubleForkCartanMatrix_inr_inl_inl (n : ℕ) (i : Fin (n + 2)) (j : Fin 2) :
    doubleForkCartanMatrix n (.inr (.inl i)) (.inl j) =
      if i.val = 0 then -1 else 0 :=
  doubleForkCartanMatrix_inr_inl_inl_aux n i j

private lemma doubleForkCartanMatrix_inr_inl_inr_inl_aux (n : ℕ) (i j : Fin (n + 2)) :
    doubleForkCartanMatrix n (.inr (.inl i)) (.inr (.inl j)) =
      CartanMatrix.A (n + 2) i j := rfl

/-- The entries within the middle chain. -/
@[simp]
theorem doubleForkCartanMatrix_inr_inl_inr_inl (n : ℕ) (i j : Fin (n + 2)) :
    doubleForkCartanMatrix n (.inr (.inl i)) (.inr (.inl j)) =
      CartanMatrix.A (n + 2) i j :=
  doubleForkCartanMatrix_inr_inl_inr_inl_aux n i j

private lemma doubleForkCartanMatrix_inr_inl_inr_inr_aux (n : ℕ) (i : Fin (n + 2))
    (j : Fin 2) :
    doubleForkCartanMatrix n (.inr (.inl i)) (.inr (.inr j)) =
      if i.val + 1 = n + 2 then -1 else 0 := rfl

/-- The entries from the middle chain to a right leaf. -/
@[simp]
theorem doubleForkCartanMatrix_inr_inl_inr_inr (n : ℕ) (i : Fin (n + 2)) (j : Fin 2) :
    doubleForkCartanMatrix n (.inr (.inl i)) (.inr (.inr j)) =
      if i.val + 1 = n + 2 then -1 else 0 :=
  doubleForkCartanMatrix_inr_inl_inr_inr_aux n i j

private lemma doubleForkCartanMatrix_inr_inr_inl_aux (n : ℕ) (i j : Fin 2) :
    doubleForkCartanMatrix n (.inr (.inr i)) (.inl j) = 0 := rfl

/-- The entries from a right leaf to a left leaf. -/
@[simp]
theorem doubleForkCartanMatrix_inr_inr_inl (n : ℕ) (i j : Fin 2) :
    doubleForkCartanMatrix n (.inr (.inr i)) (.inl j) = 0 :=
  doubleForkCartanMatrix_inr_inr_inl_aux n i j

private lemma doubleForkCartanMatrix_inr_inr_inr_inl_aux (n : ℕ) (i : Fin 2)
    (j : Fin (n + 2)) :
    doubleForkCartanMatrix n (.inr (.inr i)) (.inr (.inl j)) =
      if j.val + 1 = n + 2 then -1 else 0 := rfl

/-- The entries from a right leaf to the middle chain. -/
@[simp]
theorem doubleForkCartanMatrix_inr_inr_inr_inl (n : ℕ) (i : Fin 2) (j : Fin (n + 2)) :
    doubleForkCartanMatrix n (.inr (.inr i)) (.inr (.inl j)) =
      if j.val + 1 = n + 2 then -1 else 0 :=
  doubleForkCartanMatrix_inr_inr_inr_inl_aux n i j

private lemma doubleForkCartanMatrix_inr_inr_inr_inr_aux (n : ℕ) (i j : Fin 2) :
    doubleForkCartanMatrix n (.inr (.inr i)) (.inr (.inr j)) =
      if i = j then 2 else 0 := rfl

/-- The entries between two right leaves. -/
@[simp]
theorem doubleForkCartanMatrix_inr_inr_inr_inr (n : ℕ) (i j : Fin 2) :
    doubleForkCartanMatrix n (.inr (.inr i)) (.inr (.inr j)) =
      if i = j then 2 else 0 :=
  doubleForkCartanMatrix_inr_inr_inr_inr_aux n i j

private lemma doubleForkMark_inl_aux (n : ℕ) (i : Fin 2) :
    doubleForkMark n (.inl i) = 1 := rfl

/-- Every left leaf has affine mark one. -/
@[simp]
theorem doubleForkMark_inl (n : ℕ) (i : Fin 2) : doubleForkMark n (.inl i) = 1 :=
  doubleForkMark_inl_aux n i

private lemma doubleForkMark_inr_inl_aux (n : ℕ) (i : Fin (n + 2)) :
    doubleForkMark n (.inr (.inl i)) = 2 := rfl

/-- Every vertex of the middle chain has affine mark two. -/
@[simp]
theorem doubleForkMark_inr_inl (n : ℕ) (i : Fin (n + 2)) :
    doubleForkMark n (.inr (.inl i)) = 2 :=
  doubleForkMark_inr_inl_aux n i

private lemma doubleForkMark_inr_inr_aux (n : ℕ) (i : Fin 2) :
    doubleForkMark n (.inr (.inr i)) = 1 := rfl

/-- Every right leaf has affine mark one. -/
@[simp]
theorem doubleForkMark_inr_inr (n : ℕ) (i : Fin 2) :
    doubleForkMark n (.inr (.inr i)) = 1 :=
  doubleForkMark_inr_inr_aux n i

/-- The affine mark vector is nonzero: every leaf has mark `1`. -/
theorem doubleForkMark_ne_zero (n : ℕ) : doubleForkMark n ≠ 0 := by
  intro h
  have := congrFun h (Sum.inl (0 : Fin 2))
  norm_num [doubleForkMark] at this

/-- Every diagonal entry of a double-fork Cartan matrix is `2`. -/
@[simp]
theorem doubleForkCartanMatrix_diag (n : ℕ) (i : DoubleForkIndex n) :
    doubleForkCartanMatrix n i i = 2 := by
  rcases i with i | i
  · simp [doubleForkCartanMatrix]
  · rcases i with i | i
    · simpa [doubleForkCartanMatrix] using congrFun (CartanMatrix.A_diag (n + 2)) i
    · simp [doubleForkCartanMatrix]

/-- Every off-diagonal entry of a double-fork Cartan matrix is nonpositive. -/
theorem doubleForkCartanMatrix_off_diag_nonpos (n : ℕ) {i j : DoubleForkIndex n} (hij : i ≠ j) :
    doubleForkCartanMatrix n i j ≤ 0 := by
  rcases i with i | i <;> rcases j with j | j
  · have hne : i ≠ j := fun h => hij (by rw [h])
    simp only [doubleForkCartanMatrix]
    split_ifs <;> omega
  · rcases j with j | j
    · simp only [doubleForkCartanMatrix]
      split_ifs <;> omega
    · simp [doubleForkCartanMatrix]
  · rcases i with i | i
    · simp only [doubleForkCartanMatrix]
      split_ifs <;> omega
    · simp [doubleForkCartanMatrix]
  · rcases i with i | i <;> rcases j with j | j
    · exact CartanMatrix.A_apply_le_zero_of_ne (n + 2) i j fun h => hij (by simp [h])
    · simp only [doubleForkCartanMatrix]
      split_ifs <;> omega
    · simp only [doubleForkCartanMatrix]
      split_ifs <;> omega
    · have hne : i ≠ j := fun h => hij (by rw [h])
      simp only [doubleForkCartanMatrix]
      split_ifs <;> omega

/-- Every double-fork Cartan matrix is symmetric. -/
theorem doubleForkCartanMatrix_isSymm (n : ℕ) : (doubleForkCartanMatrix n).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rcases i with i | i <;> rcases j with j | j
  · simp [doubleForkCartanMatrix, eq_comm]
  · rcases j with j | j <;> simp [doubleForkCartanMatrix]
  · rcases i with i | i <;> simp [doubleForkCartanMatrix]
  · rcases i with i | i <;> rcases j with j | j
    · exact Matrix.IsSymm.ext_iff.mp (CartanMatrix.A_isSymm (n + 2)) i j
    · simp [doubleForkCartanMatrix]
    · simp [doubleForkCartanMatrix]
    · simp [doubleForkCartanMatrix, eq_comm]

/-- Transposing a double-fork Cartan matrix leaves it unchanged. -/
@[simp]
theorem doubleForkCartanMatrix_transpose (n : ℕ) :
    (doubleForkCartanMatrix n).transpose = doubleForkCartanMatrix n :=
  (doubleForkCartanMatrix_isSymm n).eq

private lemma sum_cartanMatrix_A_row_general : ∀ (m : ℕ) (i : Fin m),
    ∑ j, (CartanMatrix.A m i j : ℚ) =
      (if i.val = 0 then 1 else 0) + if i.val + 1 = m then 1 else 0
  | 0, i => i.elim0
  | m + 1, i => by
      refine Fin.cases ?_ (fun i => ?_) i
      · rcases m with _ | m
        · norm_num [CartanMatrix.A]
        · rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
          have htail : ∀ j : Fin m,
              (CartanMatrix.A (m + 2) 0 j.succ.succ : ℚ) = 0 := by
            intro j
            simp [CartanMatrix.A, Fin.ext_iff]
          simp_rw [htail]
          simp [CartanMatrix.A]
          norm_num
      · rw [Fin.sum_univ_succ]
        have hshift : ∀ j : Fin m,
            (CartanMatrix.A (m + 1) i.succ j.succ : ℚ) =
              CartanMatrix.A m i j := by
          intro j
          simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_succ]
          split_ifs <;> congr 1 <;> omega
        simp_rw [hshift]
        rw [sum_cartanMatrix_A_row_general m i]
        have hfirst : (CartanMatrix.A (m + 1) i.succ 0 : ℚ) =
            if i.val = 0 then -1 else 0 := by
          by_cases hi : i.val = 0
          · simp [CartanMatrix.A, Fin.ext_iff, hi]
          · simp [CartanMatrix.A, Fin.ext_iff, hi]
        rw [hfirst]
        have hlast : i.val + 1 + 1 = m + 1 ↔ i.val + 1 = m := by omega
        simp only [Fin.val_succ, Nat.succ_ne_zero, ↓reduceIte, hlast]
        by_cases hi : i.val = 0 <;> simp [hi]

/-- The standard affine marks form a null vector for the double-fork Cartan matrix. -/
theorem doubleForkCartanMatrix_mulVec_doubleForkMark (n : ℕ) :
    (Matrix.map (doubleForkCartanMatrix n) Int.cast).mulVec (doubleForkMark n) = 0 := by
  funext i
  simp only [Matrix.mulVec_apply_eq_sum, Matrix.map_apply, Pi.zero_apply]
  rcases i with i | i
  · simp [Fintype.sum_sum_type, doubleForkCartanMatrix, doubleForkMark]
  · rcases i with i | i
    · rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [doubleForkCartanMatrix, doubleForkMark]
      simp only [Fin.sum_univ_two]
      have hmiddle : (∑ j, (CartanMatrix.A (n + 2) i j : ℚ) * 2) =
          ((if i.val = 0 then 1 else 0) + if i.val + 1 = n + 2 then 1 else 0) * 2 := by
        rw [← Finset.sum_mul, sum_cartanMatrix_A_row_general (n + 2) i]
      rw [hmiddle]
      split_ifs <;> norm_num
    · have hlast : ∀ j : Fin (n + 2), j.val + 1 = n + 2 ↔ j = Fin.last (n + 1) := by
        intro j
        rw [Fin.ext_iff]
        simp only [Fin.val_last]
        omega
      simp only [Fintype.sum_sum_type, doubleForkCartanMatrix, doubleForkMark, Fin.sum_univ_two,
        hlast]
      fin_cases i <;> norm_num

/-- **Affine Cartan matrices `D̃ₘ` for `m ≥ 5` are not of finite type.** The affine marks are a
nonzero null vector, contradicting positive definiteness of any finite-type symmetrization. -/
theorem not_isFiniteType_doubleForkCartanMatrix (n : ℕ) :
    ¬ IsFiniteType (doubleForkCartanMatrix n) := by
  intro h
  have hz : doubleForkMark n = 0 := h.eq_zero_of_forall_mul_sum_apply_mul_nonpos fun i => by
    have hrow := congrFun (doubleForkCartanMatrix_mulVec_doubleForkMark n) i
    simp only [Matrix.mulVec_apply_eq_sum, Matrix.map_apply, Pi.zero_apply] at hrow
    rw [hrow]
    simp
  exact doubleForkMark_ne_zero n hz

end TauCeti
