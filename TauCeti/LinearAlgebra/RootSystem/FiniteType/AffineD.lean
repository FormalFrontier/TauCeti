/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic

public section

/-!
# Affine type D is not of finite type

The diagram of an indecomposable finite-type Cartan matrix is a tree of maximum degree three. To
finish the simply-laced part of the Cartan--Killing classification one must also show that such a
tree cannot have two branch vertices.  The path between two branch vertices, together with two
branches at either end, contains an affine diagram of type `D`.  This file supplies the uniform
matrix obstruction for that argument.

The matrix `affineDCartanMatrix n` has two fork vertices joined by a chain with `n` internal
vertices. Each fork vertex has two leaves. Thus `n = 0` is the six-vertex diagram `D̃₅`, and
increasing `n` lengthens the middle chain.  The vector which is `1` on the four leaves and `2` on
the middle chain is a nonzero null vector.  Since a finite-type matrix has positive-definite
symmetrization, it cannot admit this vector.

## Main definitions

* `TauCeti.AffineDIndex`: the four leaves and the vertices of the middle chain.
* `TauCeti.affineDCartanMatrix`: the simply-laced affine Cartan matrix of type `D`.
* `TauCeti.affineDMark`: the standard affine marks, equal to `1` on leaves and `2` on the chain.

## Main results

* `TauCeti.affineDCartanMatrix_mulVec_affineDMark`: the affine marks form a null vector.
* `TauCeti.not_isFiniteType_affineD`: no member of the affine `D` family is of finite type.

## References

This is the affine-`D` obstruction needed by the “chain/fork length constraints” step in Layer 5 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`.  See J. E. Humphreys,
*Introduction to Lie Algebras and Representation Theory*, §11.4, and Bourbaki, *Lie Groups and
Lie Algebras, Chapters 4--6*, Ch. VI, §4.
-/

namespace TauCeti

/-- The indices of an affine `D` diagram with `n` internal vertices between its two forks.

The outer `Fin 2` types are the two leaves at the left and right forks. The middle
`Fin (n + 2)` consists of the two fork vertices and the `n` vertices between them. -/
abbrev AffineDIndex (n : ℕ) := Fin 2 ⊕ (Fin (n + 2) ⊕ Fin 2)

/-- The Cartan matrix of the affine `D` diagram whose two fork vertices have `n` internal chain
vertices between them. -/
def affineDCartanMatrix (n : ℕ) : Matrix (AffineDIndex n) (AffineDIndex n) ℤ
  | .inl i, .inl j => if i = j then 2 else 0
  | .inl _, .inr (.inl j) => if j.val = 0 then -1 else 0
  | .inl _, .inr (.inr _) => 0
  | .inr (.inl i), .inl _ => if i.val = 0 then -1 else 0
  | .inr (.inl i), .inr (.inl j) => CartanMatrix.A (n + 2) i j
  | .inr (.inl i), .inr (.inr _) => if i.val + 1 = n + 2 then -1 else 0
  | .inr (.inr _), .inl _ => 0
  | .inr (.inr _), .inr (.inl j) => if j.val + 1 = n + 2 then -1 else 0
  | .inr (.inr i), .inr (.inr j) => if i = j then 2 else 0

/-- The affine marks for type `D`: `1` on each of the four leaves and `2` on every vertex of the
middle chain. -/
def affineDMark (n : ℕ) : AffineDIndex n → ℚ
  | .inl _ => 1
  | .inr (.inl _) => 2
  | .inr (.inr _) => 1

/-- The affine mark vector is nonzero: every leaf has mark `1`. -/
theorem affineDMark_ne_zero (n : ℕ) : affineDMark n ≠ 0 := by
  intro h
  have := congrFun h (Sum.inl (0 : Fin 2))
  norm_num [affineDMark] at this

@[simp]
theorem affineDCartanMatrix_apply_self (n : ℕ) (i : AffineDIndex n) :
    affineDCartanMatrix n i i = 2 := by
  rcases i with i | i
  · simp [affineDCartanMatrix]
  · rcases i with i | i
    · simpa [affineDCartanMatrix] using congrFun (CartanMatrix.A_diag (n + 2)) i
    · simp [affineDCartanMatrix]

/-- Every off-diagonal entry of the affine `D` matrix is nonpositive. -/
theorem affineDCartanMatrix_apply_nonpos_of_ne (n : ℕ) {i j : AffineDIndex n} (hij : i ≠ j) :
    affineDCartanMatrix n i j ≤ 0 := by
  rcases i with i | i <;> rcases j with j | j
  · have hne : i ≠ j := fun h => hij (by rw [h])
    simp only [affineDCartanMatrix]
    split_ifs <;> omega
  · rcases j with j | j
    · simp only [affineDCartanMatrix]
      split_ifs <;> omega
    · simp [affineDCartanMatrix]
  · rcases i with i | i
    · simp only [affineDCartanMatrix]
      split_ifs <;> omega
    · simp [affineDCartanMatrix]
  · rcases i with i | i <;> rcases j with j | j
    · exact CartanMatrix.A_apply_le_zero_of_ne (n + 2) i j fun h => hij (by simp [h])
    · simp only [affineDCartanMatrix]
      split_ifs <;> omega
    · simp only [affineDCartanMatrix]
      split_ifs <;> omega
    · have hne : i ≠ j := fun h => hij (by rw [h])
      simp only [affineDCartanMatrix]
      split_ifs <;> omega

/-- The affine Cartan matrix of type `D` is symmetric. -/
theorem affineDCartanMatrix_isSymm (n : ℕ) : (affineDCartanMatrix n).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rcases i with i | i <;> rcases j with j | j
  · simp [affineDCartanMatrix, eq_comm]
  · rcases j with j | j <;> simp [affineDCartanMatrix]
  · rcases i with i | i <;> simp [affineDCartanMatrix]
  · rcases i with i | i <;> rcases j with j | j
    · exact Matrix.IsSymm.ext_iff.mp (CartanMatrix.A_isSymm (n + 2)) i j
    · simp [affineDCartanMatrix]
    · simp [affineDCartanMatrix]
    · simp [affineDCartanMatrix, eq_comm]

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

private lemma sum_cartanMatrix_A_row (n : ℕ) (i : Fin (n + 2)) :
    ∑ j, (CartanMatrix.A (n + 2) i j : ℚ) =
      (if i.val = 0 then 1 else 0) + if i.val + 1 = n + 2 then 1 else 0 :=
  sum_cartanMatrix_A_row_general (n + 2) i

/-- The standard affine marks form a null vector for the affine Cartan matrix of type `D`. -/
theorem affineDCartanMatrix_mulVec_affineDMark (n : ℕ) :
    (Matrix.map (affineDCartanMatrix n) Int.cast).mulVec (affineDMark n) = 0 := by
  funext i
  change (∑ j, (affineDCartanMatrix n i j : ℚ) * affineDMark n j) = 0
  rcases i with i | i
  · simp [Fintype.sum_sum_type, affineDCartanMatrix, affineDMark]
  · rcases i with i | i
    · rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [affineDCartanMatrix, affineDMark]
      simp only [Fin.sum_univ_two]
      have hmiddle : (∑ j, (CartanMatrix.A (n + 2) i j : ℚ) * 2) =
          ((if i.val = 0 then 1 else 0) + if i.val + 1 = n + 2 then 1 else 0) * 2 := by
        rw [← Finset.sum_mul, sum_cartanMatrix_A_row]
      rw [hmiddle]
      split_ifs <;> norm_num
    · have hlast : ∀ j : Fin (n + 2), j.val + 1 = n + 2 ↔ j = Fin.last (n + 1) := by
        intro j
        rw [Fin.ext_iff]
        simp only [Fin.val_last]
        omega
      simp only [Fintype.sum_sum_type, affineDCartanMatrix, affineDMark, Fin.sum_univ_two,
        hlast]
      fin_cases i <;> norm_num

/-- **Affine Cartan matrices of type `D` are not of finite type.** The affine marks are a nonzero
null vector, contradicting positive definiteness of any finite-type symmetrization. -/
theorem not_isFiniteType_affineD (n : ℕ) : ¬ IsFiniteType (affineDCartanMatrix n) := by
  intro h
  have hz : affineDMark n = 0 := h.eq_zero_of_forall_mul_sum_apply_mul_nonpos fun i => by
    have hrow := congrFun (affineDCartanMatrix_mulVec_affineDMark n) i
    change (∑ j, (affineDCartanMatrix n i j : ℚ) * affineDMark n j) = 0 at hrow
    rw [hrow]
    simp
  exact affineDMark_ne_zero n hz

end TauCeti
