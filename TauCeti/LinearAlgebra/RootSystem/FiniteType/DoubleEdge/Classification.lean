/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.DoubleEdge.Basic
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin

public section

/-!
# Classification of finite double-edge chains

The double-edge bound in
`TauCeti.LinearAlgebra.RootSystem.FiniteType.DoubleEdge.Basic` leaves exactly three possible shapes
for two nonempty chains joined by a double edge: one chain has one vertex, giving the families
`B_n` and `C_n`, or both chains have two vertices, giving `F_4`. That file realizes the two infinite
families and deliberately leaves the exceptional case to the assembly step of the classification.

This file supplies that step. The equivalence `TauCeti.doubleEdgeF4Equiv` reads the second chain
towards the double edge, followed by the first chain away from it. Under this ordering the matrix
`TauCeti.doubleEdgeCartanMatrix 2 2` is Mathlib's Bourbaki-numbered `CartanMatrix.F₄`. Its finite
type follows from `TauCeti.DynkinType.isFiniteType_cartanMatrix_F4`, and combining this with the
double-edge bound gives a complete characterization of when the model diagram is of finite type.

The result classifies the model double-edge chains themselves. The preceding extraction problem --
showing that a connected finite-type Cartan matrix carrying a double edge has this shape -- remains
part of the existence half of the Cartan--Killing classification.

## Main results

* `TauCeti.doubleEdgeCartanMatrix_two_two`: the exceptional surviving matrix is `F₄`, up to its
  explicit simultaneous reindexing.
* `TauCeti.isFiniteType_doubleEdgeCartanMatrix_iff`: two nonempty chains joined by a double edge
  are of finite type exactly for the `B_n`, `C_n`, and `F₄` shapes.

## References

This is the double-edge assembly step in the "classification of finite-type Cartan matrices"
target of Layer 5 of `TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. The numbering of
`F₄` is Bourbaki's; see Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §4 and
plate VIII, or J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §11.4.
-/

open scoped Matrix

namespace TauCeti

/-- The ordering of a double-edge chain with two vertices on each side that identifies it with
the Bourbaki-numbered `F₄` diagram. It reads the second chain from its outer vertex to the double
edge, then the first chain from the double edge to its outer vertex. Thus
`inr 0, inr 1, inl 1, inl 0` become nodes `0, 1, 2, 3`. -/
def doubleEdgeF4Equiv : Fin 2 ⊕ Fin 2 ≃ Fin 4 :=
  ((Equiv.sumCongr Fin.revPerm (Equiv.refl _)).trans (Equiv.sumComm _ _)).trans finSumFinEquiv

/-- The outer vertex of the first chain is node `3` under `doubleEdgeF4Equiv`. -/
@[simp] lemma doubleEdgeF4Equiv_inl_zero :
    doubleEdgeF4Equiv (Sum.inl (0 : Fin 2)) = 3 := by decide

/-- The inner vertex of the first chain is node `2` under `doubleEdgeF4Equiv`. -/
@[simp] lemma doubleEdgeF4Equiv_inl_one :
    doubleEdgeF4Equiv (Sum.inl (1 : Fin 2)) = 2 := by decide

/-- The outer vertex of the second chain is node `0` under `doubleEdgeF4Equiv`. -/
@[simp] lemma doubleEdgeF4Equiv_inr_zero :
    doubleEdgeF4Equiv (Sum.inr (0 : Fin 2)) = 0 := by decide

/-- The inner vertex of the second chain is node `1` under `doubleEdgeF4Equiv`. -/
@[simp] lemma doubleEdgeF4Equiv_inr_one :
    doubleEdgeF4Equiv (Sum.inr (1 : Fin 2)) = 1 := by decide

/-- **The exceptional double-edge chain is `F₄`.** After ordering its four vertices from one outer
end to the other, with the double edge in the middle, `doubleEdgeCartanMatrix 2 2` is the standard
Bourbaki-numbered Cartan matrix of the Dynkin type `F₄`. -/
theorem doubleEdgeCartanMatrix_two_two :
    doubleEdgeCartanMatrix 2 2 =
      DynkinType.F4.cartanMatrix.submatrix doubleEdgeF4Equiv doubleEdgeF4Equiv := by
  rw [DynkinType.cartanMatrix_F4]
  ext v w
  dsimp [Matrix.submatrix]
  rcases v with v | v <;> rcases w with w | w <;>
    fin_cases v <;> fin_cases w <;>
    norm_num [doubleEdgeCartanMatrix_inl_inl, doubleEdgeCartanMatrix_inr_inr,
      doubleEdgeCartanMatrix_inl_inr, doubleEdgeCartanMatrix_inr_inl,
      chainEntry_def, CartanMatrix.F₄, _root_.Matrix.cons_val_zero,
      _root_.Matrix.cons_val_one, _root_.Matrix.cons_val_two,
      _root_.Matrix.cons_val_three]

/-- The double-edge chain with two vertices on each side is of finite type, since it is the
standard Cartan matrix of type `F₄` after reindexing. -/
theorem isFiniteType_doubleEdgeCartanMatrix_two_two :
    IsFiniteType (doubleEdgeCartanMatrix 2 2) := by
  rw [doubleEdgeCartanMatrix_two_two]
  exact DynkinType.isFiniteType_cartanMatrix_F4.submatrix doubleEdgeF4Equiv.injective

/-- **Classification of finite double-edge chains.** Suppose both chains are nonempty. Their
double-edge diagram is of finite type exactly when the second chain is a single vertex (type
`C_n`), the first chain is a single vertex (type `B_n`), or both chains have two vertices (type
`F₄`). -/
@[simp] theorem isFiniteType_doubleEdgeCartanMatrix_iff {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    IsFiniteType (doubleEdgeCartanMatrix p q) ↔ q = 1 ∨ p = 1 ∨ (p = 2 ∧ q = 2) := by
  constructor
  · exact eq_one_or_eq_one_or_eq_two_two_of_isFiniteType_doubleEdge hp hq
  · rintro (rfl | rfl | ⟨rfl, rfl⟩)
    · exact isFiniteType_doubleEdgeCartanMatrix_one_right p
    · exact isFiniteType_doubleEdgeCartanMatrix_one_left q
    · exact isFiniteType_doubleEdgeCartanMatrix_two_two

end TauCeti
