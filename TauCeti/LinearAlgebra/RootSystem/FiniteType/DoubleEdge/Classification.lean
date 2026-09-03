/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Classification
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.DoubleEdge.NoBranch
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

This file classifies the model double-edge chains themselves, and combines this with the no-branch
extraction theorem to establish the double-edge branch of the classification: every connected
finite-type Cartan matrix carrying a double edge has a unique valid Dynkin type
(`Bₙ`, `Cₙ`, or `F₄`).

## Main results

* `TauCeti.doubleEdgeCartanMatrix_two_two`: the exceptional surviving matrix is `F₄`, up to its
  explicit simultaneous reindexing.
* `TauCeti.isFiniteType_doubleEdgeCartanMatrix_iff`: two nonempty chains joined by a double edge
  are of finite type exactly for the `B_n`, `C_n`, and `F₄` shapes.
* `TauCeti.IsFiniteType.existsUnique_dynkinType_of_apply_mul_apply_eq_two`: a connected finite-type
  Cartan matrix with a double edge has a unique valid Dynkin type (`Bₙ`, `Cₙ`, or `F₄`).
* `TauCeti.existsUnique_dynkinType_of_apply_mul_apply_eq_two`: the root-system counterpart for
  an irreducible reduced crystallographic finite root system with a double edge.

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

/-- The equivalence identifying the double-edge chain with one vertex on the first chain with the
standard Bourbaki-numbered `B_{q+1}` diagram. It puts the `q` vertices of the second chain first,
followed by the lone vertex of the first chain. -/
def doubleEdgeBEquiv (q : ℕ) : Fin 1 ⊕ Fin q ≃ Fin (q + 1) :=
  (Equiv.sumComm (Fin 1) (Fin q)).trans finSumFinEquiv

@[simp] lemma doubleEdgeBEquiv_inl_val (q : ℕ) (i : Fin 1) :
    (doubleEdgeBEquiv q (Sum.inl i) : ℕ) = q := by
  simp [doubleEdgeBEquiv]

@[simp] lemma doubleEdgeBEquiv_inr_val (q : ℕ) (i : Fin q) :
    (doubleEdgeBEquiv q (Sum.inr i) : ℕ) = i := by
  simp [doubleEdgeBEquiv]

/-- **A double-edge chain whose first chain is a single vertex is of type `Bₙ`.** -/
theorem doubleEdgeCartanMatrix_one_left (q : ℕ) :
    doubleEdgeCartanMatrix 1 q =
      (CartanMatrix.B (q + 1)).submatrix (doubleEdgeBEquiv q) (doubleEdgeBEquiv q) := by
  ext v w
  rcases v with a | a <;> rcases w with b | b <;>
    have ha := a.isLt <;> have hb := b.isLt <;>
    simp only [Matrix.submatrix_apply,
      doubleEdgeBEquiv_inl_val, doubleEdgeBEquiv_inr_val,
      doubleEdgeCartanMatrix_inl_inl, doubleEdgeCartanMatrix_inr_inr,
      doubleEdgeCartanMatrix_inl_inr, doubleEdgeCartanMatrix_inr_inl,
      CartanMatrix.B, Matrix.of_apply, chainEntry_def, Fin.ext_iff] <;>
    split_ifs <;> omega

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

/-- Every admissible finite-type double-edge chain carries a unique valid Dynkin type. -/
private theorem doubleEdgeCartanMatrix_existsUnique_dynkinType (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (h : q = 1 ∨ p = 1 ∨ (p = 2 ∧ q = 2)) :
    ∃! t : DynkinType, t.Valid ∧
      ∃ e : Fin p ⊕ Fin q ≃ Fin t.rank,
        ∀ i j, doubleEdgeCartanMatrix p q i j = t.cartanMatrix (e i) (e j) := by
  have hex : ∃ t : DynkinType, t.Valid ∧
      ∃ e : Fin p ⊕ Fin q ≃ Fin t.rank,
        ∀ i j, doubleEdgeCartanMatrix p q i j = t.cartanMatrix (e i) (e j) := by
    rcases h with rfl | rfl | ⟨rfl, rfl⟩
    · by_cases hp2 : 2 ≤ p
      · refine ⟨.C (p + 1), ?_, finSumFinEquiv, fun i j ↦ ?_⟩
        · simp only [DynkinType.valid_C]; omega
        · rw [DynkinType.cartanMatrix_C, doubleEdgeCartanMatrix_one_right]
          rfl
      · have hp1 : p = 1 := by omega
        subst hp1
        refine ⟨.B 2, by simp only [DynkinType.valid_B]; omega, doubleEdgeBEquiv 1, fun i j ↦ ?_⟩
        rw [DynkinType.cartanMatrix_B, doubleEdgeCartanMatrix_one_left]
        rfl
    · refine ⟨.B (q + 1), ?_, doubleEdgeBEquiv q, fun i j ↦ ?_⟩
      · simp only [DynkinType.valid_B]; omega
      · rw [DynkinType.cartanMatrix_B, doubleEdgeCartanMatrix_one_left]
        rfl
    · refine ⟨.F4, DynkinType.valid_F4, doubleEdgeF4Equiv, fun i j ↦ ?_⟩
      rw [doubleEdgeCartanMatrix_two_two]
      rfl
  obtain ⟨t, htv, ht⟩ := hex
  exact ⟨t, ⟨htv, ht⟩, fun s hs ↦ DynkinType.eq_of_valid_of_forall_eq hs.1 htv hs.2.choose ht.choose
    hs.2.choose_spec ht.choose_spec⟩

namespace IsFiniteType

variable {B : Type*} [Fintype B] {A : Matrix B B ℤ}

/-- **The double-edge branch of the finite-type classification.** A connected finite-type matrix
containing a double edge has a unique valid Dynkin type. It is one of `Bₙ`, `Cₙ`, or `F₄`. -/
theorem existsUnique_dynkinType_of_apply_mul_apply_eq_two
    (h : IsFiniteType A) (hconn : (diagramGraph A).Preconnected)
    {u v : B} (huv : A u v * A v u = 2) :
    ∃! t : DynkinType, t.Valid ∧
      ∃ e : B ≃ Fin t.rank, ∀ i j, A i j = t.cartanMatrix (e i) (e j) := by
  obtain ⟨p, q, hp, hq, hadm, e, he⟩ :=
    h.exists_equiv_forall_eq_doubleEdgeCartanMatrix_of_apply_mul_apply_eq_two hconn huv
  obtain ⟨t, ⟨htv, et, het⟩, -⟩ :=
    doubleEdgeCartanMatrix_existsUnique_dynkinType p q hp hq hadm
  refine ⟨t, ⟨htv, e.trans et, fun i j ↦ by rw [he, het]; rfl⟩, ?_⟩
  intro s hs
  exact DynkinType.eq_of_valid_of_forall_eq hs.1 htv hs.2.choose (e.trans et)
    hs.2.choose_spec (fun i j ↦ by rw [he, het]; rfl)

end IsFiniteType

section RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [CharZero R] [IsDomain R]
  [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]

/-- **An irreducible root system with a double edge has a unique valid Dynkin type.** The type is
one of `Bₙ`, `Cₙ`, or `F₄`. -/
theorem existsUnique_dynkinType_of_apply_mul_apply_eq_two (b : P.Base)
    {u v : b.support} (huv : b.cartanMatrix u v * b.cartanMatrix v u = 2) :
    ∃! t : DynkinType, t.Valid ∧ HasCartanType P b t := by
  have : Nonempty ι := ⟨u.1⟩
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ :=
    (isFiniteType_cartanMatrix b).existsUnique_dynkinType_of_apply_mul_apply_eq_two
      (connected_diagramGraph_cartanMatrix b).preconnected huv
  exact ((hasCartanType_iff b t).mpr ⟨e, he⟩).existsUnique_of_valid ht

end RootPairing

end TauCeti
