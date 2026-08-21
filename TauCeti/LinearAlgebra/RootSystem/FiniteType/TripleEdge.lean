/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
public import TauCeti.LinearAlgebra.RootSystem.RankTwo

/-!
# The triple-edge case of the finite-type classification

A triple edge in a finite-type Cartan matrix is isolated: neither endpoint can have another
neighbour.  This file combines that local obstruction with preconnectedness.  If the whole diagram
is preconnected, the two endpoints are therefore all its vertices.  The rank-two classification then
identifies the matrix, up to one simultaneous relabelling of rows and columns, with the standard
Bourbaki Cartan matrix of type `G₂`.

The point of the result is the passage from the local estimate to a complete classification branch.
`TauCeti.IsFiniteType.apply_eq_zero_of_apply_mul_apply_eq_three` alone allows other connected
components, while the theorem here says that an indecomposable finite-type matrix containing a
triple edge is precisely `G₂`.

## Main results

* `TauCeti.IsFiniteType.eq_or_eq_of_apply_mul_apply_eq_three`: every vertex of a preconnected
  finite-type diagram containing a triple edge is one of its endpoints.
* `TauCeti.IsFiniteType.card_eq_two_of_apply_mul_apply_eq_three`: such a diagram has two vertices.
* `TauCeti.IsFiniteType.exists_equiv_cartanMatrix_eq_G2_of_apply_mul_apply_eq_three`: the matrix
  reindexes to the standard Cartan matrix of type `G₂`.
* `TauCeti.IsFiniteType.exists_apply_mul_apply_eq_three_iff_exists_equiv_cartanMatrix_eq_G2`: a
  preconnected finite-type matrix has a triple edge exactly when it has Cartan type `G₂`.

## References

This is the triple-edge branch of the classification of finite-type Cartan matrices in Layer 5 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`.  See N. Bourbaki, *Lie Groups and Lie
Algebras, Chapters 4--6*, Chapter VI, §4, and J. E. Humphreys, *Introduction to Lie Algebras and
Representation Theory*, §11.4.  The convention is Bourbaki's
`G₂` matrix `!![2, -1; -3, 2]`, with the short simple root first.
-/

public section

open scoped Matrix

namespace TauCeti

namespace IsFiniteType

variable {B : Type*} [Fintype B] {A : Matrix B B ℤ}

/-- **A preconnected finite-type diagram containing a triple edge consists only of its endpoints.**

Both endpoints have no other neighbour by
`TauCeti.IsFiniteType.apply_eq_zero_of_apply_mul_apply_eq_three`.  The induced subgraph on the two
endpoints is therefore closed under taking neighbours.  Preconnectedness forces every vertex into
that induced subgraph. -/
theorem eq_or_eq_of_apply_mul_apply_eq_three (h : IsFiniteType A)
    (hconn : (diagramGraph A).Preconnected) {i j : B} (hij : A i j * A j i = 3) (k : B) :
    k = i ∨ k = j := by
  classical
  have hij_ne : i ≠ j := by
    rintro rfl
    rw [h.apply_self] at hij
    omega
  let H : (diagramGraph A).Subgraph :=
    (⊤ : (diagramGraph A).Subgraph).induce ({i, j} : Set B)
  have hiH : i ∈ H.verts := by
    simp [H]
  have hclosed : ∀ v ∈ H.verts, ∀ w, (diagramGraph A).Adj v w → H.Adj v w := by
    intro v hv w hvw
    have hv' : v = i ∨ v = j := by simpa [H] using hv
    rcases hv' with hv' | hv'
    · subst v
      have hw : w = j := by
        by_contra hwj
        have hiw : i ≠ w := (h.diagramGraph_adj_iff.mp hvw).1
        have hzero := h.apply_eq_zero_of_apply_mul_apply_eq_three hiw (Ne.symm hwj) hij
        exact (h.diagramGraph_adj_iff.mp hvw).2 hzero
      subst w
      simpa only [H, SimpleGraph.Subgraph.induce_adj, SimpleGraph.Subgraph.top_adj,
        Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true, true_and] using hvw
    · subst v
      have hw : w = i := by
        by_contra hwi
        have hjw : j ≠ w := (h.diagramGraph_adj_iff.mp hvw).1
        have hzero := h.apply_eq_zero_of_apply_mul_apply_eq_three hjw (Ne.symm hwi) (by
          simpa [mul_comm] using hij)
        exact (h.diagramGraph_adj_iff.mp hvw).2 hzero
      subst w
      simpa only [H, SimpleGraph.Subgraph.induce_adj, SimpleGraph.Subgraph.top_adj,
        Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true, true_and] using hvw
  have hkH : k ∈ H.verts :=
    (hconn i k).mem_subgraphVerts hclosed hiH
  simpa [H, eq_comm] using hkH

/-- **A preconnected finite-type diagram containing a triple edge has exactly two vertices.** -/
theorem card_eq_two_of_apply_mul_apply_eq_three (h : IsFiniteType A)
    (hconn : (diagramGraph A).Preconnected) {i j : B} (hij : A i j * A j i = 3) :
    Fintype.card B = 2 := by
  have hij_ne : i ≠ j := by
    rintro rfl
    rw [h.apply_self] at hij
    omega
  rw [← Nat.card_eq_fintype_card]
  refine Nat.card_eq_two_iff.mpr ⟨i, j, hij_ne, Set.eq_univ_of_forall ?_⟩
  intro k
  simpa [eq_comm] using h.eq_or_eq_of_apply_mul_apply_eq_three hconn hij k

/-- **The triple-edge branch of the finite-type classification is `G₂`.**

For a preconnected finite-type matrix, a Cartan product of three first forces the index type to have
two elements.  Rank-two classification supplies its unique valid Dynkin type.  The Cartan product
is invariant under relabelling and distinguishes `G₂` from `A₂` and `B₂`. -/
theorem exists_equiv_cartanMatrix_eq_G2_of_apply_mul_apply_eq_three (h : IsFiniteType A)
    (hconn : (diagramGraph A).Preconnected) {i j : B} (hij : A i j * A j i = 3) :
    ∃ e : B ≃ Fin DynkinType.G2.rank,
      ∀ x y, A x y = DynkinType.G2.cartanMatrix (e x) (e y) := by
  have hij_ne : i ≠ j := by
    rintro rfl
    rw [h.apply_self] at hij
    omega
  have hcard := h.card_eq_two_of_apply_mul_apply_eq_three hconn hij
  have hnonzero : ∀ x y : B, x ≠ y → A x y ≠ 0 := by
    intro x y hxy
    have hxi := h.eq_or_eq_of_apply_mul_apply_eq_three hconn hij x
    have hyi := h.eq_or_eq_of_apply_mul_apply_eq_three hconn hij y
    rcases hxi with rfl | rfl <;> rcases hyi with rfl | rfl
    · exact absurd rfl hxy
    · exact fun hzero ↦ by rw [hzero] at hij; norm_num at hij
    · exact fun hzero ↦ by rw [hzero] at hij; norm_num at hij
    · exact absurd rfl hxy
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ :=
    h.existsUnique_dynkinType_of_card_eq_two hcard hnonzero
  have hrank : t.rank = 2 := by
    rw [← Fintype.card_fin t.rank, ← Fintype.card_congr e]
    exact hcard
  rcases DynkinType.valid_and_rank_eq_two_iff.mp ⟨ht, hrank⟩ with rfl | rfl | rfl
  · have hprod := Matrix.mul_apply_mul_apply_eq_of_equiv_fin_two e he hij_ne
    rw [DynkinType.cartanMatrix_A_two_eq] at hprod
    norm_num at hprod
    omega
  · have hprod := Matrix.mul_apply_mul_apply_eq_of_equiv_fin_two e he hij_ne
    rw [DynkinType.cartanMatrix_B_two_eq] at hprod
    norm_num at hprod
    omega
  · exact ⟨e, he⟩

/-- **A preconnected finite-type matrix contains a triple edge exactly when it has type `G₂`.**

The right side uses the same simultaneous row-and-column relabelling as `HasCartanType`.  No
orientation is imposed on the witness edge on the left: reversing its endpoints does not change
the Cartan product. -/
theorem exists_apply_mul_apply_eq_three_iff_exists_equiv_cartanMatrix_eq_G2
    (h : IsFiniteType A)
    (hconn : (diagramGraph A).Preconnected) :
    (∃ i j, A i j * A j i = 3) ↔
      ∃ e : B ≃ Fin DynkinType.G2.rank,
        ∀ x y, A x y = DynkinType.G2.cartanMatrix (e x) (e y) := by
  constructor
  · rintro ⟨i, j, hij⟩
    exact h.exists_equiv_cartanMatrix_eq_G2_of_apply_mul_apply_eq_three hconn hij
  · rintro ⟨e, he⟩
    let e' : B ≃ Fin 2 := e.trans (finCongr DynkinType.rank_G2)
    have he' : ∀ x y, A x y = (!![2, -1; -3, 2] : Matrix (Fin 2) (Fin 2) ℤ) (e' x) (e' y) := by
      intro x y
      rw [he, DynkinType.cartanMatrix_G2_eq]
      congr 1
    refine ⟨e'.symm 0, e'.symm 1, ?_⟩
    rw [he', he', e'.apply_symm_apply, e'.apply_symm_apply]
    norm_num

end IsFiniteType

end TauCeti
