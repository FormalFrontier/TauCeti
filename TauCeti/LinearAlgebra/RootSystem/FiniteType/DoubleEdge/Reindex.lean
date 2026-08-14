/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import TauCeti.Combinatorics.SimpleGraph.PathGraph
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.DoubleEdge.Basic

public section

/-!
# Reindexing path-shaped diagrams with a double edge

The classification of the model matrices `TauCeti.doubleEdgeCartanMatrix p q` is already known:
when both chains are nonempty, finite type leaves precisely the families `B_n`, `C_n`, and the
exceptional type `F_4`. To apply that result to an arbitrary Cartan matrix, its diagram must first
be reindexed onto the model.

This file performs that reindexing for the branchless case. A connected finite-type diagram in
which every vertex has degree at most two is a path. After orienting the path so that a chosen
double edge points from `-1` to `-2`, cutting at that edge gives two nonempty chains. If this is the
only double edge, every other edge is simple, so the matrix itself -- not merely its underlying
graph -- is `TauCeti.doubleEdgeCartanMatrix p q` after one simultaneous relabelling.

## Main result

* `TauCeti.IsFiniteType.exists_equiv_forall_eq_doubleEdgeCartanMatrix`: a connected finite-type
  matrix of maximum degree two, with a unique chosen double edge, reindexes to a nonempty
  `TauCeti.doubleEdgeCartanMatrix p q`.

This is the reindexing bridge in the double-edge branch of the classification of finite-type
Cartan matrices, Layer 5 of `TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. The
remaining global assembly must prove that a connected diagram containing a double edge has no
branch vertex and has no second double edge. See J. E. Humphreys, *Introduction to Lie Algebras
and Representation Theory*, section 11.4, and Bourbaki, *Lie Groups and Lie Algebras, Chapters
4--6*, Chapter VI, section 4.
-/

namespace TauCeti

open SimpleGraph

variable {B : Type*} [Fintype B] {A : Matrix B B ℤ}

/-- The path ordering of two chains joined at their last vertices. The first chain is read from
its outside vertex toward the double edge, and the second from the double edge toward its outside
vertex. -/
private def doubleEdgePathEquiv (p q n : ℕ) (hpq : p + q = n) :
    Fin p ⊕ Fin q ≃ Fin n :=
  (Equiv.sumCongr (Equiv.refl _) Fin.revPerm).trans finSumFinEquiv |>.trans (finCongr hpq)

@[simp] private lemma doubleEdgePathEquiv_inl_val (p q n : ℕ) (hpq : p + q = n)
    (i : Fin p) : (doubleEdgePathEquiv p q n hpq (Sum.inl i) : ℕ) = i := by
  simp [doubleEdgePathEquiv]

@[simp] private lemma doubleEdgePathEquiv_inr_val (p q n : ℕ) (hpq : p + q = n)
    (i : Fin q) :
    (doubleEdgePathEquiv p q n hpq (Sum.inr i) : ℕ) = p + (q - 1 - i) := by
  simp [doubleEdgePathEquiv, Fin.rev]
  omega

/-- Reversal is an automorphism of a finite path graph. -/
private def pathGraphRevIso (n : ℕ) : pathGraph n ≃g pathGraph n where
  toEquiv := Fin.revPerm
  map_rel_iff' := by
    intro i j
    simp only [pathGraph_adj, Fin.revPerm_apply, Fin.rev]
    omega

@[simp] private lemma pathGraphRevIso_apply {n : ℕ} (i : Fin n) :
    pathGraphRevIso n i = i.rev := rfl

/-- The entries of a double-edge model, read along its underlying path. The only oriented
exception to the value `-1` on adjacent vertices is the `-2` half of the double edge. -/
private lemma doubleEdgeCartanMatrix_apply_eq_path (p q n : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hpq : p + q = n) (x y : Fin p ⊕ Fin q) :
    doubleEdgeCartanMatrix p q x y =
      if x = y then 2
      else if x = Sum.inr ⟨q - 1, by omega⟩ ∧ y = Sum.inl ⟨p - 1, by omega⟩ then -2
      else if (doubleEdgePathEquiv p q n hpq x : ℕ) + 1 =
          (doubleEdgePathEquiv p q n hpq y : ℕ) ∨
          (doubleEdgePathEquiv p q n hpq y : ℕ) + 1 =
            (doubleEdgePathEquiv p q n hpq x : ℕ) then -1 else 0 := by
  rcases x with x | x <;> rcases y with y | y <;>
    simp only [doubleEdgeCartanMatrix_inl_inl, doubleEdgeCartanMatrix_inr_inr,
      doubleEdgeCartanMatrix_inl_inr, doubleEdgeCartanMatrix_inr_inl, Sum.inl.injEq,
      Sum.inr.injEq, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
      false_and, and_false, ite_false, doubleEdgePathEquiv_inl_val,
      doubleEdgePathEquiv_inr_val, Fin.ext_iff]
  · have hx := x.isLt
    have hy := y.isLt
    rw [chainEntry_def]
    split_ifs <;> omega
  · have hx := x.isLt
    have hy := y.isLt
    split_ifs <;> omega
  · have hx := x.isLt
    have hy := y.isLt
    split_ifs <;> omega
  · have hx := x.isLt
    have hy := y.isLt
    have hxle : (x : ℕ) ≤ q - 1 := by omega
    have hyle : (y : ℕ) ≤ q - 1 := by omega
    rw [chainEntry_def]
    split_ifs <;> omega

/-- The reindexing theorem with an already oriented path numbering. -/
private theorem exists_equiv_forall_eq_doubleEdgeCartanMatrix_of_pathEquiv
    (h : IsFiniteType A) (k : B ≃ Fin n)
    (hk : ∀ i j, (diagramGraph A).Adj i j ↔
      (k i : ℕ) + 1 = (k j : ℕ) ∨ (k j : ℕ) + 1 = (k i : ℕ))
    {u v : B} (horder : (k u : ℕ) + 1 = (k v : ℕ)) (hvu : A v u = -2)
    (hsimple : ∀ {i j}, i ≠ j → A i j ≠ 0 → (i = v ∧ j = u) ∨ A i j = -1) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ ∃ e : B ≃ Fin p ⊕ Fin q,
      ∀ i j, A i j = doubleEdgeCartanMatrix p q (e i) (e j) := by
  let p := (k u : ℕ) + 1
  let q := n - p
  -- Cutting immediately after `u` leaves two nonempty intervals, since `v` is its successor.
  have hp : 0 < p := by simp [p]
  have hp_le : p ≤ n := by simp only [p]; omega
  have hpq : p + q = n := Nat.add_sub_of_le hp_le
  have hq : 0 < q := by
    simp only [q]
    omega
  let e : B ≃ Fin p ⊕ Fin q := k.trans (doubleEdgePathEquiv p q n hpq).symm
  have hge (i : B) : doubleEdgePathEquiv p q n hpq (e i) = k i := by simp [e]
  -- The two endpoints of the cut become the last vertices of the two model chains.
  have heu : e u = Sum.inl ⟨p - 1, by omega⟩ := by
    apply (doubleEdgePathEquiv p q n hpq).injective
    rw [hge]
    apply Fin.ext
    simp [p]
  have hev : e v = Sum.inr ⟨q - 1, by omega⟩ := by
    apply (doubleEdgePathEquiv p q n hpq).injective
    rw [hge]
    apply Fin.ext
    simp [p, q]
    omega
  refine ⟨p, q, hp, hq, e, fun i j ↦ ?_⟩
  -- Read both matrices along the same path. Equality, the exceptional oriented edge, and
  -- adjacency are all reflected by `e`; the finite-type axioms then determine the entry.
  rw [doubleEdgeCartanMatrix_apply_eq_path p q n hp hq hpq, ← hev, ← heu]
  have hrev : (e i = e v ∧ e j = e u) ↔ (i = v ∧ j = u) :=
    and_congr e.injective.eq_iff e.injective.eq_iff
  have hadj : ((doubleEdgePathEquiv p q n hpq (e i) : ℕ) + 1 =
      (doubleEdgePathEquiv p q n hpq (e j) : ℕ) ∨
      (doubleEdgePathEquiv p q n hpq (e j) : ℕ) + 1 =
        (doubleEdgePathEquiv p q n hpq (e i) : ℕ)) ↔ (diagramGraph A).Adj i j := by
    rw [hge, hge, hk]
  rcases eq_or_ne i j with rfl | hij
  · rw [ite_eq_left rfl, h.apply_self]
  have heij : e i ≠ e j := fun he ↦ hij (e.injective he)
  rw [ite_eq_right heij]
  by_cases hpair : i = v ∧ j = u
  · rcases hpair with ⟨rfl, rfl⟩
    rw [ite_eq_left (hrev.mpr ⟨rfl, rfl⟩), hvu]
  have hpair' := fun hp ↦ hpair (hrev.mp hp)
  rw [ite_eq_right hpair']
  by_cases ha : (diagramGraph A).Adj i j
  · rw [ite_eq_left (hadj.mpr ha)]
    have hne : A i j ≠ 0 := (h.diagramGraph_adj_iff.mp ha).2
    exact (hsimple hij hne).resolve_left hpair
  · rw [ite_eq_right (fun hp ↦ ha (hadj.mp hp))]
    by_contra hne
    exact ha (h.diagramGraph_adj_iff.mpr ⟨hij, hne⟩)

/-- **A path-shaped finite-type matrix with one oriented double edge is a double-edge model.**
Suppose the diagram is connected, every vertex has degree at most two, the edge `u -- v` carries
`A v u = -2`, and that entry is the only nonzero off-diagonal entry that is not `-1`. Then there
are nonempty chains of lengths `p` and `q` and a simultaneous relabelling under which `A` is
`TauCeti.doubleEdgeCartanMatrix p q`.

The hypothesis on off-diagonal entries is the matrix form of saying that the chosen edge is the
only multiple edge; in particular it already forces the opposite entry `A u v` to be `-1`. The
global classification supplies it by excluding two multiple edges along a chain; this theorem
performs the subsequent reindexing. -/
theorem IsFiniteType.exists_equiv_forall_eq_doubleEdgeCartanMatrix [DecidableEq B]
    (h : IsFiniteType A)
    (hconn : (diagramGraph A).Connected) (hdeg : ∀ i, (diagramGraph A).degree i ≤ 2)
    {u v : B} (hvu : A v u = -2)
    (hsimple : ∀ {i j}, i ≠ j → A i j ≠ 0 → (i = v ∧ j = u) ∨ A i j = -1) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ ∃ e : B ≃ Fin p ⊕ Fin q,
      ∀ i j, A i j = doubleEdgeCartanMatrix p q (e i) (e j) := by
  obtain ⟨iso⟩ := IsTree.nonempty_iso_pathGraph_of_degree_le_two
    (h.isTree_diagramGraph hconn) hdeg
  -- Adjacency read through any numbering of the diagram as a path.
  have hnum : ∀ (m : ℕ) (f : diagramGraph A ≃g pathGraph m) (i j : B),
      (diagramGraph A).Adj i j ↔ (f i : ℕ) + 1 = (f j : ℕ) ∨ (f j : ℕ) + 1 = (f i : ℕ) :=
    fun _ f i j ↦ by simpa only [pathGraph_adj] using f.map_adj_iff.symm
  have hvu_ne : v ≠ u := by
    rintro rfl
    rw [h.apply_self] at hvu
    omega
  have hadj : (diagramGraph A).Adj u v :=
    (h.diagramGraph_adj_iff.mpr ⟨hvu_ne, by simp [hvu]⟩).symm
  have hpath : (iso u : ℕ) + 1 = (iso v : ℕ) ∨ (iso v : ℕ) + 1 = (iso u : ℕ) := by
    rwa [← iso.map_adj_iff, pathGraph_adj] at hadj
  rcases hpath with horder | horder
  · exact exists_equiv_forall_eq_doubleEdgeCartanMatrix_of_pathEquiv h iso.toEquiv
      (hnum _ iso) horder hvu hsimple
  · let iso' : diagramGraph A ≃g pathGraph (Fintype.card B) :=
      iso.trans (pathGraphRevIso (Fintype.card B))
    have horder' : (iso' u : ℕ) + 1 = (iso' v : ℕ) := by
      simp only [iso', RelIso.trans_apply, pathGraphRevIso_apply, Fin.val_rev]
      have hu := (iso u).isLt
      have hv := (iso v).isLt
      omega
    exact exists_equiv_forall_eq_doubleEdgeCartanMatrix_of_pathEquiv h iso'.toEquiv
      (hnum _ iso') horder' hvu hsimple

end TauCeti
