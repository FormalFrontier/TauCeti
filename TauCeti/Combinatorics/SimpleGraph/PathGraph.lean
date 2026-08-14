/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Hasse

public section

/-!
# A finite tree of maximum degree two is a path graph

A finite connected graph in which every vertex has at most two neighbours is a path or a cycle, and
acyclicity leaves the path. This file proves that identification in the form a consumer wants: a
finite tree of maximum degree two is isomorphic to Mathlib's `SimpleGraph.pathGraph` on as many
vertices as it has, so its vertices can be numbered `0, …, n - 1` with two of them adjacent exactly
when their numbers are consecutive.

The proof takes a path `p` of greatest length in the graph, which Mathlib's
`SimpleGraph.exists_isPath_forall_isPath_length_le_length` supplies. Every neighbour of a vertex of
`p` again lies on `p`: at an interior vertex because the two neighbours along `p` already exhaust
the degree bound, and at an endpoint because a neighbour off `p` could be prepended, contradicting
maximality. The vertices of `p` therefore admit no boundary edge, so connectedness makes them all of
the vertices, and a count of edges finishes the argument: a tree has one edge fewer than it has
vertices, `p` already supplies that many distinct edges, and so every edge of the graph is an edge
of `p`. The subgraph spanned by `p` is therefore all of `G`, and Mathlib's
`SimpleGraph.Walk.IsPath.pathGraphIsoToSubgraph` identifies it with a path graph.

## Main results

* `TauCeti.IsTree.nonempty_iso_pathGraph_of_degree_le_two`: a finite tree of maximum degree two is
  isomorphic to the path graph on its vertices.
* `TauCeti.adj_iff_of_iso_pathGraph`: adjacency read through such a numbering is consecutiveness of
  the numbers.
* `TauCeti.pathGraphRevIso`: the reversal automorphism of a path graph, which reverses a numbering.

## References

The argument is the standard one; see R. Diestel, *Graph Theory*, 5th ed., Ch. 1.5, for trees and
their edge count.
-/

namespace TauCeti

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ## Numbering a graph as a path -/

/-- **Adjacency read through a numbering of a graph as a path**: two vertices are adjacent exactly
when their numbers are consecutive. -/
theorem adj_iff_of_iso_pathGraph {n : ℕ} (f : G ≃g pathGraph n) (i j : V) :
    G.Adj i j ↔ (f i : ℕ) + 1 = (f j : ℕ) ∨ (f j : ℕ) + 1 = (f i : ℕ) := by
  simpa only [pathGraph_adj] using f.map_adj_iff.symm

/-- **Reversal is an automorphism of a path graph.** Composing with it reverses a numbering of a
graph as a path. -/
@[expose] def pathGraphRevIso (n : ℕ) : pathGraph n ≃g pathGraph n where
  toEquiv := Fin.revPerm
  map_rel_iff' := by
    intro i j
    simp only [pathGraph_adj, Fin.revPerm_apply, Fin.rev]
    omega

@[simp] theorem pathGraphRevIso_apply {n : ℕ} (i : Fin n) : pathGraphRevIso n i = i.rev := rfl

/-! ## A finite tree of maximum degree two -/

/-- **A neighbour of the first vertex of a longest path lies on that path**: otherwise it could be
prepended, and the path was not longest. -/
private lemma mem_support_of_adj_start {u v x : V} {p : G.Walk u v} (hp : p.IsPath)
    (hmax : ∀ (a b : V) (q : G.Walk a b), q.IsPath → q.length ≤ p.length) (hadj : G.Adj x u) :
    x ∈ p.support := by
  classical
  by_contra hx
  have hcons : (Walk.cons hadj p).IsPath := (Walk.cons_isPath_iff hadj p).mpr ⟨hp, hx⟩
  have hle := hmax x v _ hcons
  rw [Walk.length_cons] at hle
  omega

/-- **Every vertex of a connected graph of maximum degree two lies on a longest path.** An interior
vertex of the path already has two neighbours on it, an endpoint has all of its neighbours on it by
maximality, so the vertices of the path admit no boundary edge and connectedness forces them to be
all of the vertices. -/
private lemma forall_mem_support_of_degree_le_two [Fintype V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hdeg : ∀ x, G.degree x ≤ 2) {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    (hmax : ∀ (a b : V) (q : G.Walk a b), q.IsPath → q.length ≤ p.length) (x : V) :
    x ∈ p.support := by
  classical
  by_contra hx
  -- A walk from the first vertex of `p` to `x` crosses out of the vertices of `p`.
  obtain ⟨d, -, ha, hb⟩ := ((hconn.preconnected u x).some).exists_boundary_dart
    {y | y ∈ p.support} (Walk.start_mem_support p) hx
  set a := d.toProd.1 with hadef
  set b := d.toProd.2 with hbdef
  have hab : G.Adj a b := d.adj
  obtain ⟨i, hi, hile⟩ := Walk.mem_support_iff_exists_getVert.mp ha
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · rw [Walk.getVert_zero] at hi
    refine hb (mem_support_of_adj_start hp hmax ?_)
    rw [hi]
    exact hab.symm
  rcases eq_or_lt_of_le hile with hlast | hlt
  · -- `a` is the last vertex of `p`, so `b` could be appended to the reversed path.
    rw [hlast, Walk.getVert_length] at hi
    have hmax' : ∀ (c e : V) (q : G.Walk c e), q.IsPath → q.length ≤ p.reverse.length := by
      simpa only [Walk.length_reverse] using hmax
    have hbv : G.Adj b v := by rw [hi]; exact hab.symm
    have hbmem := mem_support_of_adj_start hp.reverse hmax' hbv
    rw [Walk.support_reverse, List.mem_reverse] at hbmem
    exact hb hbmem
  -- `a` is an interior vertex: its two neighbours along `p`, together with `b`, are three.
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hpath : (p.toSubgraph.neighborSet a).ncard = 2 := by
    rw [← hi]
    exact hp.ncard_neighborSet_toSubgraph_internal_eq_two (by omega) (by omega)
  have hbnot : b ∉ p.toSubgraph.neighborSet a := fun hba ↦
    hb (p.mem_verts_toSubgraph.mp (p.toSubgraph.neighborSet_subset_verts a hba))
  have hsub : insert b (p.toSubgraph.neighborSet a) ⊆ G.neighborSet a :=
    Set.insert_subset hab (p.toSubgraph.neighborSet_subset a)
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hcard : (insert b (p.toSubgraph.neighborSet a)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem hbnot, hpath]
  have hdeg' : (G.neighborSet a).ncard = G.degree a := by
    rw [← Set.fintypeCard_eq_ncard, card_neighborSet_eq_degree]
  have hda := hdeg a
  omega

/-- **A finite tree of maximum degree two is a path graph.** Its vertices can be numbered
`0, …, n - 1` so that two of them are adjacent exactly when their numbers are consecutive.

Both hypotheses are needed: a cycle graph is connected with every degree two and is not a path, and
a star with three arms is a tree that is not one. -/
theorem IsTree.nonempty_iso_pathGraph_of_degree_le_two [Fintype V] [DecidableRel G.Adj]
    (hG : G.IsTree) (hdeg : ∀ x, G.degree x ≤ 2) :
    Nonempty (G ≃g pathGraph (Fintype.card V)) := by
  classical
  have : Nonempty V := hG.connected.nonempty
  obtain ⟨u, v, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  have hsupp : ∀ x : V, x ∈ p.support :=
    forall_mem_support_of_degree_le_two hG.connected hdeg hp hmax
  -- The path is spanning, so it has as many vertices as the graph.
  have hpHam := hp.isHamiltonian_of_mem hsupp
  have hcard : p.length + 1 = Fintype.card V := by
    rw [← p.length_support, hpHam.length_support]
  -- A tree has one edge fewer than it has vertices, and the path already has that many.
  have hedges : ∀ {a b : V}, G.Adj a b → s(a, b) ∈ p.edges := by
    have hsub : p.edges.toFinset ⊆ G.edgeFinset := by
      intro e he
      rw [List.mem_toFinset] at he
      exact SimpleGraph.mem_edgeFinset.mpr (p.edges_subset_edgeSet he)
    have hpe : p.edges.toFinset.card = p.length := by
      rw [List.toFinset_card_of_nodup (Walk.edges_nodup_of_support_nodup hp.support_nodup),
        Walk.length_edges]
    have hGe : G.edgeFinset.card + 1 = Fintype.card V := hG.card_edgeFinset
    have heq : p.edges.toFinset = G.edgeFinset := Finset.eq_of_subset_of_card_le hsub (by omega)
    intro a b hab
    rw [← List.mem_toFinset, heq]
    exact SimpleGraph.mem_edgeFinset.mpr hab
  -- The path spans every vertex and every edge, so the subgraph it traverses is all of `G`.
  have htop : p.toSubgraph = ⊤ := by
    refine Subgraph.ext (Set.ext fun x ↦ ?_) ?_
    · simpa [Walk.mem_verts_toSubgraph] using hsupp x
    · ext a b
      simp only [Subgraph.top_adj]
      exact ⟨fun h ↦ h.adj_sub, fun h ↦ Walk.adj_toSubgraph_iff_mem_edges.mpr (hedges h)⟩
  have hiso : p.toSubgraph.coe ≃g G := by rw [htop]; exact Subgraph.topIso
  rw [← hcard]
  exact ⟨(hp.pathGraphIsoToSubgraph.trans hiso).symm⟩

end TauCeti
