/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Hasse

public section

/-!
# A finite tree of maximum degree two is a path graph

A finite connected graph in which every vertex has at most two neighbours is a path or a cycle, and
acyclicity leaves the path. This file proves that identification in the form a consumer wants: a
finite tree of maximum degree two is isomorphic to Mathlib's `SimpleGraph.pathGraph` on as many
vertices as it has, so its vertices can be numbered `0, …, n - 1` with two of them adjacent exactly
when their numbers are consecutive.

The proof takes a path `p` of greatest length in the graph, which exists because every path is
shorter than the number of vertices. Every neighbour of a vertex of `p` again lies on `p`: at an
interior vertex because the two neighbours along `p` already exhaust the degree bound, and at an
endpoint because a neighbour off `p` could be prepended, contradicting maximality. The vertices of
`p` therefore admit no boundary edge, so connectedness makes them all of the vertices, and a count
of edges finishes the argument: a tree has one edge fewer than it has vertices, `p` already supplies
that many distinct edges, and so every edge of the graph is an edge of `p`.

## Main results

* `TauCeti.nonempty_iso_pathGraph_of_isTree_of_degree_le_two`: a finite tree of maximum degree two
  is isomorphic to the path graph on its vertices.

## References

The argument is the standard one; see R. Diestel, *Graph Theory*, 5th ed., Ch. 1.5, for trees and
their edge count.
-/

namespace TauCeti

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A path of greatest length in a finite graph. There is one because every path is shorter than
the number of vertices. -/
private lemma exists_isPath_forall_length_le [Finite V] [Nonempty V] (G : SimpleGraph V) :
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧
      ∀ (a b : V) (q : G.Walk a b), q.IsPath → q.length ≤ p.length := by
  classical
  have : Fintype V := Fintype.ofFinite V
  set S : Set ℕ := {n | ∃ (a b : V) (q : G.Walk a b), q.IsPath ∧ q.length = n} with hS
  have hne : S.Nonempty :=
    ⟨0, Classical.arbitrary V, Classical.arbitrary V, Walk.nil, Walk.IsPath.nil, rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨Fintype.card V, ?_⟩
    rintro n ⟨a, b, q, hq, rfl⟩
    exact hq.length_lt.le
  obtain ⟨u, v, p, hp, hlen⟩ := Nat.sSup_mem hne hbdd
  refine ⟨u, v, p, hp, fun a b q hq ↦ ?_⟩
  rw [hlen]
  exact le_csSup hbdd ⟨a, b, q, hq, rfl⟩

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
  have hk : G.Adj a (p.getVert k) := by
    rw [← hi]
    exact (p.adj_getVert_succ (by omega)).symm
  have hk' : G.Adj a (p.getVert (k + 2)) := by
    rw [← hi]
    exact p.adj_getVert_succ (by omega)
  have hne : p.getVert k ≠ p.getVert (k + 2) := fun hc ↦ by
    have hkle : k ≤ p.length := by omega
    have hkle' : k + 2 ≤ p.length := by omega
    have := hp.getVert_injOn hkle hkle' hc
    omega
  have hbk : b ≠ p.getVert k := fun hc ↦ hb (hc ▸ p.getVert_mem_support k)
  have hbk' : b ≠ p.getVert (k + 2) := fun hc ↦ hb (hc ▸ p.getVert_mem_support (k + 2))
  have hsub : ({p.getVert k, p.getVert (k + 2), b} : Finset V) ⊆ G.neighborFinset a := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [SimpleGraph.mem_neighborFinset]
    rcases hy with rfl | rfl | rfl
    exacts [hk, hk', hab]
  have hcard : ({p.getVert k, p.getVert (k + 2), b} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hne, hbk.symm]),
      Finset.card_insert_of_notMem (by simp [hbk'.symm]), Finset.card_singleton]
  have hle := Finset.card_le_card hsub
  have hdeg' : (G.neighborFinset a).card = G.degree a := rfl
  have hda := hdeg a
  omega

/-- **A finite tree of maximum degree two is a path graph.** Its vertices can be numbered
`0, …, n - 1` so that two of them are adjacent exactly when their numbers are consecutive.

Both hypotheses are needed: a cycle graph is connected with every degree two and is not a path, and
a star with three arms is a tree that is not one. -/
theorem nonempty_iso_pathGraph_of_isTree_of_degree_le_two [Fintype V] [DecidableRel G.Adj]
    (hG : G.IsTree) (hdeg : ∀ x, G.degree x ≤ 2) :
    Nonempty (G ≃g pathGraph (Fintype.card V)) := by
  classical
  have : Nonempty V := hG.connected.nonempty
  obtain ⟨u, v, p, hp, hmax⟩ := exists_isPath_forall_length_le G
  have hsupp : ∀ x : V, x ∈ p.support :=
    forall_mem_support_of_degree_le_two hG.connected hdeg hp hmax
  -- The path is spanning, so it has as many vertices as the graph.
  have hcard : p.length + 1 = Fintype.card V := by
    have huniv : p.support.toFinset = Finset.univ := by
      ext x
      simp [hsupp x]
    rw [← p.length_support, ← List.toFinset_card_of_nodup hp.support_nodup, huniv,
      Finset.card_univ]
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
  rw [← hcard]
  -- Numbering the vertices along the path is a bijection.
  have hinj : Set.InjOn p.getVert {i | i ≤ p.length} := hp.getVert_injOn
  have hbij : Function.Bijective fun i : Fin (p.length + 1) ↦ p.getVert i := by
    refine ⟨fun i j hij ↦ Fin.ext (hinj ?_ ?_ hij), fun x ↦ ?_⟩
    · simpa using Nat.lt_succ_iff.mp i.isLt
    · simpa using Nat.lt_succ_iff.mp j.isLt
    · obtain ⟨n, hn, hnle⟩ := Walk.mem_support_iff_exists_getVert.mp (hsupp x)
      exact ⟨⟨n, by omega⟩, hn⟩
  refine ⟨(RelIso.mk (Equiv.ofBijective _ hbij) ?_).symm⟩
  intro i j
  have hile : (i : ℕ) ≤ p.length := Nat.lt_succ_iff.mp i.isLt
  have hjle : (j : ℕ) ≤ p.length := Nat.lt_succ_iff.mp j.isLt
  change G.Adj (p.getVert i) (p.getVert j) ↔ _
  rw [pathGraph_adj]
  constructor
  · intro hadj
    have hmem := hedges hadj
    rw [← Walk.adj_toSubgraph_iff_mem_edges, Walk.toSubgraph_adj_iff] at hmem
    obtain ⟨k, hk, hklt⟩ := hmem
    have hkle : k ≤ p.length := by omega
    have hkle' : k + 1 ≤ p.length := by omega
    rw [Sym2.eq_iff] at hk
    rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (by rw [← hinj hkle hile h1, ← hinj hkle' hjle h2])
    · exact Or.inr (by rw [← hinj hkle hjle h1, ← hinj hkle' hile h2])
  · rintro (h | h)
    · have hadj := p.adj_getVert_succ (i := (i : ℕ)) (by omega)
      rwa [h] at hadj
    · have hadj := p.adj_getVert_succ (i := (j : ℕ)) (by omega)
      rw [h] at hadj
      exact hadj.symm

end TauCeti
