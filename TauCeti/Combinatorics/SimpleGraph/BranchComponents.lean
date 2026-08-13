/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Combinatorics.SimpleGraph.PathGraph

public section

/-!
# Components left by deleting a branch vertex of a tree

Deleting a vertex `c` from a tree separates it into one component for each neighbour of `c`.
When `c` has degree three and every other vertex has degree at most two, the three resulting
components are paths.  This is the graph-theoretic extraction step
behind the `D` and `E` branches of the finite-type Dynkin-diagram classification.

## Main results

* `TauCeti.IsTree.neighborFinsetEquivConnectedComponentCompl`: the neighbours of a vertex index the
  connected components left after deleting that vertex from a finite tree.
* `TauCeti.IsTree.exists_three_path_components`: deleting the unique degree-three vertex leaves
  exactly three path components.

## References

See J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Section 11.4, for
the corresponding extraction in the classification of Dynkin diagrams.
-/

namespace TauCeti

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

-- `Set.compl` is the protected complement constructor, so its membership rule is not the simp
-- theorem for the typeclass-based complement notation.
private lemma mem_compl_singleton_iff {x c : V} :
    x ∈ Set.compl ({c} : Set V) ↔ x ≠ c := by
  rfl

/-- **The components of a tree with one vertex deleted are indexed by its neighbours.**

The forward map sends a neighbour of `c` to its component in the induced graph on `{c}ᶜ`.
Injectivity is acyclicity: a path outside `c` between two different neighbours, together with the
two edges through `c`, would give two paths between the same endpoints.  Surjectivity follows by
taking the first edge of the unique path from `c` to a vertex of the component. -/
noncomputable def IsTree.neighborFinsetEquivConnectedComponentCompl [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hG : G.IsTree) (c : V) :
    ↥(G.neighborFinset c) ≃ (G.induce (Set.compl {c})).ConnectedComponent := by
  let H : SimpleGraph (Set.compl {c}) := G.induce (Set.compl {c})
  let toCompl : ↥(G.neighborFinset c) -> Set.compl {c} := fun x =>
    ⟨x, by
      rw [mem_compl_singleton_iff]
      exact (G.ne_of_adj ((G.mem_neighborFinset c x).mp x.property)).symm⟩
  let f : ↥(G.neighborFinset c) -> H.ConnectedComponent := fun x =>
    H.connectedComponentMk (toCompl x)
  apply Equiv.ofBijective f
  constructor
  · intro x y hxy
    have hreach : H.Reachable (toCompl x) (toCompl y) := ConnectedComponent.exact hxy
    let q : H.Path (toCompl x) (toCompl y) := hreach.some.toPath
    let qG : G.Path x y := q.map (Embedding.induce (G := G) (Set.compl {c})).toHom
      (Embedding.induce (G := G) (Set.compl {c})).injective
    have hcq : c ∉ qG.val.support := by
      intro hc
      -- Unfold the mapped path while retaining its coerced endpoints, so the walk-level
      -- `support_map` lemma applies.
      change c ∈ (q.val.map (Embedding.induce (G := G) (Set.compl {c})).toHom).support at hc
      rw [Walk.support_map] at hc
      obtain ⟨z, -, hz⟩ := List.mem_map.mp hc
      exact z.property (by simpa using hz)
    have hxadj : G.Adj c x := (G.mem_neighborFinset c x).mp x.property
    have hyadj : G.Adj c y := (G.mem_neighborFinset c y).mp y.property
    have hxc : x ≠ c := (G.ne_of_adj hxadj).symm
    have hxy' : x = y := by
      by_contra hne
      have hxyv : (x : V) ≠ y := fun h => hne (Subtype.ext h)
      have hyc : c ≠ (y : V) := G.ne_of_adj hyadj
      let r : G.Walk x y := .cons hxadj.symm (.cons hyadj .nil)
      have hr : r.IsPath := by
        apply Walk.IsPath.mk'
        simp [r, hxc, hxyv, hyc]
      have heq := hG.isAcyclic.subsingleton_path x y |>.elim qG ⟨r, hr⟩
      have hsupp := congrArg (fun p : G.Path x y => p.val.support) heq
      have : c ∈ qG.val.support := by
        rw [hsupp]
        simp [r]
      exact hcq this
    exact hxy'
  · intro C
    obtain ⟨z, hz⟩ := C.nonempty_supp
    let p : G.Path c z := (hG.connected.preconnected c z).some.toPath
    have hcz : c ≠ z := by
      have hz' : (z : V) ≠ c := z.property
      exact hz'.symm
    have hpnon : ¬p.val.Nil := Walk.not_nil_of_ne hcz
    let a : V := p.val.snd
    have hca : G.Adj c a := p.val.adj_snd hpnon
    let aN : ↥(G.neighborFinset c) := ⟨a, (G.mem_neighborFinset c a).mpr hca⟩
    have htailc : c ∉ p.val.tail.support := by
      have hnodup := p.isPath.support_nodup
      rw [← p.val.cons_tail_support] at hnodup
      rw [p.val.support_tail_of_not_nil hpnon]
      exact (List.nodup_cons.mp hnodup).1
    have htailS : ∀ x ∈ p.val.tail.support, x ∈ Set.compl ({c} : Set V) := by
      intro x hx
      rw [mem_compl_singleton_iff]
      exact fun h => htailc (h ▸ hx)
    let pt := p.val.tail.induce (Set.compl {c}) htailS
    have hstart :
        (⟨p.val.snd, htailS _ p.val.tail.start_mem_support⟩ : Set.compl {c}) = toCompl aN :=
      Subtype.ext rfl
    have hend :
        (⟨z, htailS _ p.val.tail.end_mem_support⟩ : Set.compl {c}) = z := Subtype.ext rfl
    refine ⟨aN, ?_⟩
    dsimp only [f]
    rw [← (C.mem_supp_iff z).mp hz]
    apply ConnectedComponent.sound
    exact ⟨pt.copy hstart hend⟩

/-- The equivalence sends a neighbour to the connected component containing that neighbour. -/
@[simp] theorem IsTree.neighborFinsetEquivConnectedComponentCompl_apply [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hG : G.IsTree) (c : V) (x : ↥(G.neighborFinset c)) :
    TauCeti.IsTree.neighborFinsetEquivConnectedComponentCompl hG c x =
      (G.induce (Set.compl {c})).connectedComponentMk
        ⟨x, by
          rw [mem_compl_singleton_iff]
          exact (G.ne_of_adj ((G.mem_neighborFinset c x).mp x.property)).symm⟩ := by
  rfl

/-- **Deleting a degree-three vertex of a finite tree leaves three path components when every other
vertex has degree at most two.**

The equivalence `e` records which component begins at each of the three neighbours of `c`.  The
second conclusion is deliberately componentwise: each component carries its own natural path
length, which is the arm length used in the subsequent reindexing onto a three-arm star. -/
theorem IsTree.exists_three_path_components [Fintype V] [DecidableRel G.Adj]
    (hG : G.IsTree) (c : V) (hc : G.degree c = 3)
    (hdeg : ∀ v, v ≠ c -> G.degree v ≤ 2) :
    ∃ e : Fin 3 ≃ (G.induce (Set.compl {c})).ConnectedComponent,
      ∀ i, Nonempty ((e i).toSimpleGraph ≃g pathGraph (Nat.card (e i))) := by
  classical
  have hcard : (G.neighborFinset c).card = 3 := by simpa only [degree] using hc
  let ne : Fin 3 ≃ ↥(G.neighborFinset c) := (Finset.equivFinOfCardEq hcard).symm
  let e := ne.trans (TauCeti.IsTree.neighborFinsetEquivConnectedComponentCompl hG c)
  refine ⟨e, fun i => ?_⟩
  let H : SimpleGraph (Set.compl {c}) := G.induce (Set.compl {c})
  let _ : Fintype (e i) := Fintype.ofFinite _
  have hH : H.IsAcyclic := hG.isAcyclic.comap
    (Embedding.induce (G := G) (Set.compl {c})).toHom
    (Embedding.induce (G := G) (Set.compl {c})).injective
  have hdegree (v : e i) : (e i).toSimpleGraph.degree v ≤ 2 := by
    have hleC : (e i).toSimpleGraph.degree v ≤ H.degree v.val := by
      exact ((e i).toSimpleGraph_hom.toCopy Subtype.val_injective).degree_le v
    have hleH : H.degree v.val ≤ G.degree v.val.val := by
      exact (SimpleGraph.Copy.induce G (Set.compl {c})).degree_le v.val
    have hvG : G.degree v.val.val ≤ 2 := hdeg v.val.val v.val.property
    omega
  rw [Nat.card_eq_fintype_card]
  exact TauCeti.IsTree.nonempty_iso_pathGraph_of_degree_le_two
    (hH.isTree_connectedComponent (e i)) hdegree

end TauCeti
