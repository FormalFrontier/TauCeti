/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Combinatorics.SimpleGraph.PathGraph
import Mathlib.Combinatorics.SimpleGraph.Ends.Defs

public section

/-!
# Components left by deleting a branch vertex of a tree

Deleting a vertex `c` from a tree separates it into one component for each neighbour of `c`.
When every vertex of the complement has degree at most two there, the resulting components are
paths.  This is the graph-theoretic extraction step behind the `D` and `E` branches of the
finite-type Dynkin-diagram classification.

## Main results

* `TauCeti.IsTree.neighborSetEquivConnectedComponentCompl`: the neighbours of a vertex index the
  connected components left after deleting that vertex from a tree.
* `TauCeti.IsTree.exists_equiv_pathGraph_components`: deleting a vertex of degree `n` from a finite
  tree leaves `n` components, each a path when the complement has degree at most two.

## References

See J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Section 11.4, for
the corresponding extraction in the classification of Dynkin diagrams.
-/

namespace TauCeti

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Distinct neighbours of `c` lie in distinct components of `G ∖ {c}`, whenever `G` is acyclic.

Only acyclicity is used; connectedness plays no part. -/
private theorem connectedComponentMk_neighborSet_injective (hG : G.IsAcyclic) (c : V) :
    Function.Injective fun x : ↥(G.neighborSet c) =>
      (G.induce ({c}ᶜ : Set V)).connectedComponentMk
        ⟨(x : V), Set.mem_compl_singleton_iff.mpr (G.ne_of_adj x.property).symm⟩ := by
  classical
  -- A path outside `c` between two different neighbours, together with the two edges through
  -- `c`, would give two paths between the same endpoints.
  intro x y hxy
  let H : SimpleGraph ↥({c}ᶜ : Set V) := G.induce ({c}ᶜ : Set V)
  let toCompl : ↥(G.neighborSet c) -> ↥({c}ᶜ : Set V) := fun x =>
    ⟨x, Set.mem_compl_singleton_iff.mpr (G.ne_of_adj x.property).symm⟩
  have hreach : H.Reachable (toCompl x) (toCompl y) := ConnectedComponent.exact hxy
  let q : H.Path (toCompl x) (toCompl y) := hreach.some.toPath
  let qG : G.Path x y := q.map (Embedding.induce (G := G) ({c}ᶜ : Set V)).toHom
    (Embedding.induce (G := G) ({c}ᶜ : Set V)).injective
  have hcq : c ∉ qG.val.support := by
    intro hc
    -- Unfold the mapped path while retaining its coerced endpoints, so the walk-level
    -- `support_map` lemma applies.
    change c ∈ (q.val.map (Embedding.induce (G := G) ({c}ᶜ : Set V)).toHom).support at hc
    rw [Walk.support_map] at hc
    obtain ⟨z, -, hz⟩ := List.mem_map.mp hc
    exact z.property (by simpa using hz)
  have hxadj : G.Adj c x := x.property
  have hyadj : G.Adj c y := y.property
  have hxc : (x : V) ≠ c := (G.ne_of_adj hxadj).symm
  by_contra hne
  have hxyv : (x : V) ≠ y := fun h => hne (Subtype.ext h)
  have hyc : c ≠ (y : V) := G.ne_of_adj hyadj
  let r : G.Walk x y := .cons hxadj.symm (.cons hyadj .nil)
  have hr : r.IsPath := by
    apply Walk.IsPath.mk'
    simp [r, hxc, hxyv, hyc]
  have heq := hG.subsingleton_path x y |>.elim qG ⟨r, hr⟩
  have hsupp := congrArg (fun p : G.Path x y => p.val.support) heq
  exact hcq (by rw [hsupp]; simp [r])

/-- Every component of `G ∖ {c}` contains a neighbour of `c`, whenever `G` is preconnected.

Only preconnectedness is used; acyclicity plays no part. -/
private theorem connectedComponentMk_neighborSet_surjective (hG : G.Preconnected) (c : V) :
    Function.Surjective fun x : ↥(G.neighborSet c) =>
      (G.induce ({c}ᶜ : Set V)).connectedComponentMk
        ⟨(x : V), Set.mem_compl_singleton_iff.mpr (G.ne_of_adj x.property).symm⟩ := by
  classical
  intro C
  obtain ⟨⟨a, z⟩, haC, hzc, haz⟩ :=
    ComponentCompl.exists_adj_boundary_pair (G := G) (K := {c})
      hG (Set.singleton_nonempty c) C
  have hzc' : z = c := Set.mem_singleton_iff.mp hzc
  subst z
  refine ⟨⟨a, haz.symm⟩, ?_⟩
  rw [← haC.choose_spec]

/-- **The components of a tree with one vertex deleted are indexed by its neighbours.**

The forward map sends a neighbour of `c` to the component of the graph induced on `{c}ᶜ` that
contains it; the inverse sends a component to the unique neighbour of `c` that it contains. -/
noncomputable def IsTree.neighborSetEquivConnectedComponentCompl (hG : G.IsTree) (c : V) :
    ↥(G.neighborSet c) ≃ (G.induce ({c}ᶜ : Set V)).ConnectedComponent :=
  Equiv.ofBijective _
    ⟨connectedComponentMk_neighborSet_injective hG.isAcyclic c,
      connectedComponentMk_neighborSet_surjective hG.connected.preconnected c⟩

/-- The equivalence sends a neighbour to the connected component containing that neighbour. -/
@[simp] theorem IsTree.neighborSetEquivConnectedComponentCompl_apply (hG : G.IsTree) (c : V)
    (x : ↥(G.neighborSet c)) :
    TauCeti.IsTree.neighborSetEquivConnectedComponentCompl hG c x =
      (G.induce ({c}ᶜ : Set V)).connectedComponentMk
        ⟨x, Set.mem_compl_singleton_iff.mpr (G.ne_of_adj x.property).symm⟩ := by
  rfl

/-- **Deleting a vertex of degree `n` from a finite tree leaves `n` components, and they are paths
as soon as the complement has degree at most two.**

The equivalence `e` records which component begins at each neighbour of `c`.  The second conclusion
is deliberately componentwise: each component carries its own natural path length, which is the arm
length used in the subsequent reindexing onto a star. -/
theorem IsTree.exists_equiv_pathGraph_components [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.IsTree) (c : V) {n : ℕ} (hc : G.degree c = n)
    (hdeg : ∀ v, (G.induce ({c}ᶜ : Set V)).degree v ≤ 2) :
    ∃ e : Fin n ≃ (G.induce ({c}ᶜ : Set V)).ConnectedComponent,
      ∀ i, Nonempty ((e i).toSimpleGraph ≃g
        pathGraph (Nat.card ↥(ConnectedComponent.supp (e i)))) := by
  let H : SimpleGraph ↥({c}ᶜ : Set V) := G.induce ({c}ᶜ : Set V)
  have hcard : Fintype.card ↥(G.neighborSet c) = n := by
    rw [card_neighborSet_eq_degree, hc]
  let e := (Fintype.equivFinOfCardEq hcard).symm.trans
    (TauCeti.IsTree.neighborSetEquivConnectedComponentCompl hG c)
  refine ⟨e, fun i => ?_⟩
  let _ : Fintype ↥(ConnectedComponent.supp (e i)) := Fintype.ofFinite _
  let _ : DecidableRel (e i).toSimpleGraph.Adj := Classical.decRel _
  have hH : H.IsAcyclic := hG.isAcyclic.comap
    (Embedding.induce (G := G) ({c}ᶜ : Set V)).toHom
    (Embedding.induce (G := G) ({c}ᶜ : Set V)).injective
  have hdegree (v : ↥(ConnectedComponent.supp (e i))) : (e i).toSimpleGraph.degree v ≤ 2 :=
    le_trans (((e i).toSimpleGraph_hom.toCopy Subtype.val_injective).degree_le v) (hdeg v.val)
  rw [Nat.card_eq_fintype_card]
  exact TauCeti.IsTree.nonempty_iso_pathGraph_of_degree_le_two
    (hH.isTree_connectedComponent (e i)) hdegree

end TauCeti
