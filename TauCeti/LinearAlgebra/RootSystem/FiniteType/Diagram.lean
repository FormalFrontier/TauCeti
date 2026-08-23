/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Acyclic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic

public section

/-!
# The diagram of a finite-type Cartan matrix is a forest

The elimination tools of `TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic` are stated entrywise:
they say that certain patterns of nonzero entries cannot occur together. The classification of
finite-type Cartan matrices reads them as statements about a graph, the *diagram* of the matrix,
whose vertices are the indices and whose edges are the nonzero off-diagonal pairs. This file
introduces that graph and records the two global shape theorems the classification runs on: the
diagram of a finite-type matrix is **acyclic**, and every vertex of it has degree at most `3`. A
connected finite-type diagram is therefore a **tree**, with exactly one fewer edge than it has
vertices, and the Dynkin diagram of an irreducible root system is one such tree.

Acyclicity is the graph form of `TauCeti.IsFiniteType.exists_apply_succ_eq_zero`, whose statement is
about a cyclic list of indices; the list is supplied by Mathlib's characterization of acyclicity as
containing no copy of a cycle graph, `SimpleGraph.isAcyclic_iff_free_cycleGraph`. Connectedness in
the root-system case is irreducibility, which Mathlib packages as
`RootPairing.Base.induction_on_cartanMatrix`.

## Main definitions

* `TauCeti.diagramGraph`: the diagram of an integer matrix, a `SimpleGraph` on its index type,
  joining two distinct indices when the entries of the transposed pair are both nonzero.

## Main results

* `TauCeti.IsFiniteType.isAcyclic_diagramGraph`: **the diagram of a finite-type matrix is a
  forest**. The affine diagrams `Ãₙ` for `n ≥ 2`, the ones whose diagrams are cycles, are excluded
  here in one theorem.
* `TauCeti.IsFiniteType.exists_chain_of_reachable`: two vertices in the same component are joined
  by a chain of distinct indices whose consecutive matrix entries are nonzero and whose
  nonconsecutive entries vanish. This is the bridge from graph paths to the principal-submatrix
  arguments used in the classification.
* `TauCeti.IsFiniteType.degree_le_three`: **the degree bound**, in graph form.
* `TauCeti.IsFiniteType.isTree_diagramGraph` and
  `TauCeti.IsFiniteType.card_edgeFinset_add_one_eq_card`: a connected finite-type diagram is a tree,
  and so has one fewer edge than it has vertices.
* `TauCeti.isTree_diagramGraph_cartanMatrix` and
  `TauCeti.card_edgeFinset_add_one_eq_card_support`: **the Dynkin diagram of an irreducible reduced
  crystallographic finite root system is a tree**, whose edges number one fewer than its simple
  roots. Connectedness is `TauCeti.preconnected_diagramGraph_cartanMatrix`.

## References

This file supplies the "no cycles" and "`n - 1` edges" steps of the classification of finite-type
Cartan matrices, Layer 5 of `TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. See
J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §11.4, where the shape of
an admissible diagram is deduced from exactly these two facts, and Bourbaki, *Lie Groups and Lie
Algebras, Chapters 4-6*, Ch. VI §4.
-/

namespace TauCeti

variable {B : Type*} {A : Matrix B B ℤ}

/-- The **diagram** of an integer matrix: the graph on the index type joining two distinct indices
when both entries of the transposed pair are nonzero.

For a generalized Cartan matrix, and so for a matrix of finite type, one of the two entries is
nonzero exactly when the other is (`TauCeti.IsFiniteType.diagramGraph_adj_iff`), and the definition
is the expected one. Asking for both is what makes the relation symmetric for an arbitrary matrix,
where it is the diagram of the symmetrized vanishing pattern; the symmetrization that
`SimpleGraph.fromRel` performs is then a duplication, and `TauCeti.diagramGraph_adj` reads the
adjacency back off. -/
def diagramGraph (A : Matrix B B ℤ) : SimpleGraph B :=
  SimpleGraph.fromRel fun i j ↦ A i j ≠ 0 ∧ A j i ≠ 0

@[simp]
theorem diagramGraph_adj {i j : B} :
    (diagramGraph A).Adj i j ↔ i ≠ j ∧ A i j ≠ 0 ∧ A j i ≠ 0 := by
  rw [diagramGraph, SimpleGraph.fromRel_adj]
  tauto

instance [DecidableEq B] (A : Matrix B B ℤ) : DecidableRel (diagramGraph A).Adj :=
  fun _ _ ↦ decidable_of_iff _ diagramGraph_adj.symm

namespace IsFiniteType

variable [Fintype B]

/-- **Adjacency in the diagram of a finite-type matrix is a single nonvanishing condition**, the
vanishing pattern of such a matrix being symmetric. -/
theorem diagramGraph_adj_iff (h : IsFiniteType A) {i j : B} :
    (diagramGraph A).Adj i j ↔ i ≠ j ∧ A i j ≠ 0 := by
  rw [diagramGraph_adj]
  exact ⟨fun hadj ↦ ⟨hadj.1, hadj.2.1⟩,
    fun hadj ↦ ⟨hadj.1, hadj.2, fun hc ↦ hadj.2 (h.apply_eq_zero_symm hc)⟩⟩

/-- **The diagram of a finite-type matrix is a forest.** No walk of the diagram that returns to its
start is a cycle.

A cycle in a graph is a copy of a cycle graph of length at least three
(`SimpleGraph.isAcyclic_iff_free_cycleGraph`), so its vertices are a list of at least three distinct
indices each joined to its cyclic successor, which is what
`TauCeti.IsFiniteType.exists_apply_succ_eq_zero` forbids. -/
theorem isAcyclic_diagramGraph (h : IsFiniteType A) : (diagramGraph A).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_free_cycleGraph]
  rintro n hn ⟨f⟩
  have : NeZero n := ⟨by omega⟩
  -- The vertices of the copy are distinct, and each is joined to its cyclic successor.
  obtain ⟨k, hk⟩ := h.exists_apply_succ_eq_zero hn f.injective
  have hadj : (SimpleGraph.cycleGraph n).Adj k (k + 1) := by
    rw [SimpleGraph.cycleGraph_adj', add_sub_cancel_left, Fin.val_one',
      Nat.mod_eq_of_lt (by omega)]
    exact Or.inr rfl
  exact (diagramGraph_adj.mp (f.toHom.map_adj hadj)).2.1 hk

/-- **A reachable pair in a finite-type diagram is joined by an induced matrix chain.** More
precisely, there are vertices `w 0, ..., w n` with the prescribed endpoints, no repetitions,
nonzero entries between consecutive vertices, and zero entries between vertices separated by at
least one intermediate vertex.

The no-chord conclusion is the part not supplied merely by choosing a graph path. It follows from
the diagram being acyclic, and is what lets a classification argument identify the corresponding
principal submatrix with a chain-shaped model rather than only a matrix containing the chain's
edges. Nothing is asserted about vertices outside the chain. -/
theorem exists_chain_of_reachable (h : IsFiniteType A) {u v : B}
    (huv : (diagramGraph A).Reachable u v) :
    ∃ (n : ℕ) (w : ℕ → B), w 0 = u ∧ w n = v ∧
      Set.InjOn w {i | i ≤ n} ∧
      (∀ i, i < n → A (w i) (w (i + 1)) ≠ 0) ∧
      ∀ i j, i + 1 < j → j ≤ n → A (w i) (w j) = 0 := by
  classical
  let p : (diagramGraph A).Path u v := huv.some.toPath
  let q : (diagramGraph A).Walk u v := p
  have hq : q.IsPath := p.isPath
  refine ⟨q.length, q.getVert, ?_, ?_, ?_, ?_, ?_⟩
  · exact q.getVert_zero
  · exact q.getVert_length
  · exact hq.getVert_injOn
  · intro i hi
    exact (h.diagramGraph_adj_iff.mp (q.adj_getVert_succ hi)).2
  · intro i j hij hj
    by_contra hne
    have hne' : q.getVert i ≠ q.getVert j := fun heq ↦ by
      have := hq.getVert_injOn (by omega : i ≤ q.length) hj heq
      omega
    exact h.isAcyclic_diagramGraph.not_adj_getVert_of_add_one_lt hq hij hj
      (h.diagramGraph_adj_iff.mpr ⟨hne', hne⟩)

/-- **The degree bound in graph form**: no index of a finite-type matrix has four neighbours in the
diagram, so a finite-type diagram branches into at most three arms. -/
theorem degree_le_three [DecidableEq B] (h : IsFiniteType A) (i : B) :
    (diagramGraph A).degree i ≤ 3 :=
  h.card_le_three_of_forall_apply_ne_zero (SimpleGraph.notMem_neighborFinset_self _ i)
    fun _ hj ↦ (diagramGraph_adj.mp ((SimpleGraph.mem_neighborFinset _ _ _).mp hj)).2.1

/-- **A connected finite-type diagram is a tree.** For the Cartan matrix of a base this is the
irreducible case, the one the classification enumerates. -/
theorem isTree_diagramGraph (h : IsFiniteType A) (hconn : (diagramGraph A).Connected) :
    (diagramGraph A).IsTree :=
  ⟨hconn, h.isAcyclic_diagramGraph⟩

/-- **A connected finite-type diagram has one edge fewer than it has vertices.** This is the
counting form of acyclicity, and the constraint that the enumeration of admissible diagrams is run
against. -/
theorem card_edgeFinset_add_one_eq_card [DecidableEq B] (h : IsFiniteType A)
    (hconn : (diagramGraph A).Connected) :
    (diagramGraph A).edgeFinset.card + 1 = Fintype.card B :=
  (h.isTree_diagramGraph hconn).card_edgeFinset

end IsFiniteType

section RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic]

/-- **The Dynkin diagram of an irreducible root system is connected.** Irreducibility of a root
pairing says that the roots do not split into two mutually orthogonal families, and Mathlib records
it as the induction principle `RootPairing.Base.induction_on_cartanMatrix`: a property of the simple
roots that propagates along nonzero Cartan entries holds everywhere once it holds somewhere. Being
reachable from a fixed simple root is such a property. -/
theorem preconnected_diagramGraph_cartanMatrix [P.IsReduced] [P.IsIrreducible] (b : P.Base) :
    (diagramGraph b.cartanMatrix).Preconnected := by
  intro i j
  refine b.induction_on_cartanMatrix (fun k ↦ (diagramGraph b.cartanMatrix).Reachable i k)
    (SimpleGraph.Reachable.refl i) fun p q hp hne ↦ ?_
  rcases eq_or_ne p q with rfl | hpq
  · exact hp
  · exact hp.trans (SimpleGraph.Adj.reachable (diagramGraph_adj.mpr
      ⟨hpq, fun hc ↦ hne (b.cartanMatrix_apply_eq_zero_iff_symm.mp hc), hne⟩))

variable [Nonempty ι] [P.IsRootSystem] [P.IsReduced] [P.IsIrreducible] (b : P.Base)

omit [P.IsRootSystem] in
include b in
/-- **The Dynkin diagram of an irreducible root system is connected**, as a `Connected` graph: a
root system with at least one root has at least one simple root. -/
theorem connected_diagramGraph_cartanMatrix : (diagramGraph b.cartanMatrix).Connected := by
  have : Nonempty b.support := b.support_nonempty.to_subtype
  exact ⟨preconnected_diagramGraph_cartanMatrix b⟩

/-- **The Dynkin diagram of an irreducible root system is a tree.** Both halves are theorems about
the Cartan matrix: acyclicity because it is of finite type, connectedness because the root system is
irreducible. -/
theorem isTree_diagramGraph_cartanMatrix : (diagramGraph b.cartanMatrix).IsTree :=
  (isFiniteType_cartanMatrix b).isTree_diagramGraph (connected_diagramGraph_cartanMatrix b)

/-- **The Dynkin diagram of an irreducible root system has one edge fewer than it has simple
roots.** With the degree bound of `TauCeti.IsFiniteType.degree_le_three`, this is the shape
constraint that the enumeration of the admissible diagrams is run against. -/
theorem card_edgeFinset_add_one_eq_card_support [DecidableEq b.support] :
    (diagramGraph b.cartanMatrix).edgeFinset.card + 1 = b.support.card :=
  (Fintype.card_coe b.support) ▸ (isTree_diagramGraph_cartanMatrix b).card_edgeFinset

end RootPairing

end TauCeti
