/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
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
about a cyclic list of indices; the work here is to turn a `SimpleGraph.Walk` that is a cycle into
such a list, cyclically indexed by `Fin` of its length. Connectedness in the root-system case is
irreducibility, which Mathlib packages as `RootPairing.Base.induction_on_cartanMatrix`.

## Main definitions

* `TauCeti.diagramGraph`: the diagram of an integer matrix, a `SimpleGraph` on its index type,
  joining two distinct indices when the entries of the transposed pair are both nonzero.

## Main results

* `TauCeti.IsFiniteType.isAcyclic_diagramGraph`: **the diagram of a finite-type matrix is a
  forest**. The affine diagrams `Ãₙ`, the cycles, are excluded here in one theorem.
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
where it is the diagram of the symmetrized vanishing pattern. -/
def diagramGraph (A : Matrix B B ℤ) : SimpleGraph B where
  Adj i j := i ≠ j ∧ A i j ≠ 0 ∧ A j i ≠ 0
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

@[simp]
theorem diagramGraph_adj {i j : B} :
    (diagramGraph A).Adj i j ↔ i ≠ j ∧ A i j ≠ 0 ∧ A j i ≠ 0 := Iff.rfl

instance [DecidableEq B] (A : Matrix B B ℤ) : DecidableRel (diagramGraph A).Adj :=
  fun i j ↦ inferInstanceAs (Decidable (i ≠ j ∧ A i j ≠ 0 ∧ A j i ≠ 0))

namespace IsFiniteType

variable [Fintype B]

/-- **Adjacency in the diagram of a finite-type matrix is a single nonvanishing condition**, the
vanishing pattern of such a matrix being symmetric. -/
theorem diagramGraph_adj_iff (h : IsFiniteType A) {i j : B} :
    (diagramGraph A).Adj i j ↔ i ≠ j ∧ A i j ≠ 0 :=
  ⟨fun hadj ↦ ⟨hadj.1, hadj.2.1⟩,
    fun hadj ↦ ⟨hadj.1, hadj.2, fun hc ↦ hadj.2 (h.apply_eq_zero_symm hc)⟩⟩

/-- **The diagram of a finite-type matrix is a forest.** No walk of the diagram that returns to its
start is a cycle.

The vertices of a cycle, read off by `SimpleGraph.Walk.getVert`, are a list of at least three
distinct indices each joined to its cyclic successor, which is what
`TauCeti.IsFiniteType.exists_apply_succ_eq_zero` forbids. The wrap-around edge is the one from the
last vertex back to the first, and it is the step `SimpleGraph.Walk.getVert` takes from
`c.length - 1` to `c.length`, the endpoint being the start again. -/
theorem isAcyclic_diagramGraph (h : IsFiniteType A) : (diagramGraph A).IsAcyclic := by
  intro u c hc
  have hlen : 3 ≤ c.length := hc.three_le_length
  have : NeZero c.length := ⟨by omega⟩
  have hval1 : ((1 : Fin c.length) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  -- The vertices of the cycle, indexed cyclically by `Fin c.length`.
  set v : Fin c.length → B := fun t ↦ c.getVert t with hvdef
  have hinj : Function.Injective v := by
    intro s t hst
    have hs : (s : ℕ) < c.length := s.isLt
    have ht : (t : ℕ) < c.length := t.isLt
    exact Fin.val_injective (hc.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) hst)
  have hadj : ∀ t : Fin c.length, (diagramGraph A).Adj (v t) (v (t + 1)) := by
    intro t
    have hlt : (t : ℕ) < c.length := t.isLt
    -- The successor in `Fin c.length` is the successor step of the walk, wrapping at the end
    -- because the walk starts and finishes at `u`.
    have hstep : c.getVert ((t + 1 : Fin c.length) : ℕ) = c.getVert ((t : ℕ) + 1) := by
      by_cases hcase : (t : ℕ) + 1 = c.length
      · have h0 : ((t + 1 : Fin c.length) : ℕ) = 0 := by
          rw [Fin.val_add, hval1, hcase, Nat.mod_self]
        rw [h0, hcase, c.getVert_zero, c.getVert_length]
      · congr 1
        rw [Fin.val_add, hval1, Nat.mod_eq_of_lt (by omega)]
    simpa only [hvdef, hstep] using c.adj_getVert_succ hlt
  obtain ⟨k, hk⟩ := h.exists_apply_succ_eq_zero hlen hinj
  exact (hadj k).2.1 hk

/-- **The degree bound in graph form**: no index of a finite-type matrix has four neighbours in the
diagram, so a finite-type diagram branches into at most three arms. -/
theorem degree_le_three [DecidableEq B] (h : IsFiniteType A) (i : B) :
    (diagramGraph A).degree i ≤ 3 :=
  h.card_le_three_of_forall_apply_ne_zero (SimpleGraph.notMem_neighborFinset_self _ i)
    fun _ hj ↦ ((SimpleGraph.mem_neighborFinset _ _ _).mp hj).2.1

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
  · exact hp.trans (SimpleGraph.Adj.reachable
      ⟨hpq, fun hc ↦ hne (b.cartanMatrix_apply_eq_zero_iff_symm.mp hc), hne⟩)

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
theorem card_edgeFinset_add_one_eq_card_support [DecidableEq ι] :
    (diagramGraph b.cartanMatrix).edgeFinset.card + 1 = b.support.card :=
  (Fintype.card_coe b.support) ▸ (isTree_diagramGraph_cartanMatrix b).card_edgeFinset

end RootPairing

end TauCeti
