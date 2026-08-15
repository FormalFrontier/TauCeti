/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Combinatorics.SimpleGraph.PathGraph
public import TauCeti.LinearAlgebra.RootSystem.Chain
public import TauCeti.LinearAlgebra.RootSystem.Classification
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram

public section

/-!
# A simply-laced finite-type diagram without a branch node is of type `Aₙ`

The classification of finite-type Cartan matrices eliminates every shape outside the Dynkin list
and is then left with the task of *naming* the shapes that survive: a diagram known to be a chain
of single edges has to be reindexed onto the standard Cartan matrix `DynkinType.cartanMatrix (.A n)`
before it can be said to have that Cartan type. This file performs that reindexing for the type
`Aₙ` branch, where the surviving shape is a connected simply-laced diagram whose vertices all have
at most two neighbours.

The reindexing is the identification of the diagram with a path graph: a connected finite-type
diagram is a tree (`TauCeti.IsFiniteType.isTree_diagramGraph`), a finite tree of maximum degree two
is a path graph (`TauCeti.IsTree.nonempty_iso_pathGraph_of_degree_le_two`), and a simply-laced
matrix is determined by its diagram, its entries being `2` on the diagonal, `-1` along the edges,
and `0` elsewhere. Those are exactly the entries of `CartanMatrix.A n` at consecutive and
non-consecutive indices, which is what `TauCeti.chainEntry_eq_cartanMatrix_A` records.

Both hypotheses do work. Without simple lacing the surviving shapes are `Bₙ`, `Cₙ`, `F₄` and `G₂`,
whose diagrams are also paths, and without the degree bound they are `Dₙ` and `E₆`, `E₇`, `E₈`.

## Main results

* `TauCeti.apply_eq_chainEntry_of_iso_pathGraph`: a simply-laced normalized matrix equals
  `chainEntry` along any diagram isomorphism to `pathGraph n`.
* `TauCeti.exists_equiv_forall_eq_cartanMatrix_A_of_isTree_of_isSimplyLaced_of_degree_le_two`:
  a simply-laced matrix with diagonal entries `2` and a tree diagram of maximum degree two is the
  standard Cartan matrix of type `Aₙ` after a relabelling of its index type.
* `TauCeti.IsFiniteType.exists_equiv_forall_eq_cartanMatrix_A`: a connected simply-laced finite-type
  matrix whose diagram has maximum degree two is the standard Cartan matrix of type `Aₙ` after a
  relabelling of its index type.
* `TauCeti.hasCartanType_A_of_isSimplyLaced_of_degree_le_two`: the same statement for the base of an
  irreducible root system, in the form `TauCeti.HasCartanType`.
* `TauCeti.existsUnique_dynkinType_of_isSimplyLaced_of_degree_le_two`: such a base has exactly one
  valid Dynkin type, which is the classification statement itself on these diagrams.

## References

This is the type `Aₙ` case of the reindexing step of the classification of finite-type Cartan
matrices, Layer 5 of `TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. See
J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §11.4, and Bourbaki,
*Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §4.
-/

namespace TauCeti

open SimpleGraph

variable {B : Type*} [Fintype B] [DecidableEq B] {A : Matrix B B ℤ}

/-- **A simply-laced normalized matrix equals `chainEntry` along any diagram isomorphism to
`pathGraph n`.** -/
theorem apply_eq_chainEntry_of_iso_pathGraph {B : Type*}
    {A : Matrix B B ℤ} (hdiag : ∀ i, A i i = 2) (hsl : A.IsSimplyLaced)
    {G : SimpleGraph B} (hadj : ∀ i j, G.Adj i j ↔ i ≠ j ∧ A i j ≠ 0)
    {n : ℕ} (iso : G ≃g pathGraph n) (i j : B) :
    A i j = chainEntry (iso i) (iso j) := by
  classical
  rcases eq_or_ne i j with rfl | hij
  · rw [hdiag, chainEntry_self]
  by_cases hA : A i j = 0
  · -- Distinct nonadjacent indices: the entry vanishes and the vertices are not consecutive.
    have hnot : ¬ G.Adj i j := fun hc ↦ (hadj i j).mp hc |>.2 hA
    rw [adj_iff_of_iso_pathGraph iso] at hnot
    push Not at hnot
    have hne : (iso i : ℕ) ≠ (iso j : ℕ) := fun hc ↦ hij (iso.toEquiv.injective (Fin.ext hc))
    rw [hA, chainEntry_eq_zero hne (fun hc ↦ hnot.2 hc.symm) fun hc ↦ hnot.1 hc.symm]
  · -- Adjacent indices: the entry is `-1` and the vertices are consecutive.
    have hadj' : G.Adj i j := (hadj i j).mpr ⟨hij, hA⟩
    rw [adj_iff_of_iso_pathGraph iso] at hadj'
    rw [(hsl hij).resolve_left hA]
    rcases hadj' with hc | hc
    · rw [← hc, chainEntry_succ_right]
    · rw [← hc, chainEntry_succ_left]

/-- **A simply-laced matrix with diagonal entries `2` whose diagram is a tree of maximum degree two
is the standard Cartan matrix of type `Aₙ`**, after a relabelling of its index type by the vertices
of a path.

Only the Cartan-matrix normalization and symmetric vanishing pattern are needed here, rather than
positive definiteness or the other finite-type hypotheses. -/
theorem exists_equiv_forall_eq_cartanMatrix_A_of_isTree_of_isSimplyLaced_of_degree_le_two
    (htree : (diagramGraph A).IsTree) (hdiag : ∀ i, A i i = 2)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (hsl : A.IsSimplyLaced)
    (hdeg : ∀ i, (diagramGraph A).degree i ≤ 2) :
    ∃ e : B ≃ Fin (Fintype.card B),
      ∀ i j, A i j = DynkinType.cartanMatrix (.A (Fintype.card B)) (e i) (e j) := by
  obtain ⟨iso⟩ := IsTree.nonempty_iso_pathGraph_of_degree_le_two htree hdeg
  have hadj : ∀ i j, (diagramGraph A).Adj i j ↔ i ≠ j ∧ A i j ≠ 0 := fun i j ↦ by
    rw [diagramGraph_adj]
    exact ⟨fun h ↦ ⟨h.1, h.2.1⟩, fun h ↦ ⟨h.1, h.2, fun hji ↦ h.2 ((hzero i j).mpr hji)⟩⟩
  refine ⟨iso.toEquiv, fun i j ↦ ?_⟩
  simp only [DynkinType.cartanMatrix_A, ← chainEntry_eq_cartanMatrix_A]
  exact apply_eq_chainEntry_of_iso_pathGraph hdiag hsl hadj iso i j

/-- **A connected simply-laced finite-type matrix whose diagram has maximum degree two is the
standard Cartan matrix of type `Aₙ`**, after a relabelling of its index type by the vertices of a
path.

The relabelling is simultaneous on rows and columns, which is what `TauCeti.HasCartanType` asks
for; the type `Aₙ` matrix being symmetric, the orientation it fixes carries no information here. -/
theorem IsFiniteType.exists_equiv_forall_eq_cartanMatrix_A (h : IsFiniteType A)
    (hconn : (diagramGraph A).Connected) (hsl : A.IsSimplyLaced)
    (hdeg : ∀ i, (diagramGraph A).degree i ≤ 2) :
    ∃ e : B ≃ Fin (Fintype.card B),
      ∀ i j, A i j = DynkinType.cartanMatrix (.A (Fintype.card B)) (e i) (e j) := by
  exact exists_equiv_forall_eq_cartanMatrix_A_of_isTree_of_isSimplyLaced_of_degree_le_two
    (h.isTree_diagramGraph hconn) h.apply_self (fun _ _ ↦ h.apply_eq_zero_iff) hsl hdeg

section RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [CharZero R] [IsDomain R] [DecidableEq ι]
  [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible] [Nonempty ι]

/-- **An irreducible root system whose Dynkin diagram is simply laced and has no branch node has
Cartan type `Aₙ`**, for `n` the number of its simple roots. This is the type `Aₙ` half of the
existence of a Dynkin type; `TauCeti.HasCartanType.eq_of_valid` supplies its uniqueness. Reducedness
is used to deduce connectedness of the Dynkin diagram from irreducibility. -/
theorem hasCartanType_A_of_isSimplyLaced_of_degree_le_two (b : P.Base)
    (hsl : b.cartanMatrix.IsSimplyLaced)
    (hdeg : ∀ i, (diagramGraph b.cartanMatrix).degree i ≤ 2) :
    HasCartanType P b (.A b.support.card) := by
  obtain ⟨e, he⟩ := (isFiniteType_cartanMatrix b).exists_equiv_forall_eq_cartanMatrix_A
    (connected_diagramGraph_cartanMatrix b) hsl hdeg
  rw [← Fintype.card_coe b.support, hasCartanType_iff]
  exact ⟨e, he⟩

/-- **An irreducible root system whose Dynkin diagram is simply laced and has no branch node has
exactly one valid Dynkin type.** Existence is the identification with type `Aₙ` above and
uniqueness is `TauCeti.HasCartanType.eq_of_valid`, so this is the classification target
`existsUnique_dynkinType` on the diagrams this file names. -/
theorem existsUnique_dynkinType_of_isSimplyLaced_of_degree_le_two (b : P.Base)
    (hsl : b.cartanMatrix.IsSimplyLaced)
    (hdeg : ∀ i, (diagramGraph b.cartanMatrix).degree i ≤ 2) :
    ∃! t : DynkinType, t.Valid ∧ HasCartanType P b t :=
  (hasCartanType_A_of_isSimplyLaced_of_degree_le_two b hsl hdeg).existsUnique_of_valid
    (DynkinType.valid_A.mpr (Finset.card_pos.mpr b.support_nonempty))

end RootPairing

end TauCeti
