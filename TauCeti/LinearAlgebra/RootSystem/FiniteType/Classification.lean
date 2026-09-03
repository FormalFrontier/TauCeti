/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.DoubleEdge.Classification
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.Reindex
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.TripleEdge
-- `TauCeti.LinearAlgebra.RootSystem.Isomorphism` supplies the rigidity theorem
-- `TauCeti.nonempty_equiv_of_hasCartanType`, which `nonempty_equiv_of_classifiedDynkinType_eq`
-- feeds the selected type to. Nothing from it appears in a statement here, so the import stays
-- private.
import TauCeti.LinearAlgebra.RootSystem.Isomorphism

public section

/-!
# The Cartan-Killing classification of finite-type Cartan matrices

This file proves the central theorem of Layer 5 of the root systems roadmap: every nonempty
connected finite-type Cartan matrix reindexes to the standard Cartan matrix of a **unique valid**
`DynkinType`, and every base of an irreducible reduced crystallographic finite root system has a
unique valid `DynkinType` (`TauCeti.existsUnique_dynkinType`).

The proof assembles the four geometric branches established in the subdiagram modules:
1. **Triple edge**:
   `TauCeti.IsFiniteType.exists_equiv_cartanMatrix_eq_G2_of_apply_mul_apply_eq_three` in
   `TauCeti.LinearAlgebra.RootSystem.FiniteType.TripleEdge` isolates the exceptional type `G₂`.
2. **Double edge**: `TauCeti.IsFiniteType.existsUnique_dynkinType_of_apply_mul_apply_eq_two` in
   `TauCeti.LinearAlgebra.RootSystem.FiniteType.DoubleEdge.Classification` classifies the families
   `Bₙ`, `Cₙ`, and the exceptional type `F₄`.
3. **Simply-laced branching**:
   `TauCeti.IsFiniteType.existsUnique_dynkinType_of_isSimplyLaced_of_degree_eq_three` in
   `TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.Reindex` classifies the forks `Dₙ` and the
   exceptional types `E₆`, `E₇`, `E₈`.
4. **Simply-laced chain**: `TauCeti.IsFiniteType.exists_equiv_forall_eq_cartanMatrix_A` in
   `TauCeti.LinearAlgebra.RootSystem.FiniteType.TypeA` classifies the linear chains `Aₙ`.

Uniqueness among valid types is supplied by `TauCeti.DynkinType.eq_of_valid_of_forall_eq` in
`TauCeti.LinearAlgebra.RootSystem.Classification`.

## Main results

* `TauCeti.IsFiniteType.existsUnique_dynkinType`: every nonempty connected finite-type Cartan matrix
  has a unique valid Dynkin type.
* `TauCeti.existsUnique_dynkinType`: the Cartan-Killing classification for irreducible reduced
  crystallographic finite root systems.
* `TauCeti.classifiedDynkinType`: the selected type as data, with
  `TauCeti.valid_classifiedDynkinType`, `TauCeti.hasCartanType_classifiedDynkinType` and
  `TauCeti.hasCartanType_iff_eq_classifiedDynkinType` characterizing it. This is what a consumer
  names instead of rechoosing a witness out of the existence statement.
* `TauCeti.nonempty_equiv_of_classifiedDynkinType_eq`: two root systems whose bases have the same
  Dynkin type are isomorphic, the classification combined with the rigidity theorem
  `TauCeti.nonempty_equiv_of_hasCartanType`.

The roadmap's summit needs two ingredients beyond these, and neither is proved here. One is the
coordinate realization of each valid type over `ℚ`, which turns a type into a model root system and
so supplies the existence half. The other is the independence of the type from the chosen base,
without which the classifier below classifies bases rather than root systems. With both, the
statements here become the advertised bijection between isomorphism classes of irreducible reduced
crystallographic finite root systems and valid Dynkin types.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §4.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Ch. III, §11.
* `TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`, Layer 5.
-/

namespace TauCeti

namespace IsFiniteType

variable {B : Type*} [Fintype B] {A : Matrix B B ℤ}

/-- **The classification of finite-type Cartan matrices.** Every nonempty connected finite-type
matrix agrees with the standard Cartan matrix of a unique valid Dynkin type after a simultaneous
relabelling of its rows and columns. -/
theorem existsUnique_dynkinType (h : IsFiniteType A) (hconn : (diagramGraph A).Connected) :
    ∃! t : DynkinType, t.Valid ∧
      ∃ e : B ≃ Fin t.rank, ∀ i j, A i j = t.cartanMatrix (e i) (e j) := by
  classical
  by_cases h3 : ∃ u v : B, A u v * A v u = 3
  · obtain ⟨u, v, huv⟩ := h3
    obtain ⟨e, he⟩ := h.exists_equiv_cartanMatrix_eq_G2_of_apply_mul_apply_eq_three
      hconn.preconnected huv
    refine ⟨.G2, ⟨DynkinType.valid_G2, e, he⟩, fun s hs ↦ ?_⟩
    exact DynkinType.eq_of_valid_of_forall_eq hs.1 DynkinType.valid_G2 hs.2.choose e
      hs.2.choose_spec he
  · by_cases h2 : ∃ u v : B, A u v * A v u = 2
    · obtain ⟨u, v, huv⟩ := h2
      exact h.existsUnique_dynkinType_of_apply_mul_apply_eq_two hconn.preconnected huv
    · -- With the Cartan products `2` and `3` excluded, the rank-two bound leaves only `0` and `1`,
      -- and a finite-type matrix all of whose edges are single is simply laced.
      have hsl : A.IsSimplyLaced := h.isSimplyLaced_iff.mpr fun i j hij ↦ by
        have hmem := h.apply_mul_apply_mem_of_ne hij
        have hnot2 : A i j * A j i ≠ 2 := fun h' ↦ h2 ⟨i, j, h'⟩
        have hnot3 : A i j * A j i ≠ 3 := fun h' ↦ h3 ⟨i, j, h'⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        omega
      by_cases hc : ∃ c : B, (diagramGraph A).degree c = 3
      · obtain ⟨c, hc3⟩ := hc
        exact h.existsUnique_dynkinType_of_isSimplyLaced_of_degree_eq_three hconn hsl hc3
      · have hdeg : ∀ v : B, (diagramGraph A).degree v ≤ 2 := by
          intro v
          have h3le := h.degree_le_three v
          have hne3 : (diagramGraph A).degree v ≠ 3 := fun hv3 ↦ hc ⟨v, hv3⟩
          omega
        obtain ⟨e, he⟩ := h.exists_equiv_forall_eq_cartanMatrix_A hconn hsl hdeg
        have hcard : 1 ≤ Fintype.card B := Fintype.card_pos_iff.mpr hconn.nonempty
        refine ⟨.A (Fintype.card B), ⟨DynkinType.valid_A.mpr hcard, e, he⟩, fun s hs ↦ ?_⟩
        exact DynkinType.eq_of_valid_of_forall_eq hs.1 (DynkinType.valid_A.mpr hcard)
          hs.2.choose e hs.2.choose_spec he

end IsFiniteType

section RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [CharZero R] [IsDomain R]
  [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible] [Nonempty ι]

/-- **The Cartan-Killing classification, existence and uniqueness of the Dynkin type.** Every
irreducible reduced crystallographic finite root system has a unique valid `DynkinType`. -/
theorem existsUnique_dynkinType (b : P.Base) :
    ∃! t : DynkinType, t.Valid ∧ HasCartanType P b t := by
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ :=
    (isFiniteType_cartanMatrix b).existsUnique_dynkinType
      (connected_diagramGraph_cartanMatrix b)
  exact ((hasCartanType_iff b t).mpr ⟨e, he⟩).existsUnique_of_valid ht

/-- **The Dynkin type of a base**, the valid type that `TauCeti.existsUnique_dynkinType` selects,
as data rather than as an existence statement. Its two defining properties are
`TauCeti.valid_classifiedDynkinType` and `TauCeti.hasCartanType_classifiedDynkinType`, and
`TauCeti.hasCartanType_iff_eq_classifiedDynkinType` says they pin it down.

It is noncomputable: the classification says which types occur and that the type of a base is
unique, not how to read it off a root system.

The type is attached to a base, not to the root system. Classically it does not depend on the base,
since the Weyl group acts transitively on bases, but that independence is a roadmap target of its
own and nothing here assumes it. -/
noncomputable def classifiedDynkinType (b : P.Base) : DynkinType :=
  (existsUnique_dynkinType b).choose

/-- The Dynkin type of a base is valid: it is one of `Aₙ` (`n ≥ 1`), `Bₙ` (`n ≥ 2`), `Cₙ`
(`n ≥ 3`), `Dₙ` (`n ≥ 4`), `E₆`, `E₇`, `E₈`, `F₄`, `G₂`. -/
lemma valid_classifiedDynkinType (b : P.Base) : (classifiedDynkinType b).Valid :=
  (existsUnique_dynkinType b).choose_spec.1.1

/-- The Cartan matrix of a base is the standard Cartan matrix of its Dynkin type, up to a
relabelling of the simple roots by the nodes of that type. -/
lemma hasCartanType_classifiedDynkinType (b : P.Base) :
    HasCartanType P b (classifiedDynkinType b) :=
  (existsUnique_dynkinType b).choose_spec.1.2

/-- **A valid Cartan type of a base is its Dynkin type.** This is the uniqueness half of
`TauCeti.existsUnique_dynkinType`, in the form that identifies a type produced elsewhere - by a
coordinate model, say - with the selected one. -/
lemma HasCartanType.classifiedDynkinType_eq {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) (ht : t.Valid) : classifiedDynkinType b = t :=
  (hasCartanType_classifiedDynkinType b).eq_of_valid h (valid_classifiedDynkinType b) ht

/-- A base has a given valid Cartan type exactly when that type is its Dynkin type. -/
lemma hasCartanType_iff_eq_classifiedDynkinType (b : P.Base) {t : DynkinType} (ht : t.Valid) :
    HasCartanType P b t ↔ t = classifiedDynkinType b :=
  ⟨fun h ↦ (h.classifiedDynkinType_eq ht).symm, fun h ↦ h ▸ hasCartanType_classifiedDynkinType b⟩

/-- The rank of the Dynkin type of a base is the number of simple roots. -/
lemma rank_classifiedDynkinType (b : P.Base) :
    (classifiedDynkinType b).rank = b.support.card :=
  (hasCartanType_classifiedDynkinType b).card_support.symm

variable {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P₂ : RootPairing ι₂ R M₂ N₂} [Finite ι₂] [P₂.IsRootSystem] [P₂.IsCrystallographic]
  [P₂.IsReduced] [P₂.IsIrreducible] [Nonempty ι₂]

/-- **Two root systems whose bases have the same Dynkin type are isomorphic.** This is the
classification and the rigidity theorem `TauCeti.nonempty_equiv_of_hasCartanType` in one statement:
the Dynkin type of a base determines the root system it comes from, up to isomorphism.

The converse - isomorphic root systems have bases of the same Dynkin type - needs the Dynkin type
to be independent of the base, which is not proved here. -/
theorem nonempty_equiv_of_classifiedDynkinType_eq (b : P.Base) (b₂ : P₂.Base)
    (h : classifiedDynkinType b = classifiedDynkinType b₂) : Nonempty (P.Equiv P₂) :=
  nonempty_equiv_of_hasCartanType b b₂ (classifiedDynkinType b)
    (hasCartanType_classifiedDynkinType b)
    ((hasCartanType_iff_eq_classifiedDynkinType b₂ (valid_classifiedDynkinType b)).mpr h)

end RootPairing

end TauCeti
