/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.DoubleEdge.Classification
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.Reindex
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.TripleEdge

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
    · have hsl : A.IsSimplyLaced := by
        intro i j hij
        have hmem := h.apply_mul_apply_mem_of_ne hij
        have hle_i : A i j ≤ 0 := h.apply_le_zero_of_ne hij
        have hle_j : A j i ≤ 0 := h.apply_le_zero_of_ne hij.symm
        have hnot3 : A i j * A j i ≠ 3 := fun h' ↦ h3 ⟨i, j, h'⟩
        have hnot2 : A i j * A j i ≠ 2 := fun h' ↦ h2 ⟨i, j, h'⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with h0 | h1 | h2' | h3'
        · have hz : A i j = 0 := by
            by_contra hnz
            have hjz : A j i = 0 := by
              cases mul_eq_zero.mp h0 with
              | inl h' => contradiction
              | inr h' => exact h'
            have hsymm := h.apply_eq_zero_symm hjz
            exact hnz hsymm
          left; exact hz
        · have : A i j = -1 := by
            have hne : A i j ≠ 0 := fun hc ↦ by rw [hc, zero_mul] at h1; contradiction
            have hlt : A i j ≤ -1 := by omega
            have hne' : A j i ≠ 0 := fun hc ↦ by rw [hc, mul_zero] at h1; contradiction
            have hlt' : A j i ≤ -1 := by omega
            by_contra hc
            have : A i j ≤ -2 := by omega
            have : 2 ≤ A i j * A j i := by nlinarith
            omega
          right; exact this
        · contradiction
        · contradiction
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

end RootPairing

end TauCeti
