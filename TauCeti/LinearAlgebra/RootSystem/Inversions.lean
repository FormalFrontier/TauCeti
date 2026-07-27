/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.RootSystem.WeylGroup
public import TauCeti.LinearAlgebra.RootSystem.Positive

public section

/-!
# Inversion sets in a Weyl group

Relative to a base of a root pairing, the inversion set of a Weyl-group element consists of the
positive roots that it sends to negative roots. This file gives the set-theoretic API for inversion
sets and computes the inversion set of the identity and of a simple reflection.

These computations are the base cases for the root-level exchange step and the later identification
of Coxeter length with the number of inversions.

## Main definitions and results

* `TauCeti.inversions` is the set of positive roots sent to negative roots.
* `TauCeti.inversions_one` computes the inversion set of the identity.
* `TauCeti.inversions_ofIdx` computes the inversion set of a simple reflection.
* `TauCeti.image_root_inversions` identifies index-level inversions with vector roots.

## References

This file implements the inversion-set part of Layer 1 in
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. The mathematical convention follows
Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4--6.
-/

namespace TauCeti

open Set

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [CharZero R]

/-- The inversion set of `w`: the positive root indices that `w` sends to negative roots. -/
def inversions (b : P.Base) (w : P.weylGroup) : Set ι :=
  {i | b.IsPos i ∧ ¬ b.IsPos (P.weylGroupToPerm w i)}

variable (b : P.Base) (w : P.weylGroup)

/-- Membership in an inversion set means being positive and having negative image. -/
@[simp]
lemma mem_inversions (i : ι) :
    i ∈ inversions P b w ↔ b.IsPos i ∧ ¬ b.IsPos (P.weylGroupToPerm w i) :=
  Iff.rfl

/-- An inversion set is the intersection of the positive roots with the preimage of the negative
roots. -/
lemma inversions_eq_inter_preimage :
    inversions P b w =
      posRoots P b ∩ (P.weylGroupToPerm w) ⁻¹' negRoots P b := by
  ext i
  simp only [mem_inversions, Set.mem_inter_iff, mem_posRoots, Set.mem_preimage,
    mem_negRoots]

/-- Every inversion is a positive root. -/
lemma inversions_subset_posRoots : inversions P b w ⊆ posRoots P b := by
  intro i hi
  exact (mem_posRoots P b i).mpr hi.1

/-- The image of every inversion is a negative root. -/
lemma mapsTo_inversions_negRoots :
    MapsTo (P.weylGroupToPerm w) (inversions P b w) (negRoots P b) := by
  intro i hi
  exact (mem_negRoots P b _).mpr hi.2

/-- An element has no inversions exactly when it sends every positive root to a positive root. -/
theorem inversions_eq_empty_iff :
    inversions P b w = ∅ ↔
      MapsTo (P.weylGroupToPerm w) (posRoots P b) (posRoots P b) := by
  constructor
  · intro h i hi
    by_contra hwi
    have : i ∈ inversions P b w :=
      ⟨(mem_posRoots P b i).mp hi, (mem_posRoots P b _).not.mp hwi⟩
    rw [h] at this
    exact this
  · intro h
    rw [Set.eq_empty_iff_forall_notMem]
    intro i hi
    exact hi.2 ((mem_posRoots P b _).mp (h ((mem_posRoots P b i).mpr hi.1)))

/-- Every positive root is an inversion exactly when all positive roots are sent to
negative roots. -/
theorem inversions_eq_posRoots_iff :
    inversions P b w = posRoots P b ↔
      MapsTo (P.weylGroupToPerm w) (posRoots P b) (negRoots P b) := by
  constructor
  · intro h i hi
    apply mapsTo_inversions_negRoots P b w
    rw [h]
    exact hi
  · intro h
    apply Set.Subset.antisymm (inversions_subset_posRoots P b w)
    intro i hi
    refine ⟨(mem_posRoots P b i).mp hi, ?_⟩
    exact (mem_negRoots P b _).mp (h hi)

/-- Inversion sets are finite when the root index type is finite. -/
lemma inversions_finite [Finite ι] : (inversions P b w).Finite :=
  Set.toFinite _

/-- The number of inversions is at most the number of positive roots. -/
lemma ncard_inversions_le [Finite ι] :
    (inversions P b w).ncard ≤ (posRoots P b).ncard :=
  Set.ncard_le_ncard (inversions_subset_posRoots P b w) (posRoots_finite P b)

/-- The identity Weyl-group element has no inversions. -/
@[simp]
theorem inversions_one : inversions P b 1 = ∅ := by
  ext i
  simp

/-- The number of inversions of the identity is zero. -/
@[simp]
lemma ncard_inversions_one : (inversions P b 1).ncard = 0 := by
  rw [inversions_one, Set.ncard_empty]

variable [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- A simple reflection has exactly its defining simple root as an inversion. -/
theorem inversions_ofIdx {i : ι} (hi : i ∈ b.support) :
    inversions P b (RootPairing.weylGroup.ofIdx P i) = {i} := by
  ext j
  simp only [mem_inversions, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hj, hneg⟩
    by_contra hji
    exact hneg (hj.reflectionPerm hi hji)
  · rintro rfl
    refine ⟨b.isPos_of_mem_support hi, ?_⟩
    simpa only [RootPairing.weylGroup.ofIdx, RootPairing.weylGroupToPerm,
      MonoidHom.restrict_apply, RootPairing.Equiv.indexHom_apply,
      RootPairing.Equiv.reflection_indexEquiv,
      isPos_reflectionPerm_self_iff_mem_negRoots, mem_negRoots, not_not] using
        b.isPos_of_mem_support hi

/-- A simple reflection has one inversion. -/
@[simp]
theorem ncard_inversions_ofIdx {i : ι} (hi : i ∈ b.support) :
    (inversions P b (RootPairing.weylGroup.ofIdx P i)).ncard = 1 := by
  rw [inversions_ofIdx P b hi, Set.ncard_singleton]

omit [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] in
/-- Index-level inversions identify with the positive vector roots sent to negative vector roots. -/
theorem image_root_inversions :
    P.root '' inversions P b w =
      (P.root '' posRoots P b) ∩ {α | w • α ∈ P.root '' negRoots P b} := by
  ext α
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨⟨i, (mem_posRoots P b i).mpr hi.1, rfl⟩, ?_⟩
    exact ⟨P.weylGroupToPerm w i, (mem_negRoots P b _).mpr hi.2,
      (P.weylGroup_apply_root w i).symm⟩
  · rintro ⟨⟨i, hi, rfl⟩, j, hj, hact⟩
    have hij : P.weylGroupToPerm w i = j :=
      P.root.injective ((P.weylGroup_apply_root w i).symm.trans hact.symm)
    refine ⟨i, ⟨(mem_posRoots P b i).mp hi, ?_⟩, rfl⟩
    rwa [hij, ← mem_negRoots P b j]

end TauCeti
