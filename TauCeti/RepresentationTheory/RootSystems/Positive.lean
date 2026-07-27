/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base

public section

/-!
# Positive and negative roots

This file packages Mathlib's positivity predicate for a root-pairing base as the sets of positive
and negative root indices. It records their partition, their exchange under root negation, and the
positive-root induction principle used to study Weyl-group inversion sets.

## Main definitions

* `TauCeti.posRoots` is the set of positive roots relative to a base.
* `TauCeti.negRoots` is its complementary set of negative roots.

## References

This file implements the “Positive and negative roots” item in Layer 1 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`.
-/

namespace TauCeti

open Set

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

/-- The positive roots relative to a base. -/
@[expose]
def posRoots [CharZero R] (b : P.Base) : Set ι := {i | b.IsPos i}

/-- The negative roots relative to a base. -/
@[expose]
def negRoots [CharZero R] (b : P.Base) : Set ι := {i | ¬ b.IsPos i}

variable [CharZero R] (b : P.Base)

/-- Membership in the set of positive roots. -/
@[simp]
lemma mem_posRoots (i : ι) : i ∈ posRoots P b ↔ b.IsPos i := Iff.rfl

/-- Membership in the set of negative roots. -/
@[simp]
lemma mem_negRoots (i : ι) : i ∈ negRoots P b ↔ ¬ b.IsPos i := Iff.rfl

/-- The negative roots are the complement of the positive roots. -/
lemma posRoots_compl : (posRoots P b)ᶜ = negRoots P b := rfl

/-- The negative roots are the complement of the positive roots. -/
lemma negRoots_compl : negRoots P b = (posRoots P b)ᶜ := rfl

/-- No root is both positive and negative. -/
lemma disjoint_posRoots_negRoots : Disjoint (posRoots P b) (negRoots P b) := by
  rw [Set.disjoint_left]
  simp

/-- Every root is either positive or negative. -/
lemma posRoots_union_negRoots : posRoots P b ∪ negRoots P b = Set.univ := by
  rw [negRoots_compl]
  exact Set.union_compl_self _

/-- Every root is either positive or negative. -/
lemma mem_posRoots_or_mem_negRoots (i : ι) : i ∈ posRoots P b ∨ i ∈ negRoots P b := by
  classical
  exact em _

/-- A root is negative exactly when it is not positive. -/
lemma not_mem_posRoots_iff_mem_negRoots (i : ι) :
    i ∉ posRoots P b ↔ i ∈ negRoots P b := by
  rfl

/-- The positive roots form a finite set when the root index type is finite. -/
lemma posRoots_finite [Finite ι] : (posRoots P b).Finite := Set.toFinite _

/-- The negative roots form a finite set when the root index type is finite. -/
lemma negRoots_finite [Finite ι] : (negRoots P b).Finite := Set.toFinite _

/-- Every simple root is positive. -/
lemma support_subset_posRoots : ↑b.support ⊆ posRoots P b := by
  intro i hi
  exact b.isPos_of_mem_support hi

/-- A nonempty root index type has a positive root. -/
lemma posRoots_nonempty [Nonempty ι] : (posRoots P b).Nonempty := by
  letI := P.indexNeg
  obtain ⟨i⟩ := ‹Nonempty ι›
  rcases RootPairing.Base.IsPos.or_neg b i with hi | hi
  · exact ⟨i, hi⟩
  · exact ⟨-i, hi⟩

/-- The negative of a positive root is negative. -/
lemma reflectionPerm_self_mem_negRoots_iff_mem_posRoots (i : ι) :
    P.reflectionPerm i i ∈ negRoots P b ↔ i ∈ posRoots P b := by
  letI := P.indexNeg
  change ¬ b.IsPos (-i) ↔ b.IsPos i
  rw [RootPairing.Base.IsPos.neg_iff_not b i]
  exact not_not

/-- The negative of a negative root is positive. -/
lemma reflectionPerm_self_mem_posRoots_iff_mem_negRoots (i : ι) :
    P.reflectionPerm i i ∈ posRoots P b ↔ i ∈ negRoots P b := by
  letI := P.indexNeg
  change b.IsPos (-i) ↔ ¬ b.IsPos i
  exact RootPairing.Base.IsPos.neg_iff_not b i

/-- Root negation exchanges positive and negative roots. -/
theorem image_reflectionPerm_self_posRoots :
    (fun i ↦ P.reflectionPerm i i) '' posRoots P b = negRoots P b := by
  letI := P.indexNeg
  ext i
  constructor
  · rintro ⟨j, hj, rfl⟩
    change ¬ b.IsPos (-j)
    intro hneg
    exact (RootPairing.Base.IsPos.neg_iff_not b j).mp hneg hj
  · intro hi
    refine ⟨-i, ?_, neg_neg i⟩
    exact (RootPairing.Base.IsPos.neg_iff_not b i).mpr hi

/-- Root negation exchanges negative and positive roots. -/
theorem image_reflectionPerm_self_negRoots :
    (fun i ↦ P.reflectionPerm i i) '' negRoots P b = posRoots P b := by
  letI := P.indexNeg
  ext i
  constructor
  · rintro ⟨j, hj, rfl⟩
    change b.IsPos (-j)
    exact (RootPairing.Base.IsPos.neg_iff_not b j).mpr hj
  · intro hi
    refine ⟨-i, ?_, neg_neg i⟩
    change ¬ b.IsPos (-i)
    intro hneg
    exact (RootPairing.Base.IsPos.neg_iff_not b i).mp hneg hi

/-- A positive root is a sum of simple roots whose partial sums are roots. -/
theorem exists_sum_support_of_mem_posRoots [Finite ι] [IsDomain R] [P.IsCrystallographic]
    {i : ι} (hi : i ∈ posRoots P b) :
    ∃ n, ∃ f : Fin n → ι,
      Set.range f ⊆ b.support ∧
      P.root i = ∑ m, P.root (f m) ∧
      ∀ m, ∑ m' ≤ m, P.root (f m') ∈ Set.range P.root :=
  RootPairing.Base.exists_eq_sum_and_forall_sum_mem_of_isPos (b := b) hi

/-- To prove a predicate on positive roots, it suffices to prove it for simple roots and show that
it is preserved by the simple reflections used in positive-root lowering. -/
theorem posRoots_induction_on_reflect [Finite ι] [IsDomain R] [P.IsCrystallographic]
    [P.IsReduced] {i : ι} (hi : i ∈ posRoots P b) {p : ι → Prop}
    (hbase : ∀ j ∈ b.support, p j)
    (hreflect : ∀ j k, p j → k ∈ b.support → p (P.reflectionPerm k j)) :
    p i :=
  hi.induction_on_reflect hbase hreflect

end TauCeti
