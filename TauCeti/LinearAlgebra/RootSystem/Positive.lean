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
fact that a simple reflection permutes the positive roots other than its own simple root.

## Main definitions

* `TauCeti.posRoots` is the set of positive roots relative to a base.
* `TauCeti.negRoots` is its complementary set of negative roots.

## Main results

* `TauCeti.image_reflectionPerm_self_posRoots` says root negation exchanges the two sets.
* `TauCeti.bijOn_reflectionPerm_posRoots_diff_singleton` says a simple reflection permutes the
  positive roots other than its own simple root.

## References

This file implements the “Positive and negative roots” item in Layer 1 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`, following the target signatures in
`TauCetiRoadmap/RepresentationTheory/RootSystems/Suggested.lean`.
-/

namespace TauCeti

open Set

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

/-- The positive roots relative to a base. -/
def posRoots [CharZero R] (b : P.Base) : Set ι := {i | b.IsPos i}

/-- The negative roots relative to a base. -/
def negRoots [CharZero R] (b : P.Base) : Set ι := {i | ¬ b.IsPos i}

variable [CharZero R] (b : P.Base)

/-- Membership in the set of positive roots. -/
@[simp]
lemma mem_posRoots (i : ι) : i ∈ posRoots P b ↔ b.IsPos i := Iff.rfl

/-- Membership in the set of negative roots. -/
@[simp]
lemma mem_negRoots (i : ι) : i ∈ negRoots P b ↔ ¬ b.IsPos i := Iff.rfl

/-- The negative roots are the complement of the positive roots. -/
lemma compl_posRoots : (posRoots P b)ᶜ = negRoots P b := by
  ext i
  simp only [Set.mem_compl_iff, mem_posRoots, mem_negRoots]

/-- The negative roots are the complement of the positive roots. -/
lemma negRoots_eq_compl : negRoots P b = (posRoots P b)ᶜ := compl_posRoots P b |>.symm

/-- No root is both positive and negative. -/
lemma disjoint_posRoots_negRoots : Disjoint (posRoots P b) (negRoots P b) := by
  rw [Set.disjoint_left]
  simp

/-- Every root is either positive or negative. -/
lemma posRoots_union_negRoots : posRoots P b ∪ negRoots P b = Set.univ := by
  rw [negRoots_eq_compl]
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
  rw [← RootPairing.indexNeg_neg, mem_negRoots, mem_posRoots,
    RootPairing.Base.IsPos.neg_iff_not]
  exact not_not

/-- The self-reflection of a root is positive exactly when the root is negative. -/
@[simp]
lemma isPos_reflectionPerm_self_iff_mem_negRoots (i : ι) :
    b.IsPos (P.reflectionPerm i i) ↔ i ∈ negRoots P b := by
  letI := P.indexNeg
  rw [← RootPairing.indexNeg_neg, mem_negRoots]
  exact RootPairing.Base.IsPos.neg_iff_not b i

/-- The negative of a negative root is positive. -/
lemma reflectionPerm_self_mem_posRoots_iff_mem_negRoots (i : ι) :
    P.reflectionPerm i i ∈ posRoots P b ↔ i ∈ negRoots P b := by
  exact (mem_posRoots P b _).trans (isPos_reflectionPerm_self_iff_mem_negRoots P b i)

/-- A positive root is a nonnegative natural-number combination of simple roots. -/
lemma exists_root_eq_sum_nat_of_mem_posRoots {i : ι} (hi : i ∈ posRoots P b) :
    ∃ f : ι → ℕ, f.support ⊆ b.support ∧
      P.root i = ∑ j ∈ b.support, f j • P.root j := by
  obtain ⟨f, hf, hpos | hneg⟩ := b.exists_root_eq_sum_nat_or_neg i
  · exact ⟨f, hf, hpos⟩
  · exfalso
    let g : ι → ℤ := fun j ↦ -(f j : ℤ)
    have hroot : P.root i = ∑ j ∈ b.support, g j • P.root j := by
      rw [hneg]
      simp only [g, Finset.sum_neg_distrib, neg_smul, Nat.cast_smul_eq_nsmul]
    have hheight : b.height i = ∑ j ∈ b.support, g j := b.height_eq_sum hroot
    rw [mem_posRoots, RootPairing.Base.isPos_iff] at hi
    rw [hheight] at hi
    have hnonpos : ∑ j ∈ b.support, g j ≤ 0 :=
      Finset.sum_nonpos fun j _ ↦ by simp [g]
    exact (not_lt_of_ge hnonpos hi).elim

/-- Root negation exchanges positive and negative roots. -/
theorem image_reflectionPerm_self_posRoots :
    (fun i ↦ P.reflectionPerm i i) '' posRoots P b = negRoots P b := by
  letI := P.indexNeg
  simp_rw [← RootPairing.indexNeg_neg]
  ext i
  constructor
  · rintro ⟨j, hj, rfl⟩
    simp only [mem_negRoots, mem_posRoots] at hj ⊢
    intro hneg
    exact (RootPairing.Base.IsPos.neg_iff_not b j).mp hneg hj
  · intro hi
    refine ⟨-i, ?_, neg_neg i⟩
    simp only [mem_negRoots, mem_posRoots] at hi ⊢
    exact (RootPairing.Base.IsPos.neg_iff_not b i).mpr hi

/-- Root negation exchanges negative and positive roots. -/
theorem image_reflectionPerm_self_negRoots :
    (fun i ↦ P.reflectionPerm i i) '' negRoots P b = posRoots P b := by
  letI := P.indexNeg
  have hinv : Function.Involutive (fun i : ι ↦ P.reflectionPerm i i) := by
    intro i
    simp only [← RootPairing.indexNeg_neg, neg_neg]
  calc
    (fun i ↦ P.reflectionPerm i i) '' negRoots P b =
        (fun i ↦ P.reflectionPerm i i) '' (posRoots P b)ᶜ := by rw [negRoots_eq_compl]
    _ = ((fun i ↦ P.reflectionPerm i i) '' posRoots P b)ᶜ :=
      Set.image_compl_eq hinv.bijective
    _ = (negRoots P b)ᶜ := by rw [image_reflectionPerm_self_posRoots]
    _ = posRoots P b := by
      ext i
      simp only [Set.mem_compl_iff, mem_negRoots, mem_posRoots]
      tauto

/-- Reflecting a positive root in a simple root never produces that simple root: the only root
sent to a simple root `αᵢ` by `sᵢ` is `-αᵢ`, which is negative. -/
lemma reflectionPerm_ne_of_mem_posRoots {i j : ι} (hi : i ∈ b.support)
    (hj : j ∈ posRoots P b) :
    P.reflectionPerm i j ≠ i := by
  intro h
  have hji : j = P.reflectionPerm i i := by
    rw [← P.reflectionPerm_self i j, h]
  rw [mem_posRoots, hji, isPos_reflectionPerm_self_iff_mem_negRoots, mem_negRoots] at hj
  exact hj (b.isPos_of_mem_support hi)

variable [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- A simple reflection preserves the set of positive roots other than its own simple root. Both
directions follow from the forward implication because `P.reflectionPerm i` is an involution. -/
lemma reflectionPerm_mem_posRoots_diff_singleton_iff {i : ι} (hi : i ∈ b.support) (j : ι) :
    P.reflectionPerm i j ∈ posRoots P b \ {i} ↔ j ∈ posRoots P b \ {i} := by
  have key : ∀ k : ι, k ∈ posRoots P b \ {i} → P.reflectionPerm i k ∈ posRoots P b \ {i} := by
    rintro k ⟨hkpos, hkne⟩
    have hkne' : k ≠ i := by simpa using hkne
    exact ⟨(mem_posRoots P b _).mpr (((mem_posRoots P b k).mp hkpos).reflectionPerm hi hkne'),
      by simpa using reflectionPerm_ne_of_mem_posRoots P b hi hkpos⟩
  refine ⟨fun h ↦ ?_, key j⟩
  simpa only [P.reflectionPerm_self i j] using key _ h

/-- A simple reflection permutes the positive roots other than its own simple root. -/
theorem bijOn_reflectionPerm_posRoots_diff_singleton {i : ι} (hi : i ∈ b.support) :
    Set.BijOn (P.reflectionPerm i) (posRoots P b \ {i}) (posRoots P b \ {i}) :=
  Set.InvOn.bijOn ⟨fun j _ ↦ P.reflectionPerm_self i j, fun j _ ↦ P.reflectionPerm_self i j⟩
    (fun _ hj ↦ (reflectionPerm_mem_posRoots_diff_singleton_iff P b hi _).mpr hj)
    (fun _ hj ↦ (reflectionPerm_mem_posRoots_diff_singleton_iff P b hi _).mpr hj)

/-- The image form of `bijOn_reflectionPerm_posRoots_diff_singleton`: a simple reflection maps the
positive roots other than its own simple root onto themselves. -/
theorem image_reflectionPerm_posRoots_diff_singleton {i : ι} (hi : i ∈ b.support) :
    P.reflectionPerm i '' (posRoots P b \ {i}) = posRoots P b \ {i} :=
  (bijOn_reflectionPerm_posRoots_diff_singleton P b hi).image_eq

end TauCeti
