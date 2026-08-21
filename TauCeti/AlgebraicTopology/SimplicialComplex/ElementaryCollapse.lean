/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.LinkStar

/-!
# Elementary collapses of simplicial complexes

An elementary simplicial collapse deletes a free face together with its unique proper coface.
This file supplies that local move for `PreAbstractSimplicialComplex`, Mathlib's type of
downward-closed collections of nonempty finite faces.  This is the elementary substrate for the
collapse track in layer 11 of the geometric-topology roadmap.

Following Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 3, the pair
`(σ, τ)` is free when `σ` is a proper face of `τ` and every face containing `σ` is either `σ` or
`τ`.  The usual codimension-one condition is expressed by Mathlib's finset cover relation;
uniqueness already suffices to prove that deleting the pair leaves a simplicial complex.

`PreAbstractSimplicialComplex` is intentional here.  Mathlib's `AbstractSimplicialComplex ι`
contains every singleton of the fixed ambient vertex type `ι`, so deleting a free vertex would
leave that type.  A collapse changes the used vertex set and therefore naturally lives in the
pre-complex type.

## Main definitions

* `PreAbstractSimplicialComplex.IsFreePair`: a face and its unique proper coface.
* `PreAbstractSimplicialComplex.ElementaryCollapsesTo`: the relation of one elementary collapse.
-/

public section

namespace PreAbstractSimplicialComplex

variable {ι : Type*} (K : _root_.PreAbstractSimplicialComplex ι)

/-- A pair `(σ, τ)` of faces is free when `σ` is a proper face of `τ` and `τ` is the only
face other than `σ` that contains `σ`.

This formulation includes maximality of `τ`: applying the last field to a face containing `τ`
forces that face to equal `τ`. -/
structure IsFreePair (σ τ : Finset ι) : Prop where
  /-- The lower face belongs to the complex. -/
  lower_mem : σ ∈ K
  /-- The upper face belongs to the complex. -/
  upper_mem : τ ∈ K
  /-- The lower face is properly contained in the upper face. -/
  lower_ssubset_upper : σ ⊂ τ
  /-- These are the only faces of the complex containing the lower face. -/
  eq_lower_or_eq_upper : ∀ ⦃ω : Finset ι⦄, ω ∈ K → σ ⊆ ω → ω = σ ∨ ω = τ

namespace IsFreePair

variable {K} {σ τ : Finset ι}

/-- The upper face of a free pair is maximal in the complex. -/
theorem upper_maximal (h : IsFreePair K σ τ) {ω : Finset ι} (hω : ω ∈ K) (hτω : τ ⊆ ω) :
    ω = τ := by
  rcases h.eq_lower_or_eq_upper hω (h.lower_ssubset_upper.subset.trans hτω) with rfl | h_eq
  · exact (h.lower_ssubset_upper.not_subset hτω).elim
  · exact h_eq

/-- The lower face of a free pair has codimension one in the upper face. -/
theorem covBy (h : IsFreePair K σ τ) : σ ⋖ τ := by
  refine ⟨h.lower_ssubset_upper, fun ω hσω hωτ => ?_⟩
  have hω : ω ∈ K :=
    (K.isRelLowerSet_faces h.upper_mem).2 hωτ.le
      ((K.isRelLowerSet_faces h.lower_mem).1.mono hσω.le)
  rcases h.eq_lower_or_eq_upper hω hσω.le with rfl | rfl
  · exact hσω.false
  · exact hωτ.false

end IsFreePair

/-- Deleting the lower face of a free pair retains exactly the original faces other than the
lower and upper faces. -/
theorem mem_deletion_of_isFreePair {σ τ ω : Finset ι} (h : IsFreePair K σ τ) :
    (ω ∈ K ∧ ¬σ ⊆ ω) ↔ ω ∈ K ∧ ω ≠ σ ∧ ω ≠ τ := by
  constructor
  · rintro ⟨hω, hσ⟩
    exact ⟨hω, fun hωσ => hσ hωσ.ge, fun hωτ => hσ (hωτ ▸ h.lower_ssubset_upper.subset)⟩
  · rintro ⟨hω, hωσ, hωτ⟩
    refine ⟨hω, fun hσω => ?_⟩
    rcases h.eq_lower_or_eq_upper hω hσω with rfl | rfl
    · exact hωσ rfl
    · exact hωτ rfl

/-- One complex elementarily collapses to another when the latter is obtained by deleting a
free pair. -/
def ElementaryCollapsesTo (L : _root_.PreAbstractSimplicialComplex ι) : Prop :=
  ∃ (σ τ : Finset ι), IsFreePair K σ τ ∧ L = deletion K σ

namespace ElementaryCollapsesTo

variable {K L : _root_.PreAbstractSimplicialComplex ι}

/-- A free pair determines an elementary collapse to its deletion. -/
theorem of_isFreePair {σ τ : Finset ι} (hfree : IsFreePair K σ τ)
    (hL : L = deletion K σ) : ElementaryCollapsesTo K L :=
  ⟨σ, τ, hfree, hL⟩

/-- An elementary collapse produces a subcomplex. -/
theorem le (h : ElementaryCollapsesTo K L) : L ≤ K := by
  obtain ⟨σ, τ, hfree, rfl⟩ := h
  exact deletion_le

/-- An elementary collapse is strict: its lower free face is lost. -/
theorem lt (h : ElementaryCollapsesTo K L) : L < K := by
  refine lt_of_le_of_ne h.le ?_
  obtain ⟨σ, τ, hfree, rfl⟩ := h
  intro h_eq
  have : σ ∈ deletion K σ := h_eq.symm ▸ hfree.lower_mem
  exact (mem_deletion.mp this).2 Finset.Subset.rfl

/-- Membership in the result of an elementary collapse is membership in the original complex
away from the selected free pair. -/
theorem exists_pair (h : ElementaryCollapsesTo K L) :
    ∃ (σ τ : Finset ι) (_hfree : IsFreePair K σ τ), σ ⋖ τ ∧
      ∀ ω, ω ∈ L ↔ ω ∈ K ∧ ω ≠ σ ∧ ω ≠ τ := by
  obtain ⟨σ, τ, hfree, rfl⟩ := h
  exact ⟨σ, τ, hfree, hfree.covBy, fun ω => by
    simpa only [mem_deletion] using mem_deletion_of_isFreePair K hfree⟩

end ElementaryCollapsesTo

end PreAbstractSimplicialComplex

