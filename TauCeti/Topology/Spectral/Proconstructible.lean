/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Spectral.ConstructibleTopology

/-!
# Pro-constructible subsets

A subset of a topological space is *pro-constructible* if it is closed in the constructible
topology (Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 3.17 and Remark 3.21; on a
spectral space this agrees with being an intersection of constructible subsets). This file
defines the predicate and develops its calculus: stability under arbitrary intersections and
finite unions, pro-constructibility of closed sets and of quasi-compact opens, and stability
under preimages by spectral maps.

The spectrality of a pro-constructible subspace of a spectral space is the companion
development, which consumes the patch criterion for spectral spaces.

## Main definitions

* `TauCeti.IsProconstructible s` : `s` is closed in `constructibleTopology X`.

## Main results

* `TauCeti.IsSpectralMap.isProconstructible_preimage` : spectral maps pull back
  pro-constructible sets to pro-constructible sets, via
  `TauCeti.IsSpectralMap.continuous_constructibleTopology`.
* `TauCeti.IsClosed.isProconstructible` : on a prespectral space, closed sets are
  pro-constructible.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 3.17, Remark 3.21,
  Proposition 3.23.
-/

public section

namespace TauCeti

open TopologicalSpace Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A subset of a topological space is *pro-constructible* if it is closed in the
constructible topology. -/
def IsProconstructible (s : Set X) : Prop :=
  IsClosed[constructibleTopology X] s

/-- Pro-constructibility unfolded, as closedness in the constructible topology. -/
@[simp]
theorem isProconstructible_iff {s : Set X} :
    IsProconstructible s ↔ IsClosed[constructibleTopology X] s := Iff.rfl

/-- The empty set is pro-constructible. -/
lemma isProconstructible_empty : IsProconstructible (∅ : Set X) :=
  @isClosed_empty X (constructibleTopology X)

/-- The whole space is pro-constructible. -/
lemma isProconstructible_univ : IsProconstructible (univ : Set X) :=
  @isClosed_univ X (constructibleTopology X)

/-- The intersection of two pro-constructible sets is pro-constructible. -/
lemma IsProconstructible.inter {s t : Set X} (hs : IsProconstructible s)
    (ht : IsProconstructible t) : IsProconstructible (s ∩ t) :=
  @IsClosed.inter X _ _ (constructibleTopology X) hs ht

/-- The union of two pro-constructible sets is pro-constructible. -/
lemma IsProconstructible.union {s t : Set X} (hs : IsProconstructible s)
    (ht : IsProconstructible t) : IsProconstructible (s ∪ t) :=
  @IsClosed.union X _ _ (constructibleTopology X) hs ht

/-- Arbitrary intersections of pro-constructible sets are pro-constructible. -/
lemma isProconstructible_sInter {S : Set (Set X)} (hS : ∀ s ∈ S, IsProconstructible s) :
    IsProconstructible (⋂₀ S) :=
  @isClosed_sInter X (constructibleTopology X) S hS

/-- Indexed intersections of pro-constructible sets are pro-constructible. -/
lemma isProconstructible_iInter {ι : Sort*} {s : ι → Set X}
    (hs : ∀ i, IsProconstructible (s i)) : IsProconstructible (⋂ i, s i) :=
  @isClosed_iInter X ι (constructibleTopology X) s hs

/-- Finite indexed unions of pro-constructible sets are pro-constructible. -/
lemma isProconstructible_iUnion_of_finite {ι : Sort*} [Finite ι] {s : ι → Set X}
    (hs : ∀ i, IsProconstructible (s i)) : IsProconstructible (⋃ i, s i) :=
  @isClosed_iUnion_of_finite X ι (constructibleTopology X) _ s hs

/-- Finite bounded unions of pro-constructible sets are pro-constructible. -/
lemma isProconstructible_biUnion_of_finite {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι → Set X}
    (hs : ∀ i ∈ I, IsProconstructible (s i)) : IsProconstructible (⋃ i ∈ I, s i) :=
  @Set.Finite.isClosed_biUnion X ι (constructibleTopology X) I s hI hs

/-- Finite unions of pro-constructible sets are pro-constructible. -/
lemma isProconstructible_sUnion_of_finite {S : Set (Set X)} (hS : S.Finite)
    (h : ∀ s ∈ S, IsProconstructible s) : IsProconstructible (⋃₀ S) := by
  rw [Set.sUnion_eq_biUnion]
  exact isProconstructible_biUnion_of_finite hS h

/-- A quasi-compact open set is pro-constructible. -/
lemma IsCompact.isProconstructible_of_isOpen {s : Set X} (hs : IsCompact s) (ho : IsOpen s) :
    IsProconstructible s := by
  have h : IsOpen[constructibleTopology X] sᶜ :=
    TopologicalSpace.isOpen_generateFrom_of_mem (Or.inr (by simp [ho, hs]))
  exact (@isOpen_compl_iff X s (constructibleTopology X)).mp h

/-- On a prespectral space, every closed set is pro-constructible (Wedhorn,
Proposition 3.23(1): the constructible topology is finer than the ambient topology). -/
lemma IsClosed.isProconstructible [PrespectralSpace X] {s : Set X} (hs : IsClosed s) :
    IsProconstructible s := by
  have h : IsOpen[constructibleTopology X] sᶜ := by
    rw [(PrespectralSpace.isTopologicalBasis (X := X)).open_eq_sUnion' hs.isOpen_compl]
    refine @isOpen_sUnion X (constructibleTopology X) _ fun t ht ↦ ?_
    exact TopologicalSpace.isOpen_generateFrom_of_mem (Or.inl ⟨ht.1.1, ht.1.2⟩)
  exact (@isOpen_compl_iff X s (constructibleTopology X)).mp h

/-- A spectral map is continuous for the constructible topologies. -/
lemma IsSpectralMap.continuous_constructibleTopology {f : X → Y} (hf : IsSpectralMap f) :
    @Continuous X Y (constructibleTopology X) (constructibleTopology Y) f := by
  refine (@continuous_generateFrom_iff X Y f (constructibleTopology X)
    (constructibleTopologySubbasis Y)).mpr ?_
  rintro s (⟨ho, hc⟩ | ⟨hcl, hcc⟩)
  · exact (hc.preimage_of_isOpen hf ho).isOpen_constructibleTopology_of_isOpen
      (hf.continuous.isOpen_preimage s ho)
  · refine IsCompact.isOpen_constructibleTopology_of_isClosed ?_ ?_
    · rw [← Set.preimage_compl]
      exact (hcc.preimage_of_isOpen hf hcl.isOpen_compl)
    · exact hcl.preimage hf.continuous

/-- Spectral maps pull back pro-constructible sets to pro-constructible sets. -/
lemma IsSpectralMap.isProconstructible_preimage {f : X → Y} (hf : IsSpectralMap f)
    {s : Set Y} (hs : IsProconstructible s) : IsProconstructible (f ⁻¹' s) :=
  @IsClosed.preimage X Y (constructibleTopology X) (constructibleTopology Y) f
    (IsSpectralMap.continuous_constructibleTopology hf) s hs

end TauCeti
