/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Spectral.Hom
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Spectral.Basic

/-!
# A basis criterion for spectral maps, and transport of spectrality along an embedding

Two utilities for spectral spaces and maps. A continuous map is spectral as soon as the preimage
of every member of some topological **basis** of the target is compact; and spectrality transports
from the preimage of a set to the set itself along an embedding whose range contains it.

The basis criterion first. Spectrality asks for compact preimages of all compact open sets; the
reduction to a basis is the observation that a compact open set is a *finite* union of basis
elements — cover it by the basis members it contains and extract a finite subcover — and a finite
union of compact preimages is compact.

Nothing is assumed of the basis members themselves, not even compactness: only their preimages
enter the argument. In the intended applications the basis members are the distinguished
quasi-compact opens of a spectral space (Wedhorn's family `R` for `Spv (A, I)`), whose preimages
are computed by hand.

Mathlib's `IsSpectralMap` API provides constructors from identities, compositions and embeddings,
but no criterion that tests spectrality on a basis; this supplies the missing entry point.

## Main results

* `TauCeti.isSpectralMap_of_isTopologicalBasis` : a continuous map whose preimages of basis
  members are compact is a spectral map.
* `TauCeti.spectralSpace_of_isEmbedding` : a subset of the range of an embedding is spectral as
  soon as its preimage is — the transport step of any "prove it on a subspace" argument.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1 — Lemma 7.5(2) is the intended consumer of the
  basis criterion, and Corollary 7.12 and Theorem 7.35 of the transport lemma.
-/

public section

namespace TauCeti

open TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **A basis criterion for spectral maps.** A continuous map is spectral as soon as the preimage
of every member of a topological basis of the target is compact: a compact open set is a finite
union of basis members, and a finite union of compact preimages is compact.

The basis members themselves need not be compact — only their preimages appear in the
hypothesis. -/
theorem isSpectralMap_of_isTopologicalBasis {f : X → Y} {B : Set (Set Y)}
    (hB : IsTopologicalBasis B) (hf : Continuous f)
    (hpre : ∀ b ∈ B, IsCompact (f ⁻¹' b)) : IsSpectralMap f := by
  refine ⟨hf, fun s hso hs ↦ ?_⟩
  -- Write `s` as a union of basis members, then extract a finite subcover from compactness.
  obtain ⟨S, hSB, rfl⟩ := hB.open_eq_sUnion hso
  obtain ⟨t, ht⟩ := hs.elim_finite_subcover (fun b : S ↦ (b : Set Y))
    (fun b ↦ hB.isOpen (hSB b.2)) Set.sUnion_eq_iUnion.le
  -- The subcover is an equality: every member of `S` is contained in `⋃₀ S`.
  have heq : ⋃₀ S = ⋃ b ∈ t, (b : Set Y) := by
    refine subset_antisymm ht (Set.iUnion₂_subset fun b _ ↦ ?_)
    exact Set.subset_sUnion_of_mem b.2
  rw [heq, Set.preimage_iUnion₂]
  exact t.isCompact_biUnion fun b _ ↦ hpre b (hSB b.2)

/-- **Spectrality transports from a trace along an embedding.** A subset of the target contained
in the range of an embedding is spectral as soon as its preimage is: the embedding restricts to a
homeomorphism between the two.

This is the shape every "prove it on a subspace and carry it back" spectrality argument takes.
It is worth stating separately because the *reason* one works on the subspace is usually that the
inclusion is not a spectral map, which makes the general preservation theorems unavailable along
it; this lemma supplies the homeomorphism route instead. -/
theorem spectralSpace_of_isEmbedding {f : X → Y} (hf : Topology.IsEmbedding f) {S : Set Y}
    (hS : S ⊆ Set.range f) (h : SpectralSpace (f ⁻¹' S)) : SpectralSpace S := by
  -- The embedding restricts to a homeomorphism `f ⁻¹' S ≃ₜ S`.
  let e := hf.homeomorphOfSubsetRange hS
  -- Transfer compactness along it, then spectrality; a homeomorphism is an open embedding.
  have : CompactSpace S := e.compactSpace
  exact e.symm.isOpenEmbedding.spectralSpace

end TauCeti

end
