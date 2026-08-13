/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Cont.OfIdeal
public import TauCeti.AlgebraicGeometry.AdicSpace.SpvOfIdeal.Spectral

/-!
# The adic spectrum is spectral: Wedhorn's Theorem 7.35

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Theorem 7.35.**

For any subring `Aplus`, the subspace `spa Aplus` is pro-constructible in `Spv (A, IA)` and
is therefore a spectral space: by Theorem 7.10 its trace on the subspace is the intersection
of the trace of `Cont A` — closed there, by Corollary 7.12 — with the trace of the sub-unit
locus of `Aplus`, pro-constructible by
`isProConstructible_val_preimage_setOfPred_forall_vle_one`, and pro-constructible subspaces
of spectral spaces are spectral. At a ring of integral elements `Aplus = A⁺` this specializes
to Wedhorn's Theorem 7.35 for the adic spectrum `Spa (A, A⁺)`; the statements hold for an
arbitrary subring.

Neither trace statement descends from `Spv A`: the inclusion `Spv (A, I) → Spv A` is not
spectral, which is exactly why the two inputs are proved on the subspace side.

## Main results

* `TauCeti.ValuationSpectrum.spa_subset_spvOfIdeal` : `Spa (A, A⁺) ⊆ Spv (A, IA)`.
* `TauCeti.ValuationSpectrum.isProConstructible_val_preimage_spa` : the
  pro-constructibility of `spa Aplus` in `Spv (A, IA)` — Theorem 7.35's first half at a ring
  of integral elements.
* `TauCeti.ValuationSpectrum.spectralSpace_spa_of_pairOfDefinition`, and the
  `SpectralSpace (spa Aplus)` instance for Huber rings : `spa Aplus` is a spectral space —
  Wedhorn's Theorem 7.35 at a ring of integral elements.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- `spa Aplus ⊆ Spv (A, IA)`: the space consists of continuous points, and continuous
points lie in `Spv (A, IA)` (Theorem 7.10's inclusion). -/
theorem spa_subset_spvOfIdeal (P : PairOfDefinition A) (Aplus : Subring A) :
    spa Aplus ⊆ spvOfIdeal P.extendedIdealOfDefinition
      ⟨P.extendedIdealOfDefinition, P.fg_extendedIdealOfDefinition, rfl⟩ :=
  (spa_def Aplus ▸ Set.inter_subset_left).trans
    (cont_subset_spvOfIdeal_extendedIdealOfDefinition P)

/-- The trace of `spa Aplus` on `Spv (A, IA)` is pro-constructible — the intersection of
the closed trace of `Cont A` (Corollary 7.12) with the pro-constructible trace of the
sub-unit locus. At a ring of integral elements this is the first half of Wedhorn's
Theorem 7.35. -/
theorem isProConstructible_val_preimage_spa (P : PairOfDefinition A) (Aplus : Subring A) :
    IsProConstructible (Subtype.val ⁻¹' spa Aplus :
      Set (spvOfIdeal P.extendedIdealOfDefinition
        ⟨P.extendedIdealOfDefinition, P.fg_extendedIdealOfDefinition, rfl⟩)) := by
  have := spectralSpace_spvOfIdeal P.extendedIdealOfDefinition
    ⟨P.extendedIdealOfDefinition, P.fg_extendedIdealOfDefinition, rfl⟩
  rw [spa_def, Set.preimage_inter]
  exact (isClosed_val_preimage_cont P).isProConstructible.inter
    (isProConstructible_val_preimage_setOfPred_forall_vle_one _ _ (Aplus : Set A))

/-- `spa Aplus` is a spectral space, from an explicit pair of definition: its trace on the
spectral space `Spv (A, IA)` is pro-constructible, pro-constructible subspaces of spectral
spaces are spectral, and `spa Aplus` is homeomorphic to that trace. At a ring of integral
elements this is Wedhorn's Theorem 7.35; the instance below supplies it for any Huber ring
without naming a pair. -/
theorem spectralSpace_spa_of_pairOfDefinition (P : PairOfDefinition A) (Aplus : Subring A) :
    SpectralSpace (spa Aplus) := by
  have := spectralSpace_spvOfIdeal P.extendedIdealOfDefinition
    ⟨P.extendedIdealOfDefinition, P.fg_extendedIdealOfDefinition, rfl⟩
  have := (isProConstructible_val_preimage_spa P Aplus).spectralSpace
  -- Both sides carry the topology induced from `Spv A`, so the embedding of the subspace
  -- restricts to a homeomorphism from the preimage of `spa Aplus` onto it.
  let e := Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
    (Subtype.range_val (s := (spvOfIdeal P.extendedIdealOfDefinition
      ⟨P.extendedIdealOfDefinition, P.fg_extendedIdealOfDefinition, rfl⟩ : Set (Spv A))) ▸
      spa_subset_spvOfIdeal P Aplus)
  -- `Topology.IsOpenEmbedding.spectralSpace` transfers along `e`, once `e` has carried
  -- compactness across; a homeomorphism is in particular an open embedding.
  have : CompactSpace (spa Aplus) := e.compactSpace
  exact e.symm.isOpenEmbedding.spectralSpace

/-- **Wedhorn Theorem 7.35** (at a ring of integral elements): over a Huber ring, `spa Aplus`
is a spectral space — by instance synthesis, with the pair of definition chosen from
`IsHuberRing.nonempty_pairOfDefinition`. -/
instance [IsHuberRing A] (Aplus : Subring A) : SpectralSpace (spa Aplus) :=
  (IsHuberRing.nonempty_pairOfDefinition (A := A)).elim
    fun P ↦ spectralSpace_spa_of_pairOfDefinition P Aplus

end TauCeti.ValuationSpectrum
