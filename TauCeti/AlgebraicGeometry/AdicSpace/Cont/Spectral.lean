/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Cont.OfIdeal
public import TauCeti.AlgebraicGeometry.AdicSpace.SpvOfIdeal.Spectral

/-!
# `Cont A` is a spectral space: the second half of Wedhorn's Corollary 7.12

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Corollary 7.12.**

The continuous points of the valuation spectrum of a Huber ring form a spectral space. Wedhorn
draws this as a corollary of Theorem 7.10: `Cont A` is closed in `Spv (A, IA)`, and a closed
subspace of a spectral space is spectral.

The closedness half is `TauCeti.ValuationSpectrum.isClosed_val_preimage_cont`; this file draws
the conclusion. A closed subset is in particular pro-constructible, hence spectral in the
spectral space `Spv (A, IA)`, so
`TauCeti.spectralSpace_of_isEmbedding` carries it back along the subtype embedding, using the
Theorem 7.10 inclusion `Cont A ⊆ Spv (A, IA)`.

The argument is run on the subspace and transported back along a homeomorphism rather than
carried out in `Spv A`, because the inclusion `Spv (A, IA) → Spv A` is not a spectral map
(Remark 7.6) and the general preservation theorems are therefore unavailable along it.

## Main results

* `TauCeti.ValuationSpectrum.spectralSpace_cont_of_pairOfDefinition` : `Cont A` is a spectral
  space, from an explicit pair of definition.
* The `SpectralSpace (cont A)` instance for a Huber ring, which names no pair.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **Wedhorn Corollary 7.12**, the spectrality half, from an explicit pair of definition: the
trace of `Cont A` on `Spv (A, IA)` is closed, hence pro-constructible, and `Cont A` is
homeomorphic to that trace. -/
theorem spectralSpace_cont_of_pairOfDefinition (P : PairOfDefinition A) :
    SpectralSpace (cont A) := by
  -- `IsClosed.isProConstructible` reads the spectrality of `Spv (A, IA)` off the context.
  have := spectralSpace_spvOfIdeal P.extendedIdealOfDefinition
    ⟨P.extendedIdealOfDefinition, P.fg_extendedIdealOfDefinition, rfl⟩
  have hsub : cont A ⊆ Set.range ((↑) : spvOfIdeal P.extendedIdealOfDefinition
      ⟨P.extendedIdealOfDefinition, P.fg_extendedIdealOfDefinition, rfl⟩ → Spv A) := by
    rw [Subtype.range_val]
    exact cont_subset_spvOfIdeal_extendedIdealOfDefinition P
  exact spectralSpace_of_isEmbedding Topology.IsEmbedding.subtypeVal hsub
    (isClosed_val_preimage_cont P).isProConstructible.spectralSpace

/-- **Wedhorn Corollary 7.12**: over a Huber ring the continuous points form a spectral space —
by instance synthesis, with the pair of definition chosen from
`IsHuberRing.nonempty_pairOfDefinition`, so that the statement mentions no pair. That the space
does not depend on the pair is already true by construction: `TauCeti.ValuationSpectrum.cont` is
defined from the topology of `A` alone. -/
instance [IsHuberRing A] : SpectralSpace (cont A) :=
  (IsHuberRing.nonempty_pairOfDefinition (A := A)).elim spectralSpace_cont_of_pairOfDefinition

end TauCeti.ValuationSpectrum
