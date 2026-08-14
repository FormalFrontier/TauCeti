/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
public import TauCeti.Topology.UniformSpace.DiscreteUniformity
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Strong noetherianness of a nonarchimedean ring

The completed restricted power-series algebras `A⟨X₁,…,Xₖ⟩` of a nonarchimedean commutative
ring `A`, and the predicate they support: `A` is *strongly noetherian* when every one of them
is noetherian. This is the hypothesis of Wedhorn's Theorem 8.28 (*Adic Spaces*,
arXiv:1910.05934v1) — the strongly noetherian form of Tate acyclicity — which Wedhorn states
for Tate rings; the predicate itself needs only the nonarchimedean topology, so it is stated
here in that generality.

`A` is not assumed complete or Hausdorff: following the roadmap, `A⟨X₁,…,Xₖ⟩` — the
`TauCeti.Huber.restrictedMvPowerSeriesCompletion` of
`TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Completion` — is *defined* as the separated
completion of the ring of restricted power series at the trivial weight family `Tᵢ = {1}`
(Wedhorn Example 5.54), so for zero variables it is the separated completion of `A` itself.
Where that ring of restricted power series is already complete and Hausdorff, the completion
does nothing: `TauCeti.Huber.restrictedMvPowerSeriesCompletionEquiv`, in
`TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete`, is the identification, and the
discrete case below is proved through it.

## Main definitions

* `TauCeti.Huber.IsStronglyNoetherian`: every `A⟨X₁,…,Xₖ⟩` is a noetherian ring.

## Main results

* `TauCeti.Huber.IsStronglyNoetherian.of_discreteTopology`: a noetherian ring with the
  discrete topology is strongly noetherian — over a discrete ring the restricted series are
  the polynomials, already complete, and the Hilbert basis theorem applies. In particular
  `ℤ`, every field, and every noetherian ring discretely topologised witness the predicate.

The iteration `A⟨X⟩⟨Y⟩ ≅ A⟨X,Y⟩` and the stability of noetherianness under quotients belong
to the later roadmap milestones of Layer 0.5 and are not proved here.

## Provenance

AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08` formalises an `IsStronglyNoetherian` class in
`projects/AdicSpaces/Adic spaces/RestrictedPowerSeries.lean` and `TateAcyclicity.lean`. It
was consulted and not ported: its class quantifies over the *uncompleted* restricted-series
subring, while the class here is stated over the separated completion
`TauCeti.Huber.restrictedMvPowerSeriesCompletion`, whose own module records that contrast.
Nothing was copied.
-/

public section

namespace TauCeti.Huber

variable (k : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- A nonarchimedean commutative ring is **strongly noetherian** when every completed
restricted power-series algebra `A⟨X₁,…,Xₖ⟩` over it is noetherian. For `k = 0` this asks
that the separated completion of `A` be noetherian.

This is the hypothesis of Wedhorn's Theorem 8.28, the strongly noetherian form of Tate
acyclicity; Wedhorn states it for Tate rings, and every complete rank-one nonarchimedean
field satisfies it (BGR 5.2.6 — not yet formalised). -/
@[mk_iff]
class IsStronglyNoetherian : Prop where
  isNoetherianRing (k : ℕ) : IsNoetherianRing (restrictedMvPowerSeriesCompletion k A)

/-- The defining property, as an instance: with `[IsStronglyNoetherian A]` in scope, each
`A⟨X₁,…,Xₖ⟩` is a noetherian ring by typeclass resolution. -/
instance (k : ℕ) [IsStronglyNoetherian A] :
    IsNoetherianRing (restrictedMvPowerSeriesCompletion k A) :=
  IsStronglyNoetherian.isNoetherianRing k

/-! ### The discrete case -/

/-- **A noetherian ring with the discrete topology is strongly noetherian.** This is the
nondegenerate family of witnesses for `IsStronglyNoetherian` — `ℤ`, any field, any noetherian
ring, all discretely topologised. -/
instance IsStronglyNoetherian.of_discreteTopology [DiscreteTopology A] [IsNoetherianRing A] :
    IsStronglyNoetherian A where
  isNoetherianRing k := by
    have : DiscreteTopology (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight) := discreteTopology_weightedRestrictedSubring
    have : DiscreteUniformity (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight) := DiscreteUniformity.of_discreteTopology
    exact isNoetherianRing_of_ringEquiv _
      ((weightedPolynomialEquiv _ isWeightFamily_one_weight).trans
        (restrictedMvPowerSeriesCompletionEquiv k A).symm)

end TauCeti.Huber
