/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries
public import TauCeti.Topology.Algebra.UniformRing
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

`A` is not assumed complete or Hausdorff: following the roadmap, `A⟨X₁,…,Xₖ⟩` is *defined* as
the separated completion of the ring `TauCeti.Huber.weightedRestrictedSubring` of restricted
power series at the trivial weight family `Tᵢ = {1}` (Wedhorn Example 5.54), so for zero
variables it is the separated completion of `A` itself. Being a completion, it is a complete
Hausdorff topological `A`-algebra, with all of that structure found by instance search.

## Main definitions

* `TauCeti.Huber.restrictedMvPowerSeriesCompletion`: the completed restricted power-series
  algebra `A⟨X₁,…,Xₖ⟩`.
* `TauCeti.Huber.IsStronglyNoetherian`: every `A⟨X₁,…,Xₖ⟩` is a noetherian ring.

## Main results

* `TauCeti.Huber.continuous_algebraMap_restrictedMvPowerSeriesCompletion`: the structure map
  `A → A⟨X₁,…,Xₖ⟩` is continuous.
* `TauCeti.Huber.IsStronglyNoetherian.of_discreteTopology`: a noetherian ring with the
  discrete topology is strongly noetherian — over a discrete ring the restricted series are
  the polynomials, already complete, and the Hilbert basis theorem applies. In particular
  `ℤ`, every field, and every noetherian ring discretely topologised witness the predicate.

The comparison of `A⟨X₁,…,Xₖ⟩` with the plain restricted-series ring when `A` is itself
complete and Hausdorff, the iteration `A⟨X⟩⟨Y⟩ ≅ A⟨X,Y⟩`, and the stability of noetherianness
under quotients belong to the later roadmap milestones of Layer 0.5 and are not proved here.

## Provenance

AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08` formalises an `IsStronglyNoetherian` class in
`projects/AdicSpaces/Adic spaces/RestrictedPowerSeries.lean` and `TateAcyclicity.lean`. It
was consulted and not ported: AINTLIB quantifies over the *uncompleted* restricted-series
subring, which matches Wedhorn only for complete Hausdorff rings, whereas the roadmap — and
this file — define `A⟨X₁,…,Xₖ⟩` through the separated completion so that the predicate is
meaningful for arbitrary Tate rings. Nothing was copied.
-/

public section

namespace TauCeti.Huber

variable (k : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- The completed restricted power-series algebra `A⟨X₁,…,Xₖ⟩` of a nonarchimedean commutative
ring `A`: the separated completion of the ring of restricted power series in `k` variables —
the weighted ring `TauCeti.Huber.weightedRestrictedSubring` at the trivial weight family
`Tᵢ = {1}` — with respect to the uniformity of its ring topology. For `k = 0` this is the
separated completion of `A` itself. -/
noncomputable abbrev restrictedMvPowerSeriesCompletion : Type _ :=
  UniformSpace.Completion
    (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)

/-- The structure map `A → A⟨X₁,…,Xₖ⟩` is continuous. -/
theorem continuous_algebraMap_restrictedMvPowerSeriesCompletion :
    Continuous (algebraMap A (restrictedMvPowerSeriesCompletion k A)) := by
  have h : Continuous (algebraMap A (weightedRestrictedSubring
      (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)) :=
    (continuous_weightedC isWeightFamily_one_weight).congr fun a ↦ Subtype.ext (by simp)
  exact ((UniformSpace.Completion.continuous_coe _).comp h).congr fun a ↦
    (UniformSpace.Completion.algebraMap_def _ _ a).symm

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
        (UniformSpace.Completion.completeRingEquivSelf _).symm)

end TauCeti.Huber
