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
* `TauCeti.Huber.isNoetherianRing_completion_of_isStronglyNoetherian`: the zero-variable
  *consequence* of the predicate — strong noetherianness quantifies over every `k`, and its
  `k = 0` component says the separated completion `Â` is noetherian. The identification behind it,
  `TauCeti.Huber.restrictedMvPowerSeriesCompletionFinZeroEquiv` in
  `TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Completion`, is topological and not merely a
  ring isomorphism: at `k = 0` the coefficient index `Fin 0 →₀ ℕ` is a singleton, so a basic
  neighbourhood is cut out by the single coefficient and the two neighbourhood bases correspond.
* `TauCeti.Huber.isNoetherianRing_of_isStronglyNoetherian`: the other half of the same
  zero-variable statement — `A` itself is noetherian when it is already complete and Hausdorff,
  since then the separated completion does nothing. Completeness is an explicit hypothesis
  rather than an instance because it must be stated against the group uniformity introduced
  below, not against whichever `UniformSpace A` a consumer has in scope.

* `TauCeti.Huber.isStronglyNoetherian_congr`: strong noetherianness is invariant under a
  bicontinuous ring isomorphism. Layer 4.1 takes `IsStronglyNoetherian A` as a hypothesis while
  the ring in question is presented in more than one way, so the hypothesis has to survive the
  comparison isomorphisms; this is what makes that legitimate. Continuity is needed in *both*
  directions and is not automatic — `weightedMapCompletion` is built from
  `UniformSpace.Completion.mapRingHom`, which induces nothing on completions from a
  discontinuous map.

Neither the iteration `A⟨X⟩⟨Y⟩ ≅ A⟨X,Y⟩` nor the stability of noetherianness under quotients is
proved here; those belong to the later roadmap milestones of Layer 0.5.

## Provenance

AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08` formalises an `IsStronglyNoetherian` class in
`projects/AdicSpaces/Adic spaces/RestrictedPowerSeries.lean` and `TateAcyclicity.lean`. It
was consulted and not ported: its class quantifies over the *uncompleted* restricted-series
subring, while the class here is stated over the separated completion
`TauCeti.Huber.restrictedMvPowerSeriesCompletion`, whose own module records that contrast.
Nothing was copied.

That same contrast is why AINTLIB's `isStronglyNoetherian_congr`
(`projects/AdicSpaces/Adic spaces/StronglyNoetherianTransport.lean`) does not transfer either:
it transports along `restrictedMvPowerSeriesEquiv`, built by hand on the uncompleted subring.
The proof *shape* — coefficientwise transport in both directions, mutually inverse by the
functor laws, then noetherianness along the resulting surjection — is the same, but here it
runs one level up, on `TauCeti.Huber.weightedMapCompletion`, and the bridge is definitional:
`restrictedMvPowerSeriesCompletion k A` is by definition the completion of the weighted
subring at the trivial weight family, which is exactly that map's shape.
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

/-! ### Zero variables -/

section ZeroVariables

variable {A}

/-- **The zero-variable consequence of strong noetherianness: the separated completion `Â` is
noetherian.** This is the `k = 0` component of `TauCeti.Huber.IsStronglyNoetherian` — which
quantifies over every `k`, so this is one consequence of it rather than a characterisation —
transported along the identification of `A⟨⟩` with `Â`. -/
theorem isNoetherianRing_completion_of_isStronglyNoetherian [IsStronglyNoetherian A] :
    letI := IsTopologicalAddGroup.rightUniformSpace A
    letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
    IsNoetherianRing (UniformSpace.Completion A) :=
  let _ := IsTopologicalAddGroup.rightUniformSpace A
  let _ : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  isNoetherianRing_of_ringEquiv _ restrictedMvPowerSeriesCompletionFinZeroEquiv

/-- **A complete Hausdorff strongly noetherian ring is noetherian.** `A⟨⟩` is the separated
completion of `A`, so when `A` is already complete and Hausdorff the completion does nothing and
the noetherianness of `A⟨⟩` is noetherianness of `A`.

Completeness is a hypothesis rather than an instance because it has to be *about the right
uniformity*. `A` carries only a topology here; the uniformity is the right group uniformity
`IsTopologicalAddGroup.rightUniformSpace A`, which is what
`TauCeti.Huber.isNoetherianRing_completion_of_isStronglyNoetherian` completes against, and an
ambient `[CompleteSpace A]` would be about whichever `UniformSpace A` instance a consumer
happened to have in scope. Hausdorffness needs no such care: `T0Space` is a property of the
topology, and for a uniform additive group it is the separation the completion asks for. -/
theorem isNoetherianRing_of_isStronglyNoetherian [IsStronglyNoetherian A] [T0Space A]
    (hcomplete : letI := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A) :
    IsNoetherianRing A :=
  let _ := IsTopologicalAddGroup.rightUniformSpace A
  let _ : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  let _ : CompleteSpace A := hcomplete
  let _ : IsNoetherianRing (UniformSpace.Completion A) :=
    isNoetherianRing_completion_of_isStronglyNoetherian
  isNoetherianRing_of_ringEquiv _ (UniformSpace.Completion.completeRingEquivSelf A)

end ZeroVariables

/-! ### Transport along a bicontinuous ring isomorphism -/

section Transport

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [CommRing B] [TopologicalSpace B] [NonarchimedeanRing B]

/-- **The isomorphism `A⟨X₁,…,Xₖ⟩ ≃+* B⟨X₁,…,Xₖ⟩` induced by a bicontinuous ring isomorphism
`e : A ≃+* B`**, acting coefficientwise. Continuity of `e` and of `e.symm` are both hypotheses;
neither follows from the other for a bare `RingEquiv`. -/
-- Built from `weightedMapCompletion` in each direction; the two are mutually inverse by
-- `weightedMapCompletion_id` and `weightedMapCompletion_comp`. Both continuity hypotheses are
-- load-bearing because `weightedMapCompletion` goes through `UniformSpace.Completion.mapRingHom`,
-- which induces nothing on completions from a discontinuous map.
private noncomputable def restrictedMvPowerSeriesCompletionCongr (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (k : ℕ) :
    restrictedMvPowerSeriesCompletion k A ≃+* restrictedMvPowerSeriesCompletion k B :=
  RingEquiv.ofRingHom
    (weightedMapCompletion (φ := (e : A →+* B)) he isWeightFamily_one_weight
      isWeightFamily_one_weight
      fun _ ↦ by simp)
    (weightedMapCompletion (φ := (e.symm : B →+* A)) he' isWeightFamily_one_weight
      isWeightFamily_one_weight
      fun _ ↦ by simp)
    (by
      rw [weightedMapCompletion_comp he' he isWeightFamily_one_weight isWeightFamily_one_weight
        isWeightFamily_one_weight (fun _ ↦ by simp)
        (fun _ ↦ by simp)]
      simp)
    (by
      rw [weightedMapCompletion_comp he he' isWeightFamily_one_weight isWeightFamily_one_weight
        isWeightFamily_one_weight (fun _ ↦ by simp)
        (fun _ ↦ by simp)]
      simp)

/-- **Strong noetherianness is invariant under a bicontinuous ring isomorphism.** Continuity of
`e` and of `e.symm` are both hypotheses; neither follows from the other for a bare `RingEquiv`. -/
-- Each `A⟨X₁,…,Xₖ⟩` is carried to `B⟨X₁,…,Xₖ⟩` by `restrictedMvPowerSeriesCompletionCongr`, and
-- noetherianness transports along the resulting surjection.
theorem isStronglyNoetherian_congr (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) :
    IsStronglyNoetherian A ↔ IsStronglyNoetherian B := by
  constructor <;> intro h <;> refine ⟨fun k ↦ ?_⟩
  · exact isNoetherianRing_of_ringEquiv _ (restrictedMvPowerSeriesCompletionCongr e he he' k)
  · exact isNoetherianRing_of_ringEquiv _ (restrictedMvPowerSeriesCompletionCongr e he he' k).symm

end Transport

end TauCeti.Huber
