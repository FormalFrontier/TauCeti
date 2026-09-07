/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.Basic
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
public import TauCeti.Topology.UniformSpace.DiscreteUniformity
public import Mathlib.RingTheory.Polynomial.Basic

import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Iterate
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Surjective

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
* `TauCeti.Huber.IsStronglyNoetherian.restrictedMvPowerSeriesCompletion`: over a Huber base the
  predicate passes to `A⟨X₁,…,Xₖ⟩`, so a strongly noetherian ring stays strongly noetherian under
  the construction. This is the iteration isomorphism `A⟨X⟩⟨Y⟩ ≅ A⟨X,Y⟩` of
  `TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Iterate` read as a statement about the
  predicate; `[IsHuberRing A]` is what that isomorphism asks of the base, and the predicate itself
  does not.
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

* `TauCeti.Huber.IsStronglyNoetherian.of_surjective`: strong noetherianness passes along a
  continuous surjection carrying neighbourhoods of zero onto neighbourhoods of zero, out of a
  complete Hausdorff strongly noetherian ring whose `nhds 0` is countably generated.
  `IsOpenQuotientMap.isStronglyNoetherian` is the form taking the bundled structure. Countable
  generation is not decoration: it is what supplies the shrinking family the lifted coefficients
  are drawn from, and a complete Hausdorff strongly noetherian ring need not have it.

  This is the half of Wedhorn's Proposition & Definition 6.36(ii) that does not depend on which
  presentation is chosen: a ring *strictly* topologically of finite type over `A` is an open
  quotient of some
  `A⟨X₁,…,Xₖ⟩`, so once that ring is known to be strongly noetherian the quotient is too. The
  unqualified `TauCeti.Huber.IsTopologicallyFiniteType` is weaker — it allows an arbitrary finite
  weight family — and is not what this serves.

* `TauCeti.Huber.isStronglyNoetherian_congr`: strong noetherianness is invariant under a
  bicontinuous ring isomorphism. Layer 4.1 takes `IsStronglyNoetherian A` as a hypothesis while
  the ring in question is presented in more than one way, so the hypothesis has to survive the
  comparison isomorphisms; this is what makes that legitimate. Continuity is needed in *both*
  directions and is not automatic — `weightedMapCompletion` is built from
  `UniformSpace.Completion.mapRingHom`, which induces nothing on completions from a
  discontinuous map.

What is not here is the assembly that turns the result above into Wedhorn's statement: that a
ring *strictly* topologically of finite type over a strongly noetherian `A` is again strongly
noetherian. That needs `TauCeti.Huber.IsStrictlyTopologicallyFiniteType` unfolded to its open
quotient `A⟨X₁,…,Xₖ⟩ ↠ B` and the result above applied to it. The unqualified
`TauCeti.Huber.IsTopologicallyFiniteType` presents `B` as a quotient of the completion of a
*weighted* `A⟨X⟩_T` for an arbitrary finite weight family, and is not covered at all.

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

/-! ### The completed polynomial algebra -/

/-- **Strong noetherianity passes to `A⟨X₁,…,Xₖ⟩`.** Over a Huber base, a completed restricted
power-series algebra over a strongly noetherian ring is again strongly noetherian, so the
construction can be iterated without leaving the class.

`[IsHuberRing A]` is asked here and not by the predicate: it is what the iteration isomorphism
of `TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Iterate` requires of the base. -/
instance IsStronglyNoetherian.restrictedMvPowerSeriesCompletion [IsHuberRing A]
    [IsStronglyNoetherian A] (k : ℕ) :
    IsStronglyNoetherian (restrictedMvPowerSeriesCompletion k A) where
  isNoetherianRing m := isNoetherianRing_of_ringEquiv _ (iterateRingEquiv k m A)

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
-- The equiv is `TauCeti.Huber.weightedMapCompletionEquiv` at the constant weight family; both
-- continuity hypotheses are load-bearing there.
private noncomputable def restrictedMvPowerSeriesCompletionCongr (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (k : ℕ) :
    restrictedMvPowerSeriesCompletion k A ≃+* restrictedMvPowerSeriesCompletion k B :=
  weightedMapCompletionEquiv e he he' isWeightFamily_one_weight isWeightFamily_one_weight
    (fun _ ↦ by simp) (fun _ ↦ by simp)

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

/-! ### Descent along an open quotient map -/

section Quotient

variable {A B : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [NonarchimedeanRing A] [CompleteSpace A] [T0Space A] [(nhds (0 : A)).IsCountablyGenerated]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B]
  [CompleteSpace B] [T0Space B]

/-- **Strong noetherianness passes along a continuous surjection** carrying neighbourhoods of zero
onto neighbourhoods of zero. If `A` is complete, Hausdorff, strongly noetherian and has countably
generated `𝓝 0`, and `B` is complete and Hausdorff, then `B` is strongly noetherian.

The hypothesis is stated as the filter inequality the proof consumes. Alongside the surjectivity
assumed here it is the filter-level formulation of `IsOpenMap π`, not a weakening of it — for a
surjective continuous additive map the two say the same thing, since openness of a group
homomorphism is decided at zero. `IsOpenQuotientMap.isStronglyNoetherian` is the form for a caller
holding the bundled open-quotient structure.

Openness of `π` is what carries the hypothesis: it is what makes `A⟨Y₁,…,Yₖ⟩ → B⟨Y₁,…,Yₖ⟩`
surjective, by `TauCeti.Huber.weightedMap_one_weight_surjective`. Completeness and
separation of both rings are what let `TauCeti.Huber.restrictedMvPowerSeriesCompletionEquiv` read
that surjection back as one of the completed algebras. Countable generation of `𝓝 (0 : A)` is a
further hypothesis, carried by the section: it is what supplies the shrinking family the lifted
coefficients are drawn from, and it is not implied by the other three.

This is the presentation-independent half of Wedhorn's Proposition & Definition 6.36(ii): a ring
*strictly* topologically of finite type over `A` is an open quotient of some `A⟨X₁,…,Xₖ⟩`
(`TauCeti.Huber.IsStrictlyTopologicallyFiniteType`), so the statement that such a ring is strongly
noetherian reduces to this together with strong noetherianness of `A⟨X₁,…,Xₖ⟩` itself. The
unqualified `TauCeti.Huber.IsTopologicallyFiniteType` presents `B` as a quotient of a *weighted*
`A⟨X⟩_T` instead, and is not covered. -/
theorem IsStronglyNoetherian.of_surjective [IsStronglyNoetherian A] {π : A →+* B}
    (hπ : Continuous π) (hsurj : Function.Surjective π)
    (hnhds : nhds (0 : B) ≤ Filter.map π (nhds (0 : A))) : IsStronglyNoetherian B := by
  refine ⟨fun k ↦ ?_⟩
  refine isNoetherianRing_of_surjective _ _
    (((restrictedMvPowerSeriesCompletionEquiv k B).symm.toRingHom.comp
      (weightedMap hπ isWeightFamily_one_weight isWeightFamily_one_weight
        fun _ ↦ by simp)).comp (restrictedMvPowerSeriesCompletionEquiv k A).toRingHom) ?_
  simp only [RingHom.coe_comp]
  exact ((restrictedMvPowerSeriesCompletionEquiv k B).symm.surjective.comp
    (weightedMap_one_weight_surjective hπ hsurj hnhds)).comp
    (restrictedMvPowerSeriesCompletionEquiv k A).surjective

/-- **The open-quotient form of `TauCeti.Huber.IsStronglyNoetherian.of_surjective`**, for a caller
holding the bundled structure — which is what `TauCeti.Huber.IsStrictlyTopologicallyFiniteType`
hands over. -/
theorem _root_.IsOpenQuotientMap.isStronglyNoetherian [IsStronglyNoetherian A] {π : A →+* B}
    (hπ : IsOpenQuotientMap π) : IsStronglyNoetherian B :=
  IsStronglyNoetherian.of_surjective hπ.continuous hπ.surjective
    (map_zero π ▸ hπ.isOpenMap.nhds_le 0)

end Quotient

end TauCeti.Huber
