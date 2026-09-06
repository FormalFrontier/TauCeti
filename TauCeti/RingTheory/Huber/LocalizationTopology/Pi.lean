/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Completion

/-!
# The structure map into a family of rational localisations

For a finite set `T` of numerators, the rational localisations `A⟨T/t⟩` for `t ∈ T` carry a single
structure map out of `A` apiece. This file bundles them into one ring homomorphism
`A →+* ∀ t : T, A⟨T/t⟩` and records that it is continuous. No hypothesis relating the members of
`T` is needed for either, so none is imposed: what is defined here is the product map for an
arbitrary finite `T`.

The family `(R(T/t))_{t ∈ T}` is a cover of `Spa(A,A⁺)` — a *standard rational cover* — precisely
when `T` generates the unit ideal, by
`TauCeti.ValuationSpectrum.spa_eq_biUnion_rationalSubset_of_span_eq_top`. Under that hypothesis
this map is the comparison whose faithful flatness and injectivity Wedhorn's Corollary 8.32
asserts. Neither the hypothesis nor those conclusions appear below; this is the map they are
about.

## Implementation notes

The localisations are given as a *family* `S : T → Type*`, one type per numerator, because that is
how the rest of this development takes a localisation — as a parameter satisfying
`IsLocalization.Away`, not as a construction. Their uniform structures are likewise supplied,
which is why the three `letI` families appear before the codomain: `UniformSpace.Completion (S t)`
is not a ring until `locUniformSpace`, `isUniformAddGroup_locUniformSpace` and
`isTopologicalRing_locUniformSpace` are in scope for that `t`, and the product type mentions them
all.

## Main results

* `TauCeti.Huber.PairOfDefinition.rationalLocalizationPiHom`, with
  `TauCeti.Huber.PairOfDefinition.rationalLocalizationPiHom_apply` its computation rule and
  `TauCeti.Huber.PairOfDefinition.continuous_rationalLocalizationPiHom` its continuity.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Corollary 7.53 for the cover and
  Corollary 8.32 for what this map is for.
-/

public section

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (T : Finset A) (S : ∀ _ : T, Type*) [∀ t : T, CommRing (S t)]
  [∀ t : T, Algebra A (S t)] [∀ t : T, IsLocalization.Away (t : A) (S t)]
  (hden : ∀ t : T, HasDenominatorPower P T (t : A) (S t))

/-- **The structure map into a family of rational localisations**: the tuple of the structure maps
`A → A⟨T/t⟩`, one for each numerator `t ∈ T`. The family is a standard rational cover exactly when
`Ideal.span (T : Set A) = ⊤`, which nothing here requires. -/
noncomputable def rationalLocalizationPiHom :
    letI : ∀ t : T, UniformSpace (S t) := fun t ↦ locUniformSpace P T (t : A) (S t) (hden t)
    letI : ∀ t : T, IsUniformAddGroup (S t) := fun t ↦
      isUniformAddGroup_locUniformSpace P T (t : A) (S t) (hden t)
    letI : ∀ t : T, IsTopologicalRing (S t) := fun t ↦
      isTopologicalRing_locUniformSpace P T (t : A) (S t) (hden t)
    A →+* ∀ t : T, UniformSpace.Completion (S t) :=
  letI : ∀ t : T, UniformSpace (S t) := fun t ↦ locUniformSpace P T (t : A) (S t) (hden t)
  letI : ∀ t : T, IsUniformAddGroup (S t) := fun t ↦
    isUniformAddGroup_locUniformSpace P T (t : A) (S t) (hden t)
  letI : ∀ t : T, IsTopologicalRing (S t) := fun t ↦
    isTopologicalRing_locUniformSpace P T (t : A) (S t) (hden t)
  RingHom.pi fun t ↦ toCompletionLoc P T (t : A) (S t) (hden t)

/-- Each component of `TauCeti.Huber.PairOfDefinition.rationalLocalizationPiHom` is the structure
map into that rational localisation. The body is not exported, so this is how a consumer computes
with it. -/
@[simp]
theorem rationalLocalizationPiHom_apply (a : A) (t : T) :
    letI : ∀ t : T, UniformSpace (S t) := fun t ↦ locUniformSpace P T (t : A) (S t) (hden t)
    letI : ∀ t : T, IsUniformAddGroup (S t) := fun t ↦
      isUniformAddGroup_locUniformSpace P T (t : A) (S t) (hden t)
    letI : ∀ t : T, IsTopologicalRing (S t) := fun t ↦
      isTopologicalRing_locUniformSpace P T (t : A) (S t) (hden t)
    rationalLocalizationPiHom P T S hden a t = toCompletionLoc P T (t : A) (S t) (hden t) a := (rfl)

/-- **The structure map into a family of rational localisations is continuous**, the product
topology on the codomain being the one each factor carries. -/
theorem continuous_rationalLocalizationPiHom :
    letI : ∀ t : T, UniformSpace (S t) := fun t ↦ locUniformSpace P T (t : A) (S t) (hden t)
    letI : ∀ t : T, IsUniformAddGroup (S t) := fun t ↦
      isUniformAddGroup_locUniformSpace P T (t : A) (S t) (hden t)
    letI : ∀ t : T, IsTopologicalRing (S t) := fun t ↦
      isTopologicalRing_locUniformSpace P T (t : A) (S t) (hden t)
    Continuous (rationalLocalizationPiHom P T S hden) :=
  continuous_pi fun t ↦ continuous_toCompletionLoc P T (t : A) (S t) (hden t)

end TauCeti.Huber.PairOfDefinition

end
