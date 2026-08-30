/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Multiplicity
public import TauCeti.Algebra.Lie.UniversalEnveloping.Module
public import TauCeti.RingTheory.Semisimple.Multiplicity

/-!
# The multiplicity of an irreducible Lie module, through the enveloping algebra

`LieModule.isotypicMultiplicity` of `TauCeti/Algebra/Lie/Multiplicity.lean` is defined and computed
without the universal enveloping algebra, in the same way as the Lie isotypy interface of
`TauCeti/Algebra/Lie/Isotypic.lean`. This file connects it to the ring-level multiplicity theory of
`TauCeti/RingTheory/Semisimple/Multiplicity.lean` across the enveloping-algebra dictionary, so that
the two are one theory rather than two parallel ones: the general invariant is the finrank of the
space of `U(L)`-linear maps `S → M`, and over an algebraically closed field, for a finite
decomposition of `M` into simple `U(L)`-modules and a finite-dimensional simple `S`, it is the
number of factors isomorphic to `S`.

The translation is `TauCeti.UniversalEnvelopingAlgebra.lieModuleHomEquiv`: a morphism of Lie
modules is exactly a `U(L)`-linear map, `R`-linearly in the morphism, so the two morphism spaces
have the same finrank.

## Main results

* `LieModule.isotypicMultiplicity_eq_finrank_linearMap_of_ι_smul`: the invariant is the
  finrank of the space of `U(L)`-linear maps.
* `LieModule.isotypicMultiplicity_eq_natCard_of_linearEquiv_pi`: for a finite decomposition of `M`
  into simple `U(L)`-modules, the multiplicity is the ring-level count of
  `TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi`.

## Roadmap

This is the enveloping-algebra bridge for the `isotypicMultiplicity` target of the decomposition
toolkit in Layer 6 of `TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, in the same
role that `TauCeti/Algebra/Lie/UniversalEnveloping/Isotypic.lean` plays for the isotypic component.
-/

public section

open UniversalEnvelopingAlgebra

universe u v w w₁

namespace LieModule

open TauCeti.UniversalEnvelopingAlgebra

section Bridge

variable {R : Type u} {L : Type v} {M : Type w}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [Module (_root_.UniversalEnvelopingAlgebra R L) M]
variable [IsScalarTower R (_root_.UniversalEnvelopingAlgebra R L) M]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- **The invariant is the finrank of an enveloping-algebra morphism space.** For compatible
`U(L)`-actions, `LieModule.isotypicMultiplicity R L M S` is the finrank of the space of
`U(L)`-linear maps `S → M`. -/
theorem isotypicMultiplicity_eq_finrank_linearMap_of_ι_smul
    (hM : ∀ (x : L) (m : M), ι R x • m = ⁅x, m⁆)
    (S : Type w₁) [AddCommGroup S] [Module R S] [LieRingModule L S]
    [Module U S] [IsScalarTower R U S]
    (hS : ∀ (x : L) (s : S), ι R x • s = ⁅x, s⁆) :
    isotypicMultiplicity R L M S = Module.finrank R (S →ₗ[U] M) :=
  (isotypicMultiplicity_def R L M S).trans (lieModuleHomEquiv hS hM).finrank_eq

end Bridge

section Count

variable {K : Type u} {L : Type v} {M : Type w}
variable [Field K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
variable [Module (_root_.UniversalEnvelopingAlgebra K L) M]
variable [IsScalarTower K (_root_.UniversalEnvelopingAlgebra K L) M]

local notation "U" => _root_.UniversalEnvelopingAlgebra K L

/-- **The multiplicity is the ring-level multiplicity.** If a compatible `U(L)`-module `M` is a
finite product of simple `U(L)`-modules, the multiplicity of a simple, finite-dimensional `S`
counts the factors isomorphic to `S`. This is
`TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi` read through the enveloping-algebra
dictionary, so the Lie-level count of
`LieModule.isotypicMultiplicity_eq_ncard_of_isInternal` and the ring-level one compute the same
number. -/
theorem isotypicMultiplicity_eq_natCard_of_linearEquiv_pi
    (hM : ∀ (x : L) (m : M), ι K x • m = ⁅x, m⁆)
    (S : Type w₁) [AddCommGroup S] [Module K S] [LieRingModule L S]
    [Module U S] [IsScalarTower K U S] [IsSimpleModule U S] [FiniteDimensional K S]
    (hS : ∀ (x : L) (s : S), ι K x • s = ⁅x, s⁆)
    {κ : Type*} [Finite κ] {N : κ → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module K (N i)]
    [∀ i, Module U (N i)] [∀ i, IsScalarTower K U (N i)] [∀ i, IsSimpleModule U (N i)]
    (e : M ≃ₗ[U] ∀ i, N i) :
    isotypicMultiplicity K L M S = Nat.card {i // Nonempty (S ≃ₗ[U] N i)} := by
  rw [isotypicMultiplicity_eq_finrank_linearMap_of_ι_smul hM S hS,
    TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi e]

end Count

end LieModule
