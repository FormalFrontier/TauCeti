/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Multiplicity
public import TauCeti.Algebra.Lie.UniversalEnveloping.Isotypic
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
* `LieModule.finrank_isotypicComponent`: **the dimension of an isotypic component is the
  multiplicity times the dimension of its type**;
  `LieModule.finrank_of_isotypicComponent_eq_top`: for a module its own isotypic component, that
  dimension count is the dimension of the module; and
  `LieModule.finrank_of_isIsotypicOfType`: the same for a completely reducible module which is
  itself isotypic.

## The dimension of an isotypic component

`LieModule.finrank_isotypicComponent` is a statement of Lie module theory alone — no enveloping
algebra occurs in it — but its proof runs through the dictionary, which is why it lives here
rather than in `TauCeti/Algebra/Lie/Multiplicity.lean`: the isotypic component is carried to
Mathlib's `isotypicComponent` over `U(L)` by
`LieModule.lieSubmoduleOrderIso_isotypicComponent`, where
`TauCeti.finrank_isotypicComponent` computes its dimension. The two hypotheses are the ones that
statement needs, finite-dimensionality of `M` and of the irreducible `S`; complete reducibility of
`M` is not among them, an isotypic component being a sum of copies of `S` in any case. It is not
needed either for `LieModule.finrank_of_isotypicComponent_eq_top`, which reads off the dimension of
a module its own `S`-isotypic component; it is needed only to reach that hypothesis from isotypy,
which is what `LieModule.finrank_of_isIsotypicOfType` does.

## Roadmap

This is the enveloping-algebra bridge for the `isotypicMultiplicity` target of the decomposition
toolkit in Layer 6 of `TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, in the same
role that `TauCeti/Algebra/Lie/UniversalEnveloping/Isotypic.lean` plays for the isotypic component.
`LieModule.finrank_isotypicComponent` is that milestone's `finrank_isotypicComponent` target,
"the finrank identity `dim (isotypic component) = m_λ · dim L(λ)`".
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

/-! ### The dimension of an isotypic component -/

section IsotypicComponent

variable {K : Type u} {L : Type v} {M : Type w}
variable [Field K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
variable [FiniteDimensional K M]

open Module (finrank)

/-- **The dimension of an isotypic component is the multiplicity times the dimension of its
type.** For a finite-dimensional Lie module `M` over an algebraically closed field and a
finite-dimensional irreducible `S`, the `S`-isotypic component of `M`
(`LieModule.isotypicComponent`) has dimension `m · dim S`, where `m` is the multiplicity
`LieModule.isotypicMultiplicity`.

This is the counted form of the statement that the isotypic component is `S^{⊕ m}`; nothing is
assumed about `M` beyond finite-dimensionality, since the isotypic component is a sum of copies
of `S` whether or not `M` itself is completely reducible. -/
theorem finrank_isotypicComponent (S : Type w₁) [AddCommGroup S] [Module K S] [LieRingModule L S]
    [LieModule K L S] [FiniteDimensional K S] [IsIrreducible K L S] :
    finrank K (isotypicComponent K L M S) = isotypicMultiplicity K L M S * finrank K S := by
  let := asModule K L M
  let := isScalarTower_asModule K L M
  let := asModule K L S
  let := isScalarTower_asModule K L S
  have hM := asModule_ι_smul K L M
  have hS := asModule_ι_smul K L S
  have : IsSimpleModule (_root_.UniversalEnvelopingAlgebra K L) S :=
    (isIrreducible_iff_isSimpleModule hS).mp inferInstance
  have hrank : finrank K (isotypicComponent K L M S) =
      finrank K ↥(_root_.isotypicComponent (_root_.UniversalEnvelopingAlgebra K L) M S) := by
    let := asModule K L (isotypicComponent K L M S)
    let := isScalarTower_asModule K L (isotypicComponent K L M S)
    have h :=
      ((lieSubmoduleLinearEquiv hM (isotypicComponent K L M S)).restrictScalars K).finrank_eq
    rwa [lieSubmoduleOrderIso_isotypicComponent hM S hS] at h
  rw [hrank, isotypicMultiplicity_eq_finrank_linearMap_of_ι_smul hM S hS,
    TauCeti.finrank_isotypicComponent (k := K)]

/-- **A module exhausted by an isotypic component has dimension the multiplicity times the
dimension of its type.** This is the numerical content of `M ≅ S^{⊕ m}`, and it needs nothing of
`M` beyond finite-dimensionality: the whole hypothesis is that the `S`-isotypic component is all
of `M`. -/
theorem finrank_of_isotypicComponent_eq_top (S : Type w₁) [AddCommGroup S] [Module K S]
    [LieRingModule L S] [LieModule K L S] [FiniteDimensional K S] [IsIrreducible K L S]
    (h : isotypicComponent K L M S = ⊤) :
    finrank K M = isotypicMultiplicity K L M S * finrank K S := by
  rw [← finrank_isotypicComponent (M := M) S, h]
  exact (LieModuleEquiv.ofTop K L M).toLinearEquiv.finrank_eq.symm

/-- **An isotypic module has dimension the multiplicity times the dimension of its type.** This is
the form a decomposition argument consumes: having checked that every irreducible Lie submodule of
a completely reducible `M` is equivalent to `S`, the dimension of `M` is `m · dim S` with `m` the
multiplicity. Complete reducibility enters only to turn the isotypy hypothesis into the
component-exhausts-`M` hypothesis of `LieModule.finrank_of_isotypicComponent_eq_top`. -/
theorem finrank_of_isIsotypicOfType (S : Type w₁) [AddCommGroup S] [Module K S]
    [LieRingModule L S] [LieModule K L S] [FiniteDimensional K S] [IsIrreducible K L S]
    [ComplementedLattice (LieSubmodule K L M)] (h : IsIsotypicOfType K L M S) :
    finrank K M = isotypicMultiplicity K L M S * finrank K S := by
  let := asModule K L M
  let := isScalarTower_asModule K L M
  let := asModule K L S
  let := isScalarTower_asModule K L S
  exact finrank_of_isotypicComponent_eq_top S
    ((isotypicComponent_eq_top_iff_of_ι_smul (asModule_ι_smul K L M) S
      (asModule_ι_smul K L S)).mpr h)

end IsotypicComponent

end LieModule
