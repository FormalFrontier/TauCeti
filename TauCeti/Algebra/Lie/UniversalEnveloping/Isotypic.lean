/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleModule.Isotypic
public import TauCeti.Algebra.Lie.Isotypic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Module

/-!
# Isotypic Lie modules through the universal enveloping algebra

This file transports Mathlib's isotypic-module interface across the universal-enveloping-algebra
dictionary. For an irreducible target type, semisimplicity enters only in the characterization of
an isotypic module by its unique component.

The generic equivalence and submodule interfaces live with the rest of the enveloping-algebra
dictionary in `TauCeti.Algebra.Lie.UniversalEnveloping.Module`. The UEA-independent Lie-level
predicates and component live in `TauCeti.Algebra.Lie.Isotypic`; this file identifies them with
Mathlib's `IsIsotypicOfType`, `IsIsotypic`, and `isotypicComponent` through those interfaces.

## Main results

* `LieModule.isIsotypicOfType_iff_isIsotypicOfType_of_ι_smul`: fixed-type isotypy transport
  for compatible actions.
* `LieModule.isIsotypic_iff_isIsotypic_of_ι_smul`: pairwise isotypy transport for compatible
  actions.
* `LieModule.lieSubmoduleOrderIso_isotypicComponent`: component transport for compatible actions.
* `LieModule.mem_isotypicComponent_iff_mem_isotypicComponent_asModule`: canonical component
  membership normalization.
* `LieModule.isotypicComponent_eq_top_iff_of_ι_smul`: the top-component criterion for an
  irreducible type.

## Roadmap

This is the universal-enveloping-algebra bridge for Layer 6 of the Lie highest-weight roadmap.
It deliberately stops before highest-weight classification: consumers such as Kostant-form
modules can state that all irreducible Lie submodules are equivalent without rebuilding ring-level
isotypic machinery.

## References

* `Mathlib/RingTheory/SimpleModule/Isotypic.lean` (Junyan Xu): the module-theoretic isotypic
  interface and top-component criterion transported through the enveloping-algebra dictionary.
-/

public section

open UniversalEnvelopingAlgebra

universe u v w

namespace LieModule

open TauCeti.UniversalEnvelopingAlgebra

variable (R : Type u) (L : Type v) (M : Type w)
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

section Compatible

variable [Module (_root_.UniversalEnvelopingAlgebra R L) M]
variable [IsScalarTower R (_root_.UniversalEnvelopingAlgebra R L) M]
variable {R L M}

/-- Lie-module isotypy of a fixed type is exactly Mathlib's module isotypy for compatible
`U(L)`-actions. -/
theorem isIsotypicOfType_iff_isIsotypicOfType_of_ι_smul
    (hM : ∀ (x : L) (m : M), ι R x • m = ⁅x, m⁆)
    (S : Type*) [AddCommGroup S] [Module R S] [LieRingModule L S] [LieModule R L S]
    [Module U S] [IsScalarTower R U S]
    (hS : ∀ (x : L) (s : S), ι R x • s = ⁅x, s⁆) :
    IsIsotypicOfType R L M S ↔ _root_.IsIsotypicOfType U M S := by
  rw [isIsotypicOfType_iff]
  constructor
  · intro h Q hQ
    obtain ⟨P, rfl⟩ := (lieSubmoduleOrderIso hM).surjective Q
    let : IsIrreducible R L P :=
      (isSimpleModule_lieSubmoduleOrderIso_iff hM P).mp hQ
    exact (nonempty_lieModuleEquiv_iff_nonempty_linearEquiv hM S hS P).mp (h P)
  · intro h P hP
    let : IsSimpleModule U (lieSubmoduleOrderIso hM P) :=
      (isSimpleModule_lieSubmoduleOrderIso_iff hM P).mpr hP
    exact (nonempty_lieModuleEquiv_iff_nonempty_linearEquiv hM S hS P).mpr
      (h (lieSubmoduleOrderIso hM P))

/-- Lie-module isotypy is exactly Mathlib's module isotypy for a compatible `U(L)`-action. -/
theorem isIsotypic_iff_isIsotypic_of_ι_smul
    (hM : ∀ (x : L) (m : M), ι R x • m = ⁅x, m⁆) :
    IsIsotypic R L M ↔ _root_.IsIsotypic U M := by
  rw [isIsotypic_iff]
  simp only [_root_.IsIsotypic]
  constructor
  · intro h Q hQ
    obtain ⟨P, rfl⟩ := (lieSubmoduleOrderIso hM).surjective Q
    let : Module U P := asModule R L P
    let : IsScalarTower R U P := isScalarTower_asModule R L P
    let : IsIrreducible R L P :=
      (isSimpleModule_lieSubmoduleOrderIso_iff hM P).mp hQ
    exact (isIsotypicOfType_iff_isIsotypicOfType_of_ι_smul hM P
      (asModule_ι_smul R L P) |>.mp (h P)).of_linearEquiv_type
      (lieSubmoduleLinearEquiv hM P)
  · intro h P hP
    let : Module U P := asModule R L P
    let : IsScalarTower R U P := isScalarTower_asModule R L P
    let : IsSimpleModule U (lieSubmoduleOrderIso hM P) :=
      (isSimpleModule_lieSubmoduleOrderIso_iff hM P).mpr hP
    exact isIsotypicOfType_iff_isIsotypicOfType_of_ι_smul hM P
      (asModule_ι_smul R L P) |>.mpr
      ((h (lieSubmoduleOrderIso hM P)).of_linearEquiv_type
        (lieSubmoduleLinearEquiv hM P).symm)

/-- A compatible submodule dictionary maps the Lie isotypic component to Mathlib's
`U(L)`-isotypic component. -/
theorem lieSubmoduleOrderIso_isotypicComponent
    (hM : ∀ (x : L) (m : M), ι R x • m = ⁅x, m⁆)
    (S : Type*) [AddCommGroup S] [Module R S] [LieRingModule L S] [LieModule R L S]
    [Module U S] [IsScalarTower R U S]
    (hS : ∀ (x : L) (s : S), ι R x • s = ⁅x, s⁆) :
    lieSubmoduleOrderIso hM (isotypicComponent R L M S) =
      _root_.isotypicComponent U M S := by
  rw [isotypicComponent_def,
    (lieSubmoduleOrderIso hM).map_sSup_eq_sSup_symm_preimage,
    _root_.isotypicComponent]
  congr 1
  ext Q
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  obtain ⟨P, rfl⟩ := (lieSubmoduleOrderIso hM).surjective Q
  rw [(lieSubmoduleOrderIso hM).symm_apply_apply]
  exact nonempty_lieModuleEquiv_iff_nonempty_linearEquiv hM S hS P

/-- Membership in the Lie isotypic component is membership in the corresponding isotypic component
for compatible `U(L)`-actions. -/
theorem mem_isotypicComponent_iff_mem_isotypicComponent_of_ι_smul
    (hM : ∀ (x : L) (m : M), ι R x • m = ⁅x, m⁆)
    {S : Type*} [AddCommGroup S] [Module R S] [LieRingModule L S] [LieModule R L S]
    [Module U S] [IsScalarTower R U S]
    (hS : ∀ (x : L) (s : S), ι R x • s = ⁅x, s⁆)
    {m : M} :
    m ∈ isotypicComponent R L M S ↔ m ∈ _root_.isotypicComponent U M S := by
  rw [← mem_lieSubmoduleOrderIso hM,
    lieSubmoduleOrderIso_isotypicComponent hM S hS]

/-- For compatible `U(L)`-actions, an irreducible type `S`, and a completely reducible Lie module,
the isotypic component of type `S` is the whole module exactly when the Lie module is isotypic of
type `S`. -/
theorem isotypicComponent_eq_top_iff_of_ι_smul
    (hM : ∀ (x : L) (m : M), ι R x • m = ⁅x, m⁆)
    (S : Type*) [AddCommGroup S] [Module R S] [LieRingModule L S] [LieModule R L S]
    [Module U S] [IsScalarTower R U S]
    (hS : ∀ (x : L) (s : S), ι R x • s = ⁅x, s⁆)
    [IsIrreducible R L S]
    [ComplementedLattice (LieSubmodule R L M)] :
    isotypicComponent R L M S = ⊤ ↔ IsIsotypicOfType R L M S := by
  let : IsSimpleModule U S :=
    (isIrreducible_iff_isSimpleModule hS).mp inferInstance
  let : IsSemisimpleModule U M :=
    (complementedLattice_lieSubmodule_iff_isSemisimpleModule hM).mp inferInstance
  rw [← map_eq_top_iff (lieSubmoduleOrderIso hM),
    lieSubmoduleOrderIso_isotypicComponent hM S hS,
    _root_.isotypicComponent_eq_top_iff,
    isIsotypicOfType_iff_isIsotypicOfType_of_ι_smul hM S hS]

end Compatible

section Canonical

attribute [local instance] asModule isScalarTower_asModule

variable {R L M}

/-- Membership in the Lie isotypic component is membership in the corresponding canonical
`U(L)`-isotypic component. -/
@[simp]
theorem mem_isotypicComponent_iff_mem_isotypicComponent_asModule
    {S : Type*} [AddCommGroup S] [Module R S] [LieRingModule L S] [LieModule R L S]
    {m : M} :
    m ∈ isotypicComponent R L M S ↔ m ∈ _root_.isotypicComponent U M S :=
  mem_isotypicComponent_iff_mem_isotypicComponent_of_ι_smul
    (asModule_ι_smul R L M) (asModule_ι_smul R L S)

end Canonical

end LieModule
