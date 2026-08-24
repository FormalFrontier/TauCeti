/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Module

/-!
# Isotypic Lie modules through the universal enveloping algebra

This file transports Mathlib's isotypic-module interface across the universal-enveloping-algebra
dictionary. The core definitions require only a commutative base ring. Semisimplicity enters only
in the characterization of an isotypic module by its unique component.

The generic equivalence and submodule interfaces live with the rest of the enveloping-algebra
dictionary in `TauCeti.Algebra.Lie.UniversalEnveloping.Module`. The Lie-level predicates and
component below are direct transports of `IsIsotypicOfType`, `IsIsotypic`, and
`isotypicComponent` through those interfaces.

## Main definitions

* `LieModule.IsIsotypicOfType` and `LieModule.IsIsotypic`: Lie-module isotypy.
* `LieModule.isotypicComponent`: the Lie submodule underlying Mathlib's `U(L)`-isotypic
  component.

## Roadmap

This is the universal-enveloping-algebra bridge for Layer 6 of the Lie highest-weight roadmap.
It deliberately stops before highest-weight classification: consumers such as Kostant-form
modules can state that all irreducible Lie submodules are equivalent without rebuilding ring-level
isotypic machinery.
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

attribute [local instance] asModule isScalarTower_asModule

/-- A Lie module `M` is isotypic of type `S` if every irreducible Lie submodule of `M` is
equivalent to `S`. -/
def IsIsotypicOfType (S : Type*) [AddCommGroup S] [Module R S]
    [LieRingModule L S] : Prop :=
  ∀ (P : LieSubmodule R L M) [IsIrreducible R L P], Nonempty (P ≃ₗ⁅R,L⁆ S)

/-- A Lie module is isotypic if all its irreducible Lie submodules are equivalent. -/
def IsIsotypic : Prop :=
  ∀ (P : LieSubmodule R L M) [IsIrreducible R L P], IsIsotypicOfType R L M P

variable {R L M}

omit [LieAlgebra R L] [LieModule R L M] in
/-- A fixed isotypic type makes every pair of irreducible Lie submodules equivalent. -/
theorem IsIsotypicOfType.isIsotypic {S : Type*} [AddCommGroup S] [Module R S]
    [LieRingModule L S] (h : IsIsotypicOfType R L M S) :
    IsIsotypic R L M :=
  fun P _ Q _ => ⟨(h Q).some.trans (h P).some.symm⟩

set_option linter.style.haveILetI false in
/-- Lie-module isotypy of a fixed type is exactly Mathlib's module isotypy for the canonical
`U(L)`-actions. -/
theorem isIsotypicOfType_iff_isIsotypicOfType_asModule
    (S : Type*) [AddCommGroup S] [Module R S] [LieRingModule L S] [LieModule R L S] :
    IsIsotypicOfType R L M S ↔ _root_.IsIsotypicOfType U M S := by
  constructor
  · intro h Q hQ
    let P := (lieSubmoduleOrderIsoAsModule R L M).symm Q
    rw [← (lieSubmoduleOrderIsoAsModule R L M).apply_symm_apply Q] at hQ ⊢
    letI : IsSimpleModule U P :=
      IsSimpleModule.congr (lieSubmoduleLinearEquivAsModule R L M P)
    letI : IsIrreducible R L P :=
      (isIrreducible_iff_isSimpleModule (asModule_ι_smul R L P)).mpr inferInstance
    exact (h P).map fun e => (lieSubmoduleLinearEquivAsModule R L M P).symm.trans
      (lieModuleEquivEquiv (R := R) (L := L) (M := P) (N := S)
        (asModule_ι_smul R L P) (asModule_ι_smul R L S) e)
  · intro h P hP
    let Q := lieSubmoduleOrderIsoAsModule R L M P
    letI : IsSimpleModule U P :=
      (isIrreducible_iff_isSimpleModule (asModule_ι_smul R L P)).mp hP
    letI : IsSimpleModule U Q :=
      IsSimpleModule.congr (lieSubmoduleLinearEquivAsModule R L M P).symm
    exact (h Q).map fun e =>
      (lieModuleEquivEquiv (R := R) (L := L) (M := P) (N := S)
        (asModule_ι_smul R L P) (asModule_ι_smul R L S)).symm
        ((lieSubmoduleLinearEquivAsModule R L M P).trans e)

set_option linter.style.haveILetI false in
/-- Lie-module isotypy is exactly Mathlib's module isotypy for the canonical `U(L)`-action. -/
theorem isIsotypic_iff_isIsotypic_asModule :
    IsIsotypic R L M ↔ _root_.IsIsotypic U M := by
  simp only [IsIsotypic, _root_.IsIsotypic]
  constructor
  · intro h Q hQ
    let P := (lieSubmoduleOrderIsoAsModule R L M).symm Q
    rw [← (lieSubmoduleOrderIsoAsModule R L M).apply_symm_apply Q] at hQ ⊢
    letI : IsSimpleModule U P :=
      IsSimpleModule.congr (lieSubmoduleLinearEquivAsModule R L M P)
    letI : IsIrreducible R L P :=
      (isIrreducible_iff_isSimpleModule (asModule_ι_smul R L P)).mpr inferInstance
    exact (isIsotypicOfType_iff_isIsotypicOfType_asModule P |>.mp (h P)).of_linearEquiv_type
      (lieSubmoduleLinearEquivAsModule R L M P)
  · intro h P hP
    let Q := lieSubmoduleOrderIsoAsModule R L M P
    letI : IsSimpleModule U P :=
      (isIrreducible_iff_isSimpleModule (asModule_ι_smul R L P)).mp hP
    letI : IsSimpleModule U Q :=
      IsSimpleModule.congr (lieSubmoduleLinearEquivAsModule R L M P).symm
    exact isIsotypicOfType_iff_isIsotypicOfType_asModule P |>.mpr
      ((h Q).of_linearEquiv_type (lieSubmoduleLinearEquivAsModule R L M P).symm)

variable (R L M)

/-- The Lie isotypic component of type `S`, obtained by transporting Mathlib's `U(L)`-isotypic
component through the submodule dictionary. -/
noncomputable def isotypicComponent (S : Type*) [AddCommGroup S] [Module R S]
    [LieRingModule L S] [LieModule R L S] : LieSubmodule R L M :=
  (lieSubmoduleOrderIsoAsModule R L M).symm (_root_.isotypicComponent U M S)

variable {R L M}

/-- The Lie isotypic component maps to Mathlib's `U(L)`-isotypic component. -/
@[simp]
theorem lieSubmoduleOrderIsoAsModule_isotypicComponent
    (S : Type*) [AddCommGroup S] [Module R S] [LieRingModule L S] [LieModule R L S] :
    lieSubmoduleOrderIsoAsModule R L M (isotypicComponent R L M S) =
      _root_.isotypicComponent U M S :=
  (lieSubmoduleOrderIsoAsModule R L M).apply_symm_apply _

/-- Membership in the Lie isotypic component is membership in the corresponding `U(L)`-isotypic
component. -/
@[simp]
theorem mem_isotypicComponent_iff
    {S : Type*} [AddCommGroup S] [Module R S] [LieRingModule L S] [LieModule R L S]
    {m : M} :
    m ∈ isotypicComponent R L M S ↔ m ∈ _root_.isotypicComponent U M S := by
  rw [isotypicComponent, mem_lieSubmoduleOrderIsoAsModule_symm]

set_option linter.style.haveILetI false in
/-- In a completely reducible Lie module, the isotypic component of type `S` is the whole module
exactly when the Lie module is isotypic of type `S`. -/
theorem isotypicComponent_eq_top_iff
    (S : Type*) [AddCommGroup S] [Module R S] [LieRingModule L S] [LieModule R L S]
    [IsIrreducible R L S]
    [ComplementedLattice (LieSubmodule R L M)] :
    isotypicComponent R L M S = ⊤ ↔ IsIsotypicOfType R L M S := by
  letI : IsSimpleModule U S :=
    (isIrreducible_iff_isSimpleModule (asModule_ι_smul R L S)).mp inferInstance
  letI : IsSemisimpleModule U M :=
    (complementedLattice_lieSubmodule_iff_isSemisimpleModule
      (asModule_ι_smul R L M)).mp inferInstance
  rw [← map_eq_top_iff (lieSubmoduleOrderIsoAsModule R L M),
    lieSubmoduleOrderIsoAsModule_isotypicComponent,
    _root_.isotypicComponent_eq_top_iff,
    isIsotypicOfType_iff_isIsotypicOfType_asModule]

end LieModule
