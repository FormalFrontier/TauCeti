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

The transport has two small pieces. First, equivalences of Lie modules are exactly linear
equivalences for compatible `U(L)`-actions. Second, a Lie submodule, with its canonical
`U(L)`-action, is linearly equivalent by the identity map to the corresponding `U(L)`-submodule.
The Lie-level predicates and component below are then direct transports of
`IsIsotypicOfType`, `IsIsotypic`, and `isotypicComponent`.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.lieModuleEquivEquiv`: the equivalence dictionary for
  compatible `U(L)`-actions.
* `TauCeti.UniversalEnvelopingAlgebra.lieSubmoduleLinearEquivAsModule`: the identity equivalence
  between a Lie submodule and its image under the canonical submodule dictionary.
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

universe u v w x

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R : Type u) (L : Type v) (M : Type w) (N : Type x)
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

section Equiv

variable [LieRingModule L M] [LieModule R L M]
variable [LieRingModule L N] [LieModule R L N]
variable [Module (_root_.UniversalEnvelopingAlgebra R L) M]
variable [IsScalarTower R (_root_.UniversalEnvelopingAlgebra R L) M]
variable [Module (_root_.UniversalEnvelopingAlgebra R L) N]
variable [IsScalarTower R (_root_.UniversalEnvelopingAlgebra R L) N]

/-- **The enveloping-algebra dictionary for equivalences**: Lie module equivalences are exactly
`U(L)`-linear equivalences when both actions are compatible with the canonical Lie generators.
The correspondence is the identity on underlying functions. -/
noncomputable def lieModuleEquivEquiv
    (hM : ∀ (x : L) (m : M), ι R x • m = ⁅x, m⁆)
    (hN : ∀ (x : L) (n : N), ι R x • n = ⁅x, n⁆) :
    (M ≃ₗ⁅R,L⁆ N) ≃ (M ≃ₗ[U] N) where
  toFun e :=
    { lieModuleHomEquiv hM hN e.toLieModuleHom with
      invFun := e.invFun
      left_inv := fun m => by
        change e.invFun ((lieModuleHomEquiv hM hN e.toLieModuleHom) m) = m
        rw [show (lieModuleHomEquiv hM hN e.toLieModuleHom) m = e m by
          exact congrFun (coe_lieModuleHomEquiv hM hN e.toLieModuleHom) m]
        exact e.left_inv m
      right_inv := fun n => by
        change (lieModuleHomEquiv hM hN e.toLieModuleHom) (e.invFun n) = n
        rw [show (lieModuleHomEquiv hM hN e.toLieModuleHom) (e.invFun n) = e (e.invFun n) by
          exact congrFun (coe_lieModuleHomEquiv hM hN e.toLieModuleHom) (e.invFun n)]
        exact e.right_inv n }
  invFun e :=
    { (lieModuleHomEquiv hM hN).symm e.toLinearMap with
      invFun := e.invFun
      left_inv := fun m => by
        change e.invFun (((lieModuleHomEquiv hM hN).symm e.toLinearMap) m) = m
        rw [show ((lieModuleHomEquiv hM hN).symm e.toLinearMap) m = e m by
          exact congrFun (coe_lieModuleHomEquiv_symm hM hN e.toLinearMap) m]
        exact e.left_inv m
      right_inv := fun n => by
        change ((lieModuleHomEquiv hM hN).symm e.toLinearMap) (e.invFun n) = n
        rw [show ((lieModuleHomEquiv hM hN).symm e.toLinearMap) (e.invFun n) = e (e.invFun n) by
          exact congrFun (coe_lieModuleHomEquiv_symm hM hN e.toLinearMap) (e.invFun n)]
        exact e.right_inv n }
  left_inv e := by
    apply LieModuleEquiv.ext
    intro m
    change ((lieModuleHomEquiv hM hN).symm
      (lieModuleHomEquiv hM hN e.toLieModuleHom)) m = e m
    rw [(lieModuleHomEquiv hM hN).symm_apply_apply]
    rfl
  right_inv e := by
    apply LinearEquiv.ext
    intro m
    change (lieModuleHomEquiv hM hN
      ((lieModuleHomEquiv hM hN).symm e.toLinearMap)) m = e m
    rw [(lieModuleHomEquiv hM hN).apply_symm_apply]
    rfl

omit [LieModule R L M] in
/-- The forward equivalence dictionary does not change the underlying function. -/
@[simp]
theorem coe_lieModuleEquivEquiv
    (hM : ∀ (x : L) (m : M), ι R x • m = ⁅x, m⁆)
    (hN : ∀ (x : L) (n : N), ι R x • n = ⁅x, n⁆)
    (e : M ≃ₗ⁅R,L⁆ N) :
    ⇑(lieModuleEquivEquiv R L M N hM hN e) = ⇑e :=
  coe_lieModuleHomEquiv hM hN e.toLieModuleHom

omit [LieModule R L M] in
/-- The inverse equivalence dictionary does not change the underlying function. -/
@[simp]
theorem coe_lieModuleEquivEquiv_symm
    (hM : ∀ (x : L) (m : M), ι R x • m = ⁅x, m⁆)
    (hN : ∀ (x : L) (n : N), ι R x • n = ⁅x, n⁆)
    (e : M ≃ₗ[U] N) :
    ⇑((lieModuleEquivEquiv R L M N hM hN).symm e) = ⇑e :=
  coe_lieModuleHomEquiv_symm hM hN e.toLinearMap

end Equiv

section Submodule

variable [LieRingModule L M] [LieModule R L M]

attribute [local instance] asModule isScalarTower_asModule

/-- The canonical `U(L)`-action on a Lie submodule agrees, after inclusion, with the canonical
action on the ambient Lie module. -/
theorem coe_asModule_smul_lieSubmodule (P : LieSubmodule R L M) (u : U) (p : P) :
    ((u • p : P) : M) = u • (p : M) := by
  revert p
  induction u using induction_ι with
  | ι x =>
    intro p
    rw [asModule_ι_smul R L P, asModule_ι_smul R L M]
    rfl
  | algebraMap r => intro p; simp only [algebraMap_smul, SetLike.val_smul]
  | add u v hu hv =>
    intro p
    rw [add_smul, add_smul]
    change ((u • p : P) : M) + ((v • p : P) : M) = u • (p : M) + v • (p : M)
    rw [hu p, hv p]
  | mul u v hu hv =>
    intro p
    rw [mul_smul, mul_smul, hu (v • p), hv p]

/-- A Lie submodule with its canonical `U(L)`-action is linearly equivalent, by the identity map,
to its image under `lieSubmoduleOrderIsoAsModule`. This is the subtype-level part of the
submodule dictionary used when transporting isotypy. -/
noncomputable def lieSubmoduleLinearEquivAsModule (P : LieSubmodule R L M) :
    P ≃ₗ[U] lieSubmoduleOrderIsoAsModule R L M P where
  toFun p := ⟨p, (mem_lieSubmoduleOrderIsoAsModule R L M).mpr p.property⟩
  invFun p := ⟨p, (mem_lieSubmoduleOrderIsoAsModule R L M).mp p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' u p := by
    ext
    exact coe_asModule_smul_lieSubmodule R L M P u p

@[simp]
theorem coe_lieSubmoduleLinearEquivAsModule (P : LieSubmodule R L M) :
    ⇑(lieSubmoduleLinearEquivAsModule R L M P) =
      fun p => ⟨p, (mem_lieSubmoduleOrderIsoAsModule R L M).mpr p.property⟩ :=
  (rfl)

@[simp]
theorem coe_lieSubmoduleLinearEquivAsModule_symm (P : LieSubmodule R L M) :
    ⇑(lieSubmoduleLinearEquivAsModule R L M P).symm =
      fun p => ⟨p, (mem_lieSubmoduleOrderIsoAsModule R L M).mp p.property⟩ :=
  (rfl)

end Submodule

end TauCeti.UniversalEnvelopingAlgebra

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
    [LieRingModule L S] [LieModule R L S] : Prop :=
  ∀ (P : LieSubmodule R L M) [IsIrreducible R L P], Nonempty (P ≃ₗ⁅R,L⁆ S)

/-- A Lie module is isotypic if all its irreducible Lie submodules are equivalent. -/
def IsIsotypic : Prop :=
  ∀ (P : LieSubmodule R L M) [IsIrreducible R L P], IsIsotypicOfType R L M P

variable {R L M}

/-- A fixed isotypic type makes every pair of irreducible Lie submodules equivalent. -/
theorem IsIsotypicOfType.isIsotypic {S : Type*} [AddCommGroup S] [Module R S]
    [LieRingModule L S] [LieModule R L S] (h : IsIsotypicOfType R L M S) :
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
      (lieModuleEquivEquiv R L P S (asModule_ι_smul R L P) (asModule_ι_smul R L S) e)
  · intro h P hP
    let Q := lieSubmoduleOrderIsoAsModule R L M P
    letI : IsSimpleModule U P :=
      (isIrreducible_iff_isSimpleModule (asModule_ι_smul R L P)).mp hP
    letI : IsSimpleModule U Q :=
      IsSimpleModule.congr (lieSubmoduleLinearEquivAsModule R L M P).symm
    exact (h Q).map fun e =>
      (lieModuleEquivEquiv R L P S (asModule_ι_smul R L P) (asModule_ι_smul R L S)).symm
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
  rw [isIsotypicOfType_iff_isIsotypicOfType_asModule]
  constructor
  · intro h
    apply _root_.isotypicComponent_eq_top_iff.mp
    rw [← lieSubmoduleOrderIsoAsModule_isotypicComponent S]
    simpa using congrArg (lieSubmoduleOrderIsoAsModule R L M) h
  · intro h
    apply (lieSubmoduleOrderIsoAsModule R L M).injective
    rw [lieSubmoduleOrderIsoAsModule_isotypicComponent S]
    simpa using _root_.isotypicComponent_eq_top_iff.mpr h

end LieModule
