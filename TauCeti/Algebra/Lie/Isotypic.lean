/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Semisimple.Defs

/-!
# Isotypic Lie modules

This file defines isotypy for Lie modules over a commutative ring. It is the Lie-module analogue
of Mathlib's module-theoretic `IsIsotypicOfType`, `IsIsotypic`, and `isotypicComponent` interface.
The definitions here do not depend on a universal enveloping algebra; the comparison with
Mathlib's module-theoretic interface lives in
`TauCeti.Algebra.Lie.UniversalEnveloping.Isotypic`.

## Main definitions

* `LieModule.IsIsotypicOfType` and `LieModule.IsIsotypic`: Lie-module isotypy.
* `LieModule.isotypicComponent`: the sum of Lie submodules equivalent to a fixed type.

## Roadmap

This is the generic Lie-isotypy interface used by Layer 6 of the Lie highest-weight roadmap and
its universal-enveloping-algebra dictionary.

## References

* `Mathlib/RingTheory/SimpleModule/Isotypic.lean` (Junyan Xu): the module-theoretic definitions
  and proof pattern ported here to Lie submodules and Lie-module equivalences.
-/

public section

universe u v w

namespace LieModule

variable (R : Type u) (L : Type v) (M : Type w)
variable [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]

/-- A Lie module `M` is isotypic of type `S` if every irreducible Lie submodule of `M` is
equivalent to `S`. -/
def IsIsotypicOfType (S : Type*) [AddCommGroup S] [Module R S]
    [LieRingModule L S] : Prop :=
  ∀ (P : LieSubmodule R L M) [IsIrreducible R L P], Nonempty (P ≃ₗ⁅R,L⁆ S)

-- This private reduction is required by Lean's module system: an exported theorem cannot unfold
-- the opaque exported definition directly while checking its public signature.
private theorem isIsotypicOfType_iff_def
    (S : Type*) [AddCommGroup S] [Module R S] [LieRingModule L S] :
    IsIsotypicOfType R L M S ↔
      ∀ (P : LieSubmodule R L M) [IsIrreducible R L P], Nonempty (P ≃ₗ⁅R,L⁆ S) :=
  Iff.rfl

/-- Lie isotypy of a fixed type means that every irreducible Lie submodule is equivalent to that
type. -/
theorem isIsotypicOfType_iff (S : Type*) [AddCommGroup S] [Module R S]
    [LieRingModule L S] :
    IsIsotypicOfType R L M S ↔
      ∀ (P : LieSubmodule R L M) [IsIrreducible R L P], Nonempty (P ≃ₗ⁅R,L⁆ S) :=
  isIsotypicOfType_iff_def R L M S

/-- A Lie module is isotypic if all its irreducible Lie submodules are equivalent. -/
def IsIsotypic : Prop :=
  ∀ (P : LieSubmodule R L M) [IsIrreducible R L P], IsIsotypicOfType R L M P

-- See `isIsotypicOfType_iff_def`: the private reduction keeps this exported characteristic
-- theorem compatible with the module system.
private theorem isIsotypic_iff_def :
    IsIsotypic R L M ↔
      ∀ (P : LieSubmodule R L M) [IsIrreducible R L P], IsIsotypicOfType R L M P :=
  Iff.rfl

/-- A Lie module is isotypic exactly when it is isotypic of the type of each irreducible Lie
submodule. -/
theorem isIsotypic_iff :
    IsIsotypic R L M ↔
      ∀ (P : LieSubmodule R L M) [IsIrreducible R L P], IsIsotypicOfType R L M P :=
  isIsotypic_iff_def R L M

variable {R L M}

/-- A fixed isotypic type makes every pair of irreducible Lie submodules equivalent. -/
theorem IsIsotypicOfType.isIsotypic {S : Type*} [AddCommGroup S] [Module R S]
    [LieRingModule L S] (h : IsIsotypicOfType R L M S) :
    IsIsotypic R L M :=
  fun P _ Q _ => ⟨(h Q).some.trans (h P).some.symm⟩

variable (R L M)

/-- The Lie isotypic component of type `S`, defined as the sum of all Lie submodules equivalent
to `S`. -/
noncomputable def isotypicComponent (S : Type*) [AddCommGroup S] [Module R S]
    [LieRingModule L S] : LieSubmodule R L M :=
  sSup {P | Nonempty (P ≃ₗ⁅R,L⁆ S)}

-- See `isIsotypicOfType_iff_def`: the private reduction exposes the defining equation without
-- asking an exported theorem to unfold an opaque exported definition.
private theorem isotypicComponent_eq_sSup_def
    (S : Type*) [AddCommGroup S] [Module R S] [LieRingModule L S] :
    isotypicComponent R L M S =
      sSup {P : LieSubmodule R L M | Nonempty (P ≃ₗ⁅R,L⁆ S)} :=
  rfl

/-- The Lie isotypic component is the sum of all Lie submodules equivalent to its type. -/
theorem isotypicComponent_def (S : Type*) [AddCommGroup S] [Module R S]
    [LieRingModule L S] :
    isotypicComponent R L M S =
      sSup {P : LieSubmodule R L M | Nonempty (P ≃ₗ⁅R,L⁆ S)} :=
  isotypicComponent_eq_sSup_def R L M S

/-- The Lie isotypic component is below `N` exactly when every submodule equivalent to its type is
below `N`. -/
@[simp]
theorem isotypicComponent_le_iff (S : Type*) [AddCommGroup S] [Module R S]
    [LieRingModule L S] (N : LieSubmodule R L M) :
    isotypicComponent R L M S ≤ N ↔
      ∀ P : LieSubmodule R L M, Nonempty (P ≃ₗ⁅R,L⁆ S) → P ≤ N := by
  rw [isotypicComponent_def, sSup_le_iff]
  simp only [Set.mem_ofPred_eq]

end LieModule

namespace LieSubmodule

variable (R : Type u) (L : Type v) (M : Type w)
variable [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]

/-- A Lie submodule equivalent to `S` is contained in the Lie isotypic component of type `S`. -/
theorem le_isotypicComponent_of_equiv (P : LieSubmodule R L M)
    (S : Type*) [AddCommGroup S] [Module R S] [LieRingModule L S]
    (h : Nonempty (P ≃ₗ⁅R,L⁆ S)) :
    P ≤ LieModule.isotypicComponent R L M S := by
  rw [LieModule.isotypicComponent_def]
  exact le_sSup h

/-- A Lie submodule is contained in its Lie isotypic component. -/
theorem le_isotypicComponent (P : LieSubmodule R L M) :
    P ≤ LieModule.isotypicComponent R L M P := by
  exact le_isotypicComponent_of_equiv R L M P P ⟨LieModuleEquiv.refl⟩

end LieSubmodule
