/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basic

public section

/-!
# Basic infrastructure for Lie modules

This file supplies general constructions for Lie modules that are missing from Mathlib.

## Main definitions

* `TauCeti.LieModuleEquiv.ofBijective`: a bijective morphism of Lie modules is an equivalence.
-/

namespace TauCeti

universe u v w w₁

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}
variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M] [LieRingModule L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N]

namespace LieModuleEquiv

/-- A bijective morphism of Lie modules is an equivalence of Lie modules. This is the Lie module
analogue of `LieEquiv.ofBijective`. -/
noncomputable def ofBijective (f : M →ₗ⁅R,L⁆ N) (hf : Function.Bijective f) : M ≃ₗ⁅R,L⁆ N :=
  { LinearEquiv.ofBijective (f : M →ₗ[R] N) hf with
    toFun := f
    map_lie' := f.map_lie _ _ }

@[simp]
theorem ofBijective_apply (f : M →ₗ⁅R,L⁆ N) (hf : Function.Bijective f) (m : M) :
    ofBijective f hf m = f m := by
  change (LinearEquiv.ofBijective (f : M →ₗ[R] N) hf) m = f m
  exact LinearEquiv.ofBijective_apply _ _

end LieModuleEquiv

end TauCeti
