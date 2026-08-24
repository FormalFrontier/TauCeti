/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Subalgebra

public section

/-!
# Basic infrastructure for Lie modules

This file supplies general constructions for Lie modules that are missing from Mathlib.

## Main definitions

* `TauCeti.LieModuleEquiv.ofBijective`: a bijective morphism of Lie modules is an equivalence.
* `TauCeti.annihilator`: the Lie subalgebra of elements annihilating a vector in a Lie module.

## Main results

* `TauCeti.mem_annihilator`: membership in `annihilator v` is equivalent to vanishing of the Lie
  action on `v`.
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
  -- `LieModuleEquiv` has no projection lemma exposing the underlying `LinearEquiv`, so reveal that
  -- representation boundary before applying the corresponding linear-equivalence interface lemma.
  change (LinearEquiv.ofBijective (f : M →ₗ[R] N) hf) m = f m
  exact LinearEquiv.ofBijective_apply _ _

end LieModuleEquiv

section Annihilator

variable [LieAlgebra R L] [LieModule R L M]

/-- The elements of `L` annihilating a fixed vector `v` form a Lie subalgebra: the bracket is
linear in its left argument, and the Leibniz rule `lie_lie` closes the set under brackets. -/
def annihilator (v : M) : LieSubalgebra R L where
  carrier := {x : L | ⁅x, v⁆ = 0}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [add_lie, hx, hy, add_zero]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    rw [zero_lie]
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [smul_lie, hx, smul_zero]
  lie_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [lie_lie, hx, hy, lie_zero, lie_zero, sub_zero]

/-- Membership in the annihilator of a vector is exactly vanishing of the Lie action. -/
@[simp]
theorem mem_annihilator {v : M} {x : L} :
    x ∈ (annihilator v : LieSubalgebra R L) ↔ ⁅x, v⁆ = 0 :=
  Iff.rfl

end Annihilator

end TauCeti
