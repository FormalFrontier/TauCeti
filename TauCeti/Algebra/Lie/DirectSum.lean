/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.DirectSum
public import TauCeti.Algebra.Lie.Basic

public section

/-!
# External direct sums of Lie modules

This file supplements `Mathlib/Algebra/Lie/DirectSum.lean`, which puts a Lie module structure on an
external direct sum `⨁ i, Pᵢ` and provides the inclusion `DirectSum.lieModuleOf` and the projection
`DirectSum.lieModuleComponent` as morphisms of Lie modules. Those two come with no application
lemmas; the ones saying they are the underlying `DirectSum.of` and evaluation are recorded here, so
that no consumer has to unfold either definition.

They are what makes the **morphism space additive over a direct sum in its target**: a morphism
from a Lie module `S` into a finite external direct sum is the family of its components, and a
finite family of components reassembles to the element it came from. That is
`TauCeti.LieModule.lieModuleHomDirectSumEquiv`.

## Main definitions

* `TauCeti.LieModule.lieModuleHomDirectSumEquiv`: **the morphism space is additive over a direct
  sum in its target**, `(S →ₗ⁅R,L⁆ ⨁ i, Pᵢ) ≃ₗ[R] Π i, (S →ₗ⁅R,L⁆ Pᵢ)`.

## Main results

* `DirectSum.lieModuleOf_apply` and `DirectSum.lieModuleComponent_apply`: the inclusion and the
  projection of an external direct sum of Lie modules are `DirectSum.of` and evaluation.

## Roadmap

This is infrastructure for the decomposition toolkit of Layer 6 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`: additivity of the morphism space
is the ingredient that `TauCeti/Algebra/Lie/Schur.lean` names as missing from its dimension form of
Schur's lemma, and with which `TauCeti/Algebra/Lie/Multiplicity.lean` reads a multiplicity off
`dim_K (S →ₗ⁅K,L⁆ M)`.
-/

open scoped DirectSum

universe u v w w₁ w₂

namespace DirectSum

section LieModules

variable (R : Type u) (ι : Type w₂) (L : Type v) (P : ι → Type w₁)
variable [CommRing R] [LieRing L]
variable [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
variable [∀ i, LieRingModule L (P i)]

/-- The inclusion of a summand into an external direct sum of Lie modules is `DirectSum.of`. -/
@[simp]
theorem lieModuleOf_apply [DecidableEq ι] (i : ι) (x : P i) :
    lieModuleOf R ι L P i x = of P i x :=
  (rfl)

/-- The projection of an external direct sum of Lie modules onto a summand is evaluation. -/
@[simp]
theorem lieModuleComponent_apply (i : ι) (x : ⨁ i, P i) :
    lieModuleComponent R ι L P i x = x i :=
  (rfl)

end LieModules

end DirectSum

namespace TauCeti.LieModule

section Additivity

variable {R : Type u} {L : Type v} {ι : Type w₂} [DecidableEq ι] [Fintype ι]
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable (R L)
variable (S : Type w) [AddCommGroup S] [Module R S] [LieRingModule L S] [_root_.LieModule R L S]
variable (P : ι → Type w₁) [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
  [∀ i, LieRingModule L (P i)] [∀ i, _root_.LieModule R L (P i)]

/-- **The morphism space is additive over a direct sum in its target.** A morphism from `S` into a
finite external direct sum of Lie modules is the family of its components, and conversely a family
of morphisms assembles to one; this is an isomorphism of `R`-modules. -/
def lieModuleHomDirectSumEquiv :
    (S →ₗ⁅R,L⁆ ⨁ i, P i) ≃ₗ[R] Π i, (S →ₗ⁅R,L⁆ P i) where
  toFun f i := (DirectSum.lieModuleComponent R ι L P i).comp f
  map_add' _ _ := by ext i s; simp
  map_smul' _ _ := by ext i s; simp
  invFun g := ∑ i, (DirectSum.lieModuleOf R ι L P i).comp (g i)
  left_inv f := by
    refine LieModuleHom.ext fun s ↦ ?_
    rw [LieModuleHom.sum_apply]
    simp only [_root_.LieModuleHom.comp_apply, DirectSum.lieModuleOf_apply,
      DirectSum.lieModuleComponent_apply]
    exact _root_.DirectSum.sum_univ_of (f s)
  right_inv g := by
    refine funext fun j ↦ LieModuleHom.ext fun s ↦ ?_
    rw [_root_.LieModuleHom.comp_apply, LieModuleHom.sum_apply]
    simp only [_root_.LieModuleHom.comp_apply, DirectSum.lieModuleOf_apply,
      DirectSum.lieModuleComponent_apply]
    rw [DFinsupp.finsetSum_apply, Finset.sum_eq_single j]
    · simp
    · exact fun b _ hb ↦ _root_.DirectSum.of_eq_of_ne _ _ _ (Ne.symm hb)
    · simp

omit [_root_.LieModule R L S] in
@[simp]
theorem lieModuleHomDirectSumEquiv_apply (f : S →ₗ⁅R,L⁆ ⨁ i, P i) (i : ι) (s : S) :
    lieModuleHomDirectSumEquiv R L S P f i s = f s i :=
  (rfl)

omit [_root_.LieModule R L S] in
@[simp]
theorem lieModuleHomDirectSumEquiv_symm_apply (g : Π i, (S →ₗ⁅R,L⁆ P i)) (s : S) :
    (lieModuleHomDirectSumEquiv R L S P).symm g s
      = ∑ i, _root_.DirectSum.of P i (g i s) := by
  simp [lieModuleHomDirectSumEquiv, LieModuleHom.sum_apply]

end Additivity

end TauCeti.LieModule
