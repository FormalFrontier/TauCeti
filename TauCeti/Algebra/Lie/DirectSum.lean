/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.DirectSum
public import TauCeti.Algebra.Lie.Basic

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

The file also refines the two ways an external direct sum is transported to Mathlib's Lie module
structure: along a family of morphisms of the summands (`DirectSum.lieModuleMap`, refining
`DirectSum.lmap`, and `DirectSum.lieModuleEquivCongrRight`, refining
`DirectSum.congrLinearEquiv`) and along an equivalence of the index type
(`DirectSum.lieModuleEquivCongrLeft`, refining `DirectSum.lequivCongrLeft`). The bracket acts
summand by summand, so in each case the only thing to check is that Mathlib's underlying linear map
is equivariant; the `_toLinearMap` and `_toLinearEquiv` lemmas record which map that is, so that
Mathlib's API for it stays reachable.

## Main definitions

* `TauCeti.LieModule.lieModuleHomDirectSumEquiv`: **the morphism space is additive over a direct
  sum in its target**, `(S →ₗ⁅R,L⁆ ⨁ i, Pᵢ) ≃ₗ[R] Π i, (S →ₗ⁅R,L⁆ Pᵢ)`.
* `DirectSum.lieModuleMap` and `DirectSum.lieModuleEquivCongrRight`: a family of morphisms,
  respectively of equivalences, of the summands acts on the external direct sum.
* `DirectSum.lieModuleEquivCongrLeft`: **reindexing an external direct sum of Lie modules** along
  an equivalence of index types.

## Main results

* `DirectSum.lieModuleOf_apply` and `DirectSum.lieModuleComponent_apply`: the inclusion and the
  projection of an external direct sum of Lie modules are `DirectSum.of` and evaluation.

## Roadmap

This is infrastructure for the decomposition toolkit of Layer 6 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`: additivity of the morphism space
is the ingredient that `TauCeti/Algebra/Lie/Schur.lean` names as missing from its dimension form of
Schur's lemma, and with which `TauCeti/Algebra/Lie/Multiplicity.lean` reads a multiplicity off
`dim_K (S →ₗ⁅K,L⁆ M)`. The transport definitions are what regroup a decomposition of a module into
irreducibles by isomorphism type, in
`TauCeti/Algebra/Lie/Submodule/DirectSum.lean`.
-/

public section

open scoped DirectSum

universe u v w w₁ w₂ w₃ w₄

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

section Transport

variable {R : Type u} {L : Type v} {ι : Type w₂} {κ : Type w₃}
variable [CommRing R] [LieRing L]
variable {P : ι → Type w₁} [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
  [∀ i, LieRingModule L (P i)]
variable {Q : ι → Type w₄} [∀ i, AddCommGroup (Q i)] [∀ i, Module R (Q i)]
  [∀ i, LieRingModule L (Q i)]

/-- **A family of morphisms of the summands, as a morphism of the external direct sums.** Its
underlying linear map is Mathlib's `DirectSum.lmap`, so it acts componentwise; the bracket does
too, which is all that equivariance needs. -/
def lieModuleMap (f : ∀ i, P i →ₗ⁅R,L⁆ Q i) : (⨁ i, P i) →ₗ⁅R,L⁆ ⨁ i, Q i :=
  { lmap fun i ↦ (f i : P i →ₗ[R] Q i) with
    map_lie' := by
      intro x m
      ext i
      simp [lie_module_bracket_apply] }

/-- The underlying linear map of a family of morphisms of the summands is Mathlib's
`DirectSum.lmap`, which is how its API is reached. -/
@[simp]
theorem lieModuleMap_toLinearMap (f : ∀ i, P i →ₗ⁅R,L⁆ Q i) :
    (lieModuleMap f : (⨁ i, P i) →ₗ[R] ⨁ i, Q i) = lmap fun i ↦ (f i : P i →ₗ[R] Q i) :=
  (rfl)

@[simp]
theorem lieModuleMap_apply (f : ∀ i, P i →ₗ⁅R,L⁆ Q i) (x : ⨁ i, P i) (i : ι) :
    lieModuleMap f x i = f i (x i) :=
  (rfl)

/-- **A family of equivalences of the summands, as an equivalence of the external direct sums.**
Its underlying linear equivalence is Mathlib's `DirectSum.congrLinearEquiv`, whose inverse is
already the family of inverses; equivariance is that of the underlying `DirectSum.lieModuleMap`. -/
def lieModuleEquivCongrRight (e : ∀ i, P i ≃ₗ⁅R,L⁆ Q i) : (⨁ i, P i) ≃ₗ⁅R,L⁆ ⨁ i, Q i :=
  { congrLinearEquiv fun i ↦ (e i : P i ≃ₗ[R] Q i) with
    map_lie' := (lieModuleMap fun i ↦ (e i : P i →ₗ⁅R,L⁆ Q i)).map_lie' }

/-- The underlying linear equivalence of a family of equivalences of the summands is Mathlib's
`DirectSum.congrLinearEquiv`, which is how its API is reached. -/
@[simp]
theorem lieModuleEquivCongrRight_toLinearEquiv (e : ∀ i, P i ≃ₗ⁅R,L⁆ Q i) :
    (lieModuleEquivCongrRight e : (⨁ i, P i) ≃ₗ[R] ⨁ i, Q i)
      = congrLinearEquiv fun i ↦ (e i : P i ≃ₗ[R] Q i) :=
  (rfl)

@[simp]
theorem lieModuleEquivCongrRight_apply (e : ∀ i, P i ≃ₗ⁅R,L⁆ Q i) (x : ⨁ i, P i) (i : ι) :
    lieModuleEquivCongrRight e x i = e i (x i) :=
  (rfl)

/-- The inverse of a family of equivalences of the summands is the family of inverses. -/
@[simp]
theorem lieModuleEquivCongrRight_symm (e : ∀ i, P i ≃ₗ⁅R,L⁆ Q i) :
    (lieModuleEquivCongrRight e).symm = lieModuleEquivCongrRight fun i ↦ (e i).symm :=
  (rfl)

variable (R L) in
/-- **Reindexing an external direct sum of Lie modules** along an equivalence of index types. Its
underlying linear equivalence is Mathlib's `DirectSum.lequivCongrLeft`. -/
def lieModuleEquivCongrLeft (h : ι ≃ κ) : (⨁ i, P i) ≃ₗ⁅R,L⁆ ⨁ k, P (h.symm k) :=
  { lequivCongrLeft R h with
    map_lie' := by
      intro x m
      ext k
      simp [lequivCongrLeft_apply, lie_module_bracket_apply] }

variable (R L) in
/-- The underlying linear equivalence of a reindexing is Mathlib's `DirectSum.lequivCongrLeft`,
which is how its API is reached. -/
@[simp]
theorem lieModuleEquivCongrLeft_toLinearEquiv (h : ι ≃ κ) :
    (lieModuleEquivCongrLeft R L (P := P) h : (⨁ i, P i) ≃ₗ[R] ⨁ k, P (h.symm k))
      = lequivCongrLeft R h :=
  (rfl)

variable (R L) in
@[simp]
theorem lieModuleEquivCongrLeft_apply (h : ι ≃ κ) (x : ⨁ i, P i) (k : κ) :
    lieModuleEquivCongrLeft R L (P := P) h x k = x (h.symm k) :=
  lequivCongrLeft_apply R h x k

end Transport

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
