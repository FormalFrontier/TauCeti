/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupExtension.Defs

/-!
# Basic operations on group extensions

This file provides operations on an existing group extension.

## Main definitions and results

* `GroupExtension.relabelKer`: relabels the kernel term of a group extension.

The construction is mirrored for additive groups by `to_additive`.
-/

public section

universe u v w

namespace GroupExtension

variable {N : Type u} {E : Type v} {G : Type w} [Group N] [Group E] [Group G]

/-- Relabel the kernel term of a group extension along a multiplicative equivalence. -/
@[to_additive /-- Relabel the kernel term of an additive group extension along an additive
equivalence. -/]
def relabelKer (S : GroupExtension N E G) {N' : Type*} [Group N'] (e : N' ≃* N) :
    GroupExtension N' E G where
  inl := S.inl.comp e.toMonoidHom
  rightHom := S.rightHom
  inl_injective := S.inl_injective.comp e.injective
  range_inl_eq_ker_rightHom := by
    rw [MonoidHom.range_comp, MulEquiv.toMonoidHom_eq_coe, e.range_eq_top,
      ← MonoidHom.range_eq_map, S.range_inl_eq_ker_rightHom]
  rightHom_surjective := S.rightHom_surjective

/-- The inclusion of `S.relabelKer e` is the original inclusion after `e`. -/
@[to_additive (attr := simp)
  /-- The inclusion of `S.relabelKer e` is the original inclusion after `e`. -/]
theorem relabelKer_inl (S : GroupExtension N E G) {N' : Type*} [Group N'] (e : N' ≃* N) :
    (S.relabelKer e).inl = S.inl.comp e.toMonoidHom :=
  (rfl)

/-- Relabelling the kernel does not change the projection. -/
@[to_additive (attr := simp) /-- Relabelling the kernel does not change the projection. -/]
theorem relabelKer_rightHom (S : GroupExtension N E G) {N' : Type*} [Group N'] (e : N' ≃* N) :
    (S.relabelKer e).rightHom = S.rightHom :=
  (rfl)

end GroupExtension
