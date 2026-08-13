/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.GroupExtension.Defs

/-!
# Group extensions from surjective homomorphisms

A surjective homomorphism determines an extension by its kernel. An equivalence with that kernel
can be used to choose a different group as the extension's left term.

## Main definitions and results

* `GroupExtension.ofSurjective`: the canonical extension by the kernel of a surjective
  homomorphism.
* `GroupExtension.relabelKernel`: relabels the kernel term of a group extension.
* `GroupExtension.ofMulEquivKer`: `ofSurjective` with its kernel relabelled.
* `GroupExtension.ofMulEquivKer_inl_apply`: its inclusion is the given kernel equivalence.
* `GroupExtension.ofMulEquivKer_rightHom`: its projection is the original homomorphism.

The constructions are mirrored for additive groups by `to_additive`.
-/

public section

universe u v w

namespace GroupExtension

variable {N : Type u} {E : Type v} {G : Type w} [Group N] [Group E] [Group G]

/-- A surjective homomorphism `f : E →* G` determines an extension of `G` by `f.ker`. -/
@[to_additive
  /-- A surjective homomorphism `f : E →+ G` determines an extension of `G` by `f.ker`. -/]
def ofSurjective {f : E →* G} (hf : Function.Surjective f) :
    GroupExtension f.ker E G where
  inl := f.ker.subtype
  rightHom := f
  inl_injective := f.ker.subtype_injective
  range_inl_eq_ker_rightHom := Subgroup.range_subtype _
  rightHom_surjective := hf

/-- The inclusion in `GroupExtension.ofSurjective hf` is the kernel subtype. -/
@[to_additive (attr := simp)
  /-- The inclusion in `AddGroupExtension.ofSurjective hf` is the kernel subtype. -/]
theorem ofSurjective_inl_apply {f : E →* G} (hf : Function.Surjective f) (x : f.ker) :
    (ofSurjective hf).inl x = x :=
  (rfl)

/-- The projection in `GroupExtension.ofSurjective hf` is the original homomorphism. -/
@[to_additive (attr := simp)
  /-- The projection in `AddGroupExtension.ofSurjective hf` is the original homomorphism. -/]
theorem ofSurjective_rightHom {f : E →* G} (hf : Function.Surjective f) :
    (ofSurjective hf).rightHom = f :=
  (rfl)

/-- Relabel the kernel term of a group extension along a multiplicative equivalence. -/
@[to_additive /-- Relabel the kernel term of an additive group extension along an additive
equivalence. -/]
def relabelKernel (S : GroupExtension N E G) {N' : Type*} [Group N'] (e : N' ≃* N) :
    GroupExtension N' E G where
  inl := S.inl.comp e.toMonoidHom
  rightHom := S.rightHom
  inl_injective := S.inl_injective.comp e.injective
  range_inl_eq_ker_rightHom := by
    rw [MonoidHom.range_comp]
    -- Expose the coerced multiplicative equivalence as a monoid homomorphism so range lemmas apply.
    change Subgroup.map S.inl (e : N' →* N).range = S.rightHom.ker
    rw [e.range_eq_top, ← MonoidHom.range_eq_map, S.range_inl_eq_ker_rightHom]
  rightHom_surjective := S.rightHom_surjective

/-- The inclusion of `S.relabelKernel e` is the original inclusion after `e`. -/
@[to_additive (attr := simp)
  /-- The inclusion of `S.relabelKernel e` is the original inclusion after `e`. -/]
theorem relabelKernel_inl_apply (S : GroupExtension N E G) {N' : Type*} [Group N'] (e : N' ≃* N)
    (n : N') : (S.relabelKernel e).inl n = S.inl (e n) :=
  (rfl)

/-- Relabelling the kernel does not change the projection. -/
@[to_additive (attr := simp) /-- Relabelling the kernel does not change the projection. -/]
theorem relabelKernel_rightHom (S : GroupExtension N E G) {N' : Type*} [Group N'] (e : N' ≃* N) :
    (S.relabelKernel e).rightHom = S.rightHom :=
  (rfl)

/-- A surjective homomorphism `f : E →* G`, together with an equivalence `N ≃* f.ker`,
determines a group extension of `G` by `N`. -/
@[to_additive
  /-- A surjective homomorphism `f : E →+ G`, together with an equivalence `N ≃+ f.ker`,
  determines an additive group extension of `G` by `N`. -/]
def ofMulEquivKer {f : E →* G} (hf : Function.Surjective f)
    (e : N ≃* f.ker) :
    GroupExtension N E G :=
  (ofSurjective hf).relabelKernel e

/-- The inclusion of `GroupExtension.ofMulEquivKer hf e` is the given kernel equivalence. -/
@[to_additive (attr := simp)
  /-- The inclusion of `AddGroupExtension.ofAddEquivKer hf e` is the given kernel equivalence. -/]
theorem ofMulEquivKer_inl_apply {f : E →* G} (hf : Function.Surjective f) (e : N ≃* f.ker)
    (n : N) : (ofMulEquivKer hf e).inl n = (e n : E) :=
  (rfl)

/-- The projection of `GroupExtension.ofMulEquivKer hf e` is the original homomorphism. -/
@[to_additive (attr := simp)
  /-- The projection of `AddGroupExtension.ofAddEquivKer hf e` is the original homomorphism. -/]
theorem ofMulEquivKer_rightHom {f : E →* G} (hf : Function.Surjective f) (e : N ≃* f.ker) :
    (ofMulEquivKer hf e).rightHom = f :=
  (rfl)

end GroupExtension
