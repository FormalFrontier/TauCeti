/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Basic

/-!
# Group extensions from surjective homomorphisms

A surjective homomorphism determines an extension by its kernel. An equivalence with that kernel
can be used to choose a different group as the extension's left term.

## Main definitions and results

* `GroupExtension.ofSurjective`: the canonical extension by the kernel of a surjective
  homomorphism.
* `GroupExtension.ofMulEquivKer`: `ofSurjective` with its kernel relabelled by `relabelKer`.
* `GroupExtension.ofMulEquivKer_inl`: its inclusion is the given kernel equivalence followed by
  the kernel subtype.
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
theorem ofSurjective_inl {f : E →* G} (hf : Function.Surjective f) :
    (ofSurjective hf).inl = f.ker.subtype :=
  (rfl)

/-- The projection in `GroupExtension.ofSurjective hf` is the original homomorphism. -/
@[to_additive (attr := simp)
  /-- The projection in `AddGroupExtension.ofSurjective hf` is the original homomorphism. -/]
theorem ofSurjective_rightHom {f : E →* G} (hf : Function.Surjective f) :
    (ofSurjective hf).rightHom = f :=
  (rfl)

/-- A surjective homomorphism `f : E →* G`, together with an equivalence `N ≃* f.ker`,
determines a group extension of `G` by `N`. -/
@[to_additive
  /-- A surjective homomorphism `f : E →+ G`, together with an equivalence `N ≃+ f.ker`,
  determines an additive group extension of `G` by `N`. -/]
def ofMulEquivKer {f : E →* G} (hf : Function.Surjective f)
    (e : N ≃* f.ker) :
    GroupExtension N E G :=
  (ofSurjective hf).relabelKer e

/-- The inclusion of `GroupExtension.ofMulEquivKer hf e` is the given kernel equivalence followed
by the kernel subtype. -/
@[to_additive (attr := simp)
  /-- The inclusion of `AddGroupExtension.ofAddEquivKer hf e` is the given kernel equivalence
  followed by the kernel subtype. -/]
theorem ofMulEquivKer_inl {f : E →* G} (hf : Function.Surjective f) (e : N ≃* f.ker) :
    (ofMulEquivKer hf e).inl = f.ker.subtype.comp e.toMonoidHom :=
  by rw [ofMulEquivKer, relabelKer_inl, ofSurjective_inl]

/-- The projection of `GroupExtension.ofMulEquivKer hf e` is the original homomorphism. -/
@[to_additive (attr := simp)
  /-- The projection of `AddGroupExtension.ofAddEquivKer hf e` is the original homomorphism. -/]
theorem ofMulEquivKer_rightHom {f : E →* G} (hf : Function.Surjective f) (e : N ≃* f.ker) :
    (ofMulEquivKer hf e).rightHom = f :=
  by rw [ofMulEquivKer, relabelKer_rightHom, ofSurjective_rightHom]

end GroupExtension
