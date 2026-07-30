/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Rep.Res

/-!
# Restriction of a finite-dimensional representation to a subgroup

For a subgroup `S` of a group `G` this file restricts a finite-dimensional representation of `G`
to `S`.  This is Mathlib's `Rep.res` transported to `FDRep`, and it depends on nothing beyond
`FDRep` itself: it is kept separate from the induction and Frobenius-reciprocity files so that a
consumer of restriction alone need not import them.

Restriction is packaged both objectwise, as `resFDRep`, and functorially, as `resFDRepFunctor`,
the latter naturally isomorphic to `Rep.resFunctor` under the forgetful functor to `Rep k S`.
This mirrors the `indFDRep` / `indFDRepFunctor` pair of
`TauCeti.RepresentationTheory.Induction.FiniteDimensional`.

## Main definitions

* `TauCeti.resFDRep`: restriction of a finite-dimensional representation to a subgroup.
* `TauCeti.resFDRepMap`: restriction of an intertwiner.
* `TauCeti.resFDRepFunctor`: the two packaged as a functor `FDRep k G ⥤ FDRep k S`.
* `TauCeti.resFDRepForgetIso`, `TauCeti.resFDRepForgetNatIso`: the identification of `resFDRep`
  with Mathlib's `Rep.res` after forgetting finite-dimensionality, objectwise and naturally.

## Implementation notes

Everything except the character formula lives over a commutative ring, matching Mathlib's
`Rep.resFunctor`; `Field k` enters only with `FDRep.character`.

The bodies of `resFDRep` and `resFDRepMap` are not exposed; their characteristic properties are
`character_resFDRep`, `forget₂_obj_resFDRep` and `forget₂_map_resFDRepMap`.  The second is an
*equality* of objects of `Rep k S` with `Rep.res`, not merely an isomorphism, so it carries the
description of the restricted representation and lets Mathlib's `Rep.res` API transfer.  Since a
sealed body cannot be unfolded while elaborating the *type* of a later declaration,
`resFDRepForgetIso` records the same identification as an isomorphism, which the morphism-level
lemmas and downstream files use in place of the definitional equality; this mirrors
`TauCeti.indFDRepForgetIso`.

## References

This is restriction infrastructure for Layer 2 of
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

variable {k G : Type u} [Group G]

section Representation

variable [CommRing k]

/-- Restriction of a finite-dimensional representation of `G` to a subgroup `S`.  This is Mathlib's
`Action.res` along `S.subtype`, under the definitional identification
`FDRep k G = Action (FGModuleCat k) G`; this definition only supplies the representation-theoretic
name. -/
def resFDRep (S : Subgroup G) (B : FDRep k G) : FDRep k S :=
  (Action.res (FGModuleCat k) S.subtype).obj B

/-- Restriction commutes with forgetting finite-dimensionality. -/
@[simp]
theorem forget₂_obj_resFDRep (S : Subgroup G) (B : FDRep k G) :
    (forget₂ (FDRep k S) (Rep k S)).obj (resFDRep S B) =
      Rep.res S.subtype ((forget₂ (FDRep k G) (Rep k G)).obj B) :=
  (rfl)

/-- `forget₂_obj_resFDRep` as an isomorphism, for use in the types of later declarations, where the
sealed body of `resFDRep` is not available to unfold. -/
noncomputable def resFDRepForgetIso (S : Subgroup G) (B : FDRep k G) :
    (forget₂ (FDRep k S) (Rep k S)).obj (resFDRep S B) ≅
      Rep.res S.subtype ((forget₂ (FDRep k G) (Rep k G)).obj B) :=
  Iso.refl _

/-- Restriction of an intertwiner of finite-dimensional representations: Mathlib's `Rep.resFunctor`
on the underlying intertwiner, conjugated by `resFDRepForgetIso` and transported back along the
fully faithful forgetful functor `FDRep k S ⥤ Rep k S`.  Its characterizing property is
`forget₂_map_resFDRepMap`; the definition itself is not exposed. -/
noncomputable def resFDRepMap (S : Subgroup G) {B B' : FDRep k G} (f : B ⟶ B') :
    resFDRep S B ⟶ resFDRep S B' :=
  (forget₂ (FDRep k S) (Rep k S)).preimage
    ((resFDRepForgetIso S B).hom ≫
      (Rep.resFunctor S.subtype).map ((forget₂ (FDRep k G) (Rep k G)).map f) ≫
        (resFDRepForgetIso S B').inv)

/-- Forgetting finite-dimensionality from `resFDRepMap` gives Mathlib's restricted intertwiner,
conjugated by `resFDRepForgetIso`.  This is the only fact about `resFDRepMap` used below. -/
@[simp]
theorem forget₂_map_resFDRepMap (S : Subgroup G) {B B' : FDRep k G} (f : B ⟶ B') :
    (forget₂ (FDRep k S) (Rep k S)).map (resFDRepMap S f) =
      (resFDRepForgetIso S B).hom ≫
        (Rep.resFunctor S.subtype).map ((forget₂ (FDRep k G) (Rep k G)).map f) ≫
          (resFDRepForgetIso S B').inv := by
  rw [resFDRepMap]
  exact (forget₂ (FDRep k S) (Rep k S)).map_preimage _

/-- Restriction of intertwiners preserves identities. -/
theorem resFDRepMap_id (S : Subgroup G) (B : FDRep k G) :
    resFDRepMap S (𝟙 B) = 𝟙 (resFDRep S B) :=
  -- The law holds after applying the forgetful functor: the conjugating copies of
  -- `resFDRepForgetIso` cancel, so the proof does not unfold `resFDRep`.
  (forget₂ (FDRep k S) (Rep k S)).map_injective (by
    simp only [forget₂_map_resFDRepMap, CategoryTheory.Functor.map_id]
    rfl)

/-- Restriction of intertwiners preserves composition. -/
theorem resFDRepMap_comp (S : Subgroup G) {B B' B'' : FDRep k G} (f : B ⟶ B') (g : B' ⟶ B'') :
    resFDRepMap S (f ≫ g) = resFDRepMap S f ≫ resFDRepMap S g :=
  (forget₂ (FDRep k S) (Rep k S)).map_injective (by
    simp only [forget₂_map_resFDRepMap, CategoryTheory.Functor.map_comp]
    rfl)

/-- Restriction to a subgroup, as a functor on finite-dimensional representations.  It acts on
objects as `resFDRep` and on intertwiners as `resFDRepMap`.

`@[simps obj map]` supplies the projection lemmas `resFDRepFunctor_obj` and `resFDRepFunctor_map`.
Both are proved by `rfl`, and the type of the second needs `(resFDRepFunctor S).obj B` to reduce to
`resFDRep S B`, so this definition is `@[expose]`.  Exposing it publishes exactly those two
projections: the construction of the morphism map lives in `resFDRepMap`, which stays opaque behind
`forget₂_map_resFDRepMap`. -/
@[expose, simps obj map]
noncomputable def resFDRepFunctor (S : Subgroup G) : FDRep k G ⥤ FDRep k S where
  obj B := resFDRep S B
  map f := resFDRepMap S f
  map_id B := resFDRepMap_id S B
  map_comp f g := resFDRepMap_comp S f g

/-- Under the forgetful functor to `Rep k S`, `resFDRepFunctor` is naturally isomorphic to
Mathlib's restriction functor, componentwise by `resFDRepForgetIso`. -/
noncomputable def resFDRepForgetNatIso (S : Subgroup G) :
    resFDRepFunctor (k := k) S ⋙ forget₂ (FDRep k S) (Rep k S) ≅
      forget₂ (FDRep k G) (Rep k G) ⋙ Rep.resFunctor S.subtype :=
  NatIso.ofComponents (fun B ↦ resFDRepForgetIso S B) fun {B B'} f ↦ by
    -- Naturality is the cancellation of the conjugating isomorphisms in `resFDRepMap`.
    change (forget₂ (FDRep k S) (Rep k S)).map (resFDRepMap S f) ≫ (resFDRepForgetIso S B').hom =
      (resFDRepForgetIso S B).hom ≫
        (Rep.resFunctor S.subtype).map ((forget₂ (FDRep k G) (Rep k G)).map f)
    rw [forget₂_map_resFDRepMap, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Representation

section Character

variable [Field k]

/-- The character of a restriction is the restriction of the character. -/
@[simp]
theorem character_resFDRep (S : Subgroup G) (B : FDRep k G) (s : S) :
    (resFDRep S B).character s = B.character (s : G) :=
  (rfl)

end Character

end TauCeti
