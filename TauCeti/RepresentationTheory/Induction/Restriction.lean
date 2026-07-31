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

For a subgroup `S` of a group `G` this file names the restriction of a finite-dimensional
representation of `G` to `S` and records its character.

`FDRep k G` is by definition `Action (FGModuleCat k) G`, so Mathlib's `Action.res` along
`S.subtype` *is* the restriction functor `FDRep k G ⥤ FDRep k S`; nothing has to be built.
Accordingly `resFDRep` is a reducible abbreviation for that functor on objects, exactly as
Mathlib's `Rep.res` is one for `Rep.resFunctor` on objects, and everything functorial —
restriction of an intertwiner, the functor laws, naturality — is used straight from
`Action.res (FGModuleCat k) S.subtype` and its `@[simps]` lemmas (`Action.res_obj_V`,
`Action.res_obj_ρ`, `Action.res_map_hom`) rather than restated here.

## Main definitions

* `TauCeti.resFDRep`: restriction of a finite-dimensional representation to a subgroup.

## Implementation notes

The abbreviation is over a commutative ring, matching Mathlib's `Action.res`; `Field k` enters
only with `FDRep.character`.

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

/-- Restriction of a finite-dimensional representation of `G` to a subgroup `S`: Mathlib's
`Action.res` along `S.subtype`, under the definitional identification
`FDRep k G = Action (FGModuleCat k) G`.

This is a reducible abbreviation, so Mathlib's `Action.res` API applies to it unchanged; in
particular `(Action.res (FGModuleCat k) S.subtype).map f : resFDRep S B ⟶ resFDRep S B'`
restricts an intertwiner, and is functorial by `Functor.map_id` and `Functor.map_comp`. -/
abbrev resFDRep (S : Subgroup G) (B : FDRep k G) : FDRep k S :=
  (Action.res (FGModuleCat k) S.subtype).obj B

/-- Restriction commutes with forgetting finite-dimensionality: after forgetting, `resFDRep` is
Mathlib's `Rep.res`, on the nose rather than up to isomorphism. -/
@[simp]
theorem forget₂_obj_resFDRep (S : Subgroup G) (B : FDRep k G) :
    (forget₂ (FDRep k S) (Rep k S)).obj (resFDRep S B) =
      Rep.res S.subtype ((forget₂ (FDRep k G) (Rep k G)).obj B) :=
  rfl

end Representation

section Character

variable [Field k]

/-- The character of a restriction is the restriction of the character. -/
@[simp]
theorem character_resFDRep (S : Subgroup G) (B : FDRep k G) (s : S) :
    (resFDRep S B).character s = B.character (s : G) :=
  rfl

end Character

end TauCeti
