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

## Main definitions

* `TauCeti.resFDRep`: restriction of a finite-dimensional representation to a subgroup.
* `TauCeti.resFDRepForgetIso`: the identification of `resFDRep` with Mathlib's `Rep.res` after
  forgetting finite-dimensionality.

## Implementation notes

The body of `resFDRep` is not exposed; its characteristic properties are `character_resFDRep` and
`forget₂_obj_resFDRep`.  The latter is an *equality* of objects of `Rep k S` with `Rep.res`, not
merely an isomorphism, so it carries the description of the restricted representation and lets
Mathlib's `Rep.res` API transfer.  Since a sealed body cannot be unfolded while elaborating the
*type* of a later declaration, `resFDRepForgetIso` records the same identification as an
isomorphism, which downstream files use in place of the definitional equality; this mirrors
`TauCeti.indFDRepForgetIso`.

## References

This is restriction infrastructure for Layer 2 of
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

variable {k G : Type u} [Field k] [Group G]

/-- Restriction of a finite-dimensional representation of `G` to a subgroup `S`.  This is Mathlib's
`Action.res` along `S.subtype`, under the definitional identification
`FDRep k G = Action (FGModuleCat k) G`; this definition only supplies the representation-theoretic
name. -/
def resFDRep (S : Subgroup G) (B : FDRep k G) : FDRep k S :=
  (Action.res (FGModuleCat k) S.subtype).obj B

/-- The character of a restriction is the restriction of the character. -/
@[simp]
theorem character_resFDRep (S : Subgroup G) (B : FDRep k G) (s : S) :
    (resFDRep S B).character s = B.character (s : G) :=
  (rfl)

/-- Restriction commutes with forgetting finite-dimensionality. -/
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

end TauCeti
