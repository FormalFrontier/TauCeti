/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Rep.Res

/-!
# Restriction of representations

This file collects restriction infrastructure shared by the induction files: how the restriction
functors `Rep.resFunctor` and `Action.res` behave under composing and inverting the homomorphism
restricted along, and, for a subgroup `S` of a group `G`, the restriction of a finite-dimensional
representation of `G` to `S` together with its character.

`FDRep k G` is by definition `Action (FGModuleCat k) G`, so Mathlib's `Action.res` along
`S.subtype` *is* the restriction functor `FDRep k G ⥤ FDRep k S`; nothing has to be built.
Accordingly `resFDRep` is a reducible abbreviation for that functor on objects, exactly as
Mathlib's `Rep.res` is one for `Rep.resFunctor` on objects, and everything functorial —
restriction of an intertwiner, the functor laws, naturality — is used straight from
`Action.res (FGModuleCat k) S.subtype` and its `@[simps]` lemmas (`Action.res_obj_V`,
`Action.res_obj_ρ`, `Action.res_map_hom`) rather than restated here.

## Main definitions

* `TauCeti.resFunctorEquiv`: restriction along a monoid isomorphism, as an equivalence of
  categories.
* `TauCeti.resFDRep`: restriction of a finite-dimensional representation to a subgroup.

## Main statements

* `TauCeti.resFunctor_comp`, `TauCeti.actionRes_comp`: restriction along a composite is
  restriction twice over.

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

section Functor

variable [Semiring k] {H K L : Type*} [Monoid H] [Monoid K] [Monoid L]

/-- Restricting representations along a composite homomorphism is restricting twice over.
Mathlib has no equality of this shape (`Action.resComp` is the natural isomorphism for `Action`),
so we record the equality form, which keeps the reduction out of proofs that state equalities of
restriction functors. -/
theorem resFunctor_comp (φ : K →* L) (ψ : H →* K) :
    Rep.resFunctor (k := k) (φ.comp ψ) = Rep.resFunctor φ ⋙ Rep.resFunctor ψ :=
  rfl

/-- The `Action` form of `resFunctor_comp`, which is the one that applies to `FDRep`; the equality
strengthens Mathlib's natural isomorphism `Action.resComp`. -/
theorem actionRes_comp {V : Type*} [Category V] (φ : K →* L) (ψ : H →* K) :
    Action.res V (φ.comp ψ) = Action.res V φ ⋙ Action.res V ψ :=
  rfl

/-- Restricting along the identity is the identity functor. -/
theorem resFunctor_id : Rep.resFunctor (k := k) (MonoidHom.id H) = 𝟭 (Rep k H) :=
  rfl

/-- Restriction along a monoid isomorphism is an equivalence of categories, with inverse
restriction along the inverse isomorphism.  This is the `Rep` analogue of Mathlib's
`Action.resEquiv`, which does not apply because `Rep` is a structure rather than an `Action`.

`@[expose]` so that `resFunctorEquiv_functor` and `resFunctorEquiv_inverse` identify its two
functors with restriction downstream. -/
@[expose]
def resFunctorEquiv (e : H ≃* K) : Rep k K ≌ Rep k H :=
  CategoryTheory.Equivalence.mk (Rep.resFunctor e.toMonoidHom) (Rep.resFunctor e.symm.toMonoidHom)
    (eqToIso (by
      rw [← resFunctor_comp,
        show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id K from
          MonoidHom.ext fun x => by simp,
        resFunctor_id]))
    (eqToIso (by
      rw [← resFunctor_comp,
        show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id H from
          MonoidHom.ext fun x => by simp,
        resFunctor_id]))

@[simp]
theorem resFunctorEquiv_functor (e : H ≃* K) :
    (resFunctorEquiv (k := k) e).functor = Rep.resFunctor e.toMonoidHom :=
  rfl

@[simp]
theorem resFunctorEquiv_inverse (e : H ≃* K) :
    (resFunctorEquiv (k := k) e).inverse = Rep.resFunctor e.symm.toMonoidHom :=
  rfl

end Functor

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
