/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Comodule.Basic

/-!
# The category of point representations

Let `H` be a commutative Hopf algebra over a commutative ring `R`. This file bundles natural
actions of the affine group represented by `H` into a category. Morphisms are linear maps whose
scalar extensions intertwine every algebra-valued point action.

The objects and the value-algebra category used by their actions live in the maximum universe of
`R`, `H`, and the underlying module. In particular, morphisms here relate representations whose
underlying modules lie in the same universe.

## Main declarations

* `TauCeti.PointRepresentationCat`: the category of natural point representations.
* `TauCeti.PointRepresentationCat.Hom`: equivariant linear maps between point representations.

## References

* J. S. Milne, *Basic Theory of Affine Group Schemes*, Chapter VIII, §§2, 4, and 6.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 4(a), Remark 4.1.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v w

variable (R : Type u) [CommRing R]
variable (H : Type v) [CommRing H] [HopfAlgebra R H]

/-- The category of natural point representations of the affine group represented by `H`.

An object is an `R`-module together with a natural action of the represented point groups on all
of its scalar extensions. -/
structure PointRepresentationCat extends SemimoduleCat.{w} R where
  /-- The natural point action on the underlying module. -/
  representation : HopfAlgebra.PointRepresentation (R := R) (H := H) (V := carrier)

namespace PointRepresentationCat

instance : CoeSort (PointRepresentationCat.{u, v, w} R H) (Type w) :=
  ⟨fun V ↦ V.toSemimoduleCat⟩

instance (V : PointRepresentationCat.{u, v, w} R H) : AddCommMonoid V :=
  V.isAddCommMonoid

instance (V : PointRepresentationCat.{u, v, w} R H) : Module R V :=
  V.isModule

/-- Bundle a natural point representation on an `R`-module. -/
abbrev of (V : Type w) [AddCommMonoid V] [Module R V]
    (Theta : HopfAlgebra.PointRepresentation (R := R) (H := H) (V := V)) :
    PointRepresentationCat.{u, v, w} R H where
  carrier := V
  representation := Theta

/-- A morphism of point representations is a linear map whose scalar extensions intertwine every
algebra-valued point action in `CommAlgCat.{max u v w} R`. -/
structure Hom (V W : PointRepresentationCat.{u, v, w} R H) where
  /-- The underlying linear map. -/
  toLinearMap : V →ₗ[R] W
  /-- Every scalar extension of the linear map intertwines every point action. -/
  intertwines : ∀ (A : CommAlgCat.{max u v w} R) (x : HopfAlgebra.points (H := H) A),
    toLinearMap.baseChange A ∘ₗ (V.representation.action A x).val =
      (W.representation.action A x).val ∘ₗ toLinearMap.baseChange A

namespace Hom

/-- The identity morphism of a point representation. -/
def id (V : PointRepresentationCat.{u, v, w} R H) : Hom R H V V where
  toLinearMap := LinearMap.id
  intertwines A x := by simp

/-- Composition of morphisms of point representations. -/
def comp {U V W : PointRepresentationCat.{u, v, w} R H}
    (g : Hom R H V W) (f : Hom R H U V) : Hom R H U W where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  intertwines A x := by
    rw [LinearMap.baseChange_comp, LinearMap.comp_assoc, f.intertwines,
      ← LinearMap.comp_assoc, g.intertwines, LinearMap.comp_assoc]

private theorem id_toLinearMap (V : PointRepresentationCat.{u, v, w} R H) :
    (id R H V).toLinearMap = LinearMap.id := by
  rw [id]

private theorem comp_toLinearMap {U V W : PointRepresentationCat.{u, v, w} R H}
    (g : Hom R H V W) (f : Hom R H U V) :
    (comp R H g f).toLinearMap = g.toLinearMap.comp f.toLinearMap := by
  rw [comp]

/-- Morphisms of point representations are equal when their underlying linear maps are equal. -/
theorem ext {V W : PointRepresentationCat.{u, v, w} R H} {f g : Hom R H V W}
    (h : f.toLinearMap = g.toLinearMap) : f = g := by
  cases f
  cases g
  simp_all

end Hom

instance category : Category (PointRepresentationCat.{u, v, w} R H) where
  Hom := Hom R H
  id := Hom.id R H
  comp f g := Hom.comp R H g f
  id_comp _ := Hom.ext R H (by simp only [Hom.comp_toLinearMap, Hom.id_toLinearMap,
    LinearMap.comp_id])
  comp_id _ := Hom.ext R H (by simp only [Hom.comp_toLinearMap, Hom.id_toLinearMap,
    LinearMap.id_comp])
  assoc _ _ _ := Hom.ext R H (by simp only [Hom.comp_toLinearMap, LinearMap.comp_assoc])

instance {V W : PointRepresentationCat.{u, v, w} R H} : FunLike (Hom R H V W) V W where
  coe f := f.toLinearMap
  coe_injective _ _ h :=
    Hom.ext R H <| LinearMap.ext fun v ↦ congrFun h v

/-- `PointRepresentationCat` is concrete, with concrete morphisms the equivariant linear maps. -/
instance concreteCategory :
    ConcreteCategory (PointRepresentationCat.{u, v, w} R H) (Hom R H) where
  hom f := f
  ofHom f := f

/-- Two categorical morphisms of point representations are equal when they agree on every
vector. -/
@[ext]
theorem hom_ext {V W : PointRepresentationCat.{u, v, w} R H} {f g : V ⟶ W}
    (h : ∀ v, f v = g v) : f = g :=
  Hom.ext R H (LinearMap.ext h)

/-- The identity morphism has the identity linear map underneath. -/
@[simp]
theorem toLinearMap_id (V : PointRepresentationCat.{u, v, w} R H) :
    (CategoryStruct.id V).toLinearMap = LinearMap.id :=
  Hom.id_toLinearMap R H V

/-- Composition of representation morphisms is composition of their underlying linear maps. -/
@[simp]
theorem toLinearMap_comp {U V W : PointRepresentationCat.{u, v, w} R H}
    (f : U ⟶ V) (g : V ⟶ W) :
    (f ≫ g).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  Hom.comp_toLinearMap R H g f

/-- Forget a point representation to its underlying semimodule. -/
instance hasForgetToSemimodule :
    HasForget₂ (PointRepresentationCat.{u, v, w} R H) (SemimoduleCat.{w} R) where
  forget₂ :=
    { obj V := SemimoduleCat.of R V
      map f := SemimoduleCat.ofHom f.toLinearMap }

/-- The forgetful functor sends a point representation to its underlying semimodule. -/
@[simp]
theorem forget₂_obj (V : PointRepresentationCat.{u, v, w} R H) :
    (forget₂ (PointRepresentationCat.{u, v, w} R H) (SemimoduleCat.{w} R)).obj V =
      SemimoduleCat.of R V :=
  rfl

/-- The forgetful functor sends a representation morphism to its underlying linear map. -/
@[simp]
theorem forget₂_map {V W : PointRepresentationCat.{u, v, w} R H} (f : V ⟶ W) :
    (forget₂ (PointRepresentationCat.{u, v, w} R H) (SemimoduleCat.{w} R)).map f =
      SemimoduleCat.ofHom f.toLinearMap :=
  rfl

/-- A categorical isomorphism of point representations induces the underlying linear
equivalence. -/
def isoToLinearEquiv {V W : PointRepresentationCat.{u, v, w} R H} (i : V ≅ W) : V ≃ₗ[R] W :=
  ((forget₂ (PointRepresentationCat.{u, v, w} R H) (SemimoduleCat.{w} R)).mapIso i).toLinearEquivₛ

end PointRepresentationCat

end TauCeti
