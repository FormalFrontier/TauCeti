/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Comodule.Morphism
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Basic

/-!
# The category of point representations

Let `H` be a commutative Hopf algebra over a commutative ring `R`. A point representation of the
affine group represented by `H` is a natural action of every group of algebra-valued points on the
corresponding scalar extension of a fixed `R`-module. This file bundles these representations into
a category: morphisms are linear maps whose scalar extensions intertwine every point action.

The fixed-module representation--comodule correspondence and its morphism criterion identify this
category with the category of right `H`-comodules. Thus the functor-of-points and coordinate-Hopf-
algebra descriptions agree not only on objects, but also on morphisms.

## Main declarations

* `TauCeti.PointRepresentationCat`: the category of natural point representations.
* `TauCeti.PointRepresentationCat.toComodule`: the functor recovering the associated comodule.
* `TauCeti.pointRepresentationCategoryEquivalence`: the equivalence between point
  representations and right comodules.
* `TauCeti.FGPointRepresentationCat`: the finite-generation restriction, equivalent to
  `FGComoduleCat` and hence the finite-dimensional representation category over a field.

## References

* J. S. Milne, *Basic Theory of Affine Group Schemes*, Chapter VIII, §§2, 4, and 6.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 4(a), Remark 4.1.

This completes the categorical representation--comodule dictionary requested in Layer 1 of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory TensorProduct

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
algebra-valued point action. -/
structure Hom (V W : PointRepresentationCat.{u, v, w} R H) where
  /-- The underlying linear map. -/
  toLinearMap : V →ₗ[R] W
  /-- Every scalar extension of the linear map intertwines every point action. -/
  intertwines : ∀ (A : CommAlgCat.{max u v w} R) (x : HopfAlgebra.points (H := H) A),
    toLinearMap.baseChange A ∘ₗ (V.representation.action A x).val =
      (W.representation.action A x).val ∘ₗ toLinearMap.baseChange A

namespace Hom

/-- The identity morphism of a point representation. -/
@[expose] def id (V : PointRepresentationCat.{u, v, w} R H) : Hom R H V V where
  toLinearMap := LinearMap.id
  intertwines A x := by simp

/-- Composition of morphisms of point representations. -/
@[expose] def comp {U V W : PointRepresentationCat.{u, v, w} R H}
    (g : Hom R H V W) (f : Hom R H U V) : Hom R H U W where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  intertwines A x := by
    rw [LinearMap.baseChange_comp, LinearMap.comp_assoc, f.intertwines,
      ← LinearMap.comp_assoc, g.intertwines, LinearMap.comp_assoc]

/-- Morphisms of point representations are equal when their underlying linear maps are equal. -/
@[ext]
theorem ext_toLinearMap {V W : PointRepresentationCat.{u, v, w} R H} {f g : Hom R H V W}
    (h : f.toLinearMap = g.toLinearMap) : f = g := by
  cases f
  cases g
  simp_all

end Hom

instance category : Category (PointRepresentationCat.{u, v, w} R H) where
  Hom := Hom R H
  id := Hom.id R H
  comp f g := Hom.comp R H g f
  id_comp _ := Hom.ext_toLinearMap R H rfl
  comp_id _ := Hom.ext_toLinearMap R H rfl
  assoc _ _ _ := Hom.ext_toLinearMap R H rfl

instance {V W : PointRepresentationCat.{u, v, w} R H} : FunLike (Hom R H V W) V W where
  coe f := f.toLinearMap
  coe_injective _ _ h :=
    Hom.ext_toLinearMap R H <| LinearMap.ext fun v ↦ congrFun h v

/-- `PointRepresentationCat` is concrete, with concrete morphisms the equivariant linear maps. -/
instance concreteCategory :
    ConcreteCategory (PointRepresentationCat.{u, v, w} R H) (Hom R H) where
  hom f := f
  ofHom f := f

/-- The underlying linear map of a categorical morphism of point representations. -/
abbrev homLinearMap {V W : PointRepresentationCat.{u, v, w} R H} (f : V ⟶ W) : V →ₗ[R] W :=
  f.toLinearMap

/-- Two categorical morphisms of point representations are equal when their underlying linear
maps agree. -/
theorem hom_ext_toLinearMap {V W : PointRepresentationCat.{u, v, w} R H} {f g : V ⟶ W}
    (h : f.toLinearMap = g.toLinearMap) : f = g :=
  Hom.ext_toLinearMap R H h

/-- Two categorical morphisms of point representations are equal when they agree on every
vector. -/
@[ext]
theorem hom_ext {V W : PointRepresentationCat.{u, v, w} R H} {f g : V ⟶ W}
    (h : ∀ v, f v = g v) : f = g :=
  hom_ext_toLinearMap R H (LinearMap.ext h)

/-- The identity morphism has the identity linear map underneath. -/
@[simp]
theorem toLinearMap_id (V : PointRepresentationCat.{u, v, w} R H) :
    (CategoryStruct.id V).toLinearMap = LinearMap.id :=
  (rfl)

/-- Composition of representation morphisms is composition of their underlying linear maps. -/
@[simp]
theorem toLinearMap_comp {U V W : PointRepresentationCat.{u, v, w} R H}
    (f : U ⟶ V) (g : V ⟶ W) :
    (f ≫ g).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  (rfl)

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
  (rfl)

/-- The forgetful functor sends a representation morphism to its underlying linear map. -/
@[simp]
theorem forget₂_map {V W : PointRepresentationCat.{u, v, w} R H} (f : V ⟶ W) :
    (forget₂ (PointRepresentationCat.{u, v, w} R H) (SemimoduleCat.{w} R)).map f =
      SemimoduleCat.ofHom f.toLinearMap :=
  (rfl)

/-- Recover the right comodule underlying a natural point representation. -/
@[expose] noncomputable def toComodule :
    PointRepresentationCat.{u, v, w} R H ⥤ ComoduleCat.{u, v, w} R H where
  obj V :=
    { toSemimoduleCat := V.toSemimoduleCat
      instComodule := HopfAlgebra.PointRepresentation.toComodule V.representation }
  map {V W} f := by
    letI : Comodule R H V := HopfAlgebra.PointRepresentation.toComodule V.representation
    letI : Comodule R H W := HopfAlgebra.PointRepresentation.toComodule W.representation
    exact ComoduleCat.ofHom (R := R) (C := H)
      { toLinearMap := f.toLinearMap
        map_coact :=
          (HopfAlgebra.PointRepresentation.map_coact_iff_baseChange_comp_action
            V.representation W.representation f.toLinearMap).mpr f.intertwines }
  map_id V := ComoduleCat.hom_ext (R := R) (C := H) fun _ ↦ rfl
  map_comp f g := ComoduleCat.hom_ext (R := R) (C := H) fun _ ↦ rfl

/-- The comodule functor leaves the underlying linear map of a morphism unchanged. -/
@[simp]
theorem toComodule_map_toLinearMap {V W : PointRepresentationCat.{u, v, w} R H}
    (f : V ⟶ W) :
    ((toComodule R H).map f).toLinearMap = f.toLinearMap :=
  rfl

/-- The comodule functor is fully faithful: colinearity is exactly equivariance for all
algebra-valued point actions. -/
noncomputable def toComoduleFullyFaithful :
    (toComodule R H : PointRepresentationCat.{u, v, w} R H ⥤
      ComoduleCat.{u, v, w} R H).FullyFaithful where
  preimage {V W} f :=
    { toLinearMap := f.toLinearMap
      intertwines :=
        (HopfAlgebra.PointRepresentation.map_coact_iff_baseChange_comp_action
          V.representation W.representation f.toLinearMap).mp f.map_coact }
  map_preimage _ := ComoduleCat.hom_ext (R := R) (C := H) fun _ ↦ rfl
  preimage_map _ := PointRepresentationCat.hom_ext_toLinearMap (R := R) (H := H) rfl

/-- Bundle a right comodule as its associated natural point representation, preserving its
underlying bundled semimodule. -/
noncomputable def ofComodule (M : ComoduleCat.{u, v, w} R H) :
    PointRepresentationCat.{u, v, w} R H where
  toSemimoduleCat := M.toSemimoduleCat
  representation := HopfAlgebra.PointRepresentation.ofComodule
    (inferInstance : Comodule R H M)

/-- Recovering the comodule associated to `ofComodule` returns the original bundled comodule. -/
@[simp]
theorem toComodule_obj_ofComodule (M : ComoduleCat.{u, v, w} R H) :
    (toComodule R H).obj (ofComodule R H M) = M := by
  cases M with
  | mk S rho =>
      simp only [toComodule, ofComodule, ComoduleCat.mk.injEq, true_and]
      exact heq_of_eq (HopfAlgebra.PointRepresentation.toComodule_ofComodule rho)

/-- Every right comodule is isomorphic to the comodule recovered from its natural point
representation. -/
noncomputable instance toComoduleEssSurj :
    (toComodule R H : PointRepresentationCat.{u, v, w} R H ⥤
      ComoduleCat.{u, v, w} R H).EssSurj :=
  Functor.EssSurj.mk fun (M : ComoduleCat.{u, v, w} R H) ↦ by
    exact ⟨ofComodule R H M, ⟨eqToIso (toComodule_obj_ofComodule R H M)⟩⟩

/-- Recovering comodules from natural point representations is an equivalence of categories. -/
noncomputable instance toComoduleIsEquivalence :
    (toComodule R H : PointRepresentationCat.{u, v, w} R H ⥤
      ComoduleCat.{u, v, w} R H).IsEquivalence where
  faithful := (toComoduleFullyFaithful R H).faithful
  full := (toComoduleFullyFaithful R H).full
  essSurj := inferInstance

end PointRepresentationCat

/-- The object property of finite generation on natural point representations. Over a field this
is finite-dimensionality of the representation. -/
def PointRepresentationCat.isFG :
    ObjectProperty (PointRepresentationCat.{u, v, w} R H) :=
  fun V ↦ Module.Finite R V

/-- Finite generation of a point representation is finite generation of its underlying
module. -/
theorem PointRepresentationCat.isFG_iff (V : PointRepresentationCat.{u, v, w} R H) :
    PointRepresentationCat.isFG (R := R) (H := H) V ↔ Module.Finite R V :=
  Iff.rfl

/-- The category of finitely generated natural point representations. Over a field, this is the
category of finite-dimensional representations of the affine group represented by `H`. -/
abbrev FGPointRepresentationCat :=
  (PointRepresentationCat.isFG (R := R) (H := H)).FullSubcategory

namespace FGPointRepresentationCat

/-- The inclusion of finitely generated point representations into all point representations. -/
abbrev incl :
    FGPointRepresentationCat.{u, v, w} R H ⥤ PointRepresentationCat.{u, v, w} R H :=
  (PointRepresentationCat.isFG (R := R) (H := H)).ι

/-- Recover the finitely generated comodule underlying a finitely generated point
representation. -/
@[expose] noncomputable def toComodule :
    FGPointRepresentationCat.{u, v, w} R H ⥤ FGComoduleCat.{u, v, w} R H :=
  (ComoduleCat.isFG (R := R) (C := H)).lift
    (incl R H ⋙ PointRepresentationCat.toComodule R H) fun V ↦ by
      change Module.Finite R V.obj
      exact V.property

/-- The finite comodule functor is fully faithful. -/
noncomputable def toComoduleFullyFaithful :
    (toComodule R H : FGPointRepresentationCat.{u, v, w} R H ⥤
      FGComoduleCat.{u, v, w} R H).FullyFaithful where
  preimage {V W} f := ObjectProperty.homMk <|
    (PointRepresentationCat.toComoduleFullyFaithful R H).preimage f.hom
  map_preimage _ := by
    apply ObjectProperty.hom_ext
    exact (PointRepresentationCat.toComoduleFullyFaithful R H).map_preimage _
  preimage_map _ := by
    apply ObjectProperty.hom_ext
    exact (PointRepresentationCat.toComoduleFullyFaithful R H).preimage_map _

/-- Every finitely generated comodule is represented by a finitely generated natural point
representation. -/
noncomputable instance toComoduleEssSurj :
    (toComodule R H : FGPointRepresentationCat.{u, v, w} R H ⥤
      FGComoduleCat.{u, v, w} R H).EssSurj :=
  Functor.EssSurj.mk fun M ↦ by
    let V : FGPointRepresentationCat.{u, v, w} R H :=
      ⟨PointRepresentationCat.ofComodule R H M.obj, M.property⟩
    refine ⟨V, ⟨(ComoduleCat.isFG (R := R) (C := H)).isoMk ?_⟩⟩
    exact eqToIso (PointRepresentationCat.toComodule_obj_ofComodule R H M.obj)

/-- Recovering finite comodules from finite point representations is an equivalence of
categories. -/
noncomputable instance toComoduleIsEquivalence :
    (toComodule R H : FGPointRepresentationCat.{u, v, w} R H ⥤
      FGComoduleCat.{u, v, w} R H).IsEquivalence where
  faithful := (toComoduleFullyFaithful R H).faithful
  full := (toComoduleFullyFaithful R H).full
  essSurj := inferInstance

end FGPointRepresentationCat

/-- Natural point representations of an affine group and comodules over its coordinate Hopf
algebra form equivalent categories. -/
noncomputable def pointRepresentationCategoryEquivalence :
    PointRepresentationCat.{u, v, w} R H ≌ ComoduleCat.{u, v, w} R H :=
  (PointRepresentationCat.toComodule R H).asEquivalence

/-- Finitely generated point representations and finitely generated comodules form equivalent
categories. Over a field, this is the representation--comodule equivalence for finite-dimensional
representations. -/
noncomputable def fgPointRepresentationCategoryEquivalence :
    FGPointRepresentationCat.{u, v, w} R H ≌ FGComoduleCat.{u, v, w} R H :=
  (FGPointRepresentationCat.toComodule R H).asEquivalence

/-- The forward functor in the finite representation--comodule equivalence recovers the
underlying finite comodule. -/
@[simp]
theorem fgPointRepresentationCategoryEquivalence_functor :
    (fgPointRepresentationCategoryEquivalence R H).functor =
      FGPointRepresentationCat.toComodule R H :=
  by rw [fgPointRepresentationCategoryEquivalence, Functor.asEquivalence_functor]

/-- The forward functor in the categorical representation--comodule equivalence recovers the
underlying comodule. -/
@[simp]
theorem pointRepresentationCategoryEquivalence_functor :
    (pointRepresentationCategoryEquivalence R H).functor =
      PointRepresentationCat.toComodule R H :=
  by rw [pointRepresentationCategoryEquivalence, Functor.asEquivalence_functor]

end TauCeti
