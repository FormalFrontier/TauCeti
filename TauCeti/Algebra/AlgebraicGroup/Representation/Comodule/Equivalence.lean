/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import TauCeti.Algebra.AlgebraicGroup.Representation.Comodule.Cat
public import TauCeti.Algebra.AlgebraicGroup.Representation.Comodule.Morphism
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Basic

/-!
# The point-representation--comodule equivalence

Let `H` be a commutative Hopf algebra over a commutative ring `R`. A point representation of the
affine group represented by `H` is a natural action of every group of algebra-valued points on the
corresponding scalar extension of a fixed `R`-module. The objects and their value-algebra category
live in the maximum universe of `R`, `H`, and their shared underlying-module universe.

The fixed-module representation--comodule correspondence and its morphism criterion identify this
category with the category of right `H`-comodules. Thus the functor-of-points and coordinate-Hopf-
algebra descriptions agree not only on objects, but also on morphisms.

## Main declarations

* `TauCeti.PointRepresentationCat.toComodule`: the functor recovering the associated comodule.
* `TauCeti.pointRepresentationCategoryEquivalence`: the equivalence between point
  representations and right comodules.
* `TauCeti.FGPointRepresentationCat`: the finite-generation restriction, equivalent to
  `FGComoduleCat` and hence the finite-dimensional representation category over a field.
* `TauCeti.FGPointRepresentationCat.toComodule`: the finite-generation restriction of the
  comodule functor.
* `TauCeti.fgPointRepresentationCategoryEquivalence`: the equivalence between finitely generated
  point representations and comodules.

## References

* J. S. Milne, *Basic Theory of Affine Group Schemes*, Chapter VIII, §§2, 4, and 6.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 4(a), Remark 4.1.

This supplies the categorical form of the Layer 1 representation--comodule dictionary in the
ReductiveGroups roadmap; the monoidal and rigid refinements are not provided here.
-/

public section

open CategoryTheory TensorProduct

namespace TauCeti

universe u v w

variable (R : Type u) [CommRing R]
variable (H : Type v) [CommRing H] [HopfAlgebra R H]

namespace PointRepresentationCat

/-- Recover the right comodule underlying a natural point representation. -/
@[expose] noncomputable def toComodule :
    PointRepresentationCat.{u, v, w} R H ⥤ ComoduleCat.{u, v, w} R H where
  obj V :=
    { toSemimoduleCat := V.toSemimoduleCat
      instComodule := HopfAlgebra.PointRepresentation.toComodule V.representation }
  map {V W} f :=
    letI : Comodule R H V := HopfAlgebra.PointRepresentation.toComodule V.representation
    letI : Comodule R H W := HopfAlgebra.PointRepresentation.toComodule W.representation
    { toLinearMap := f.toLinearMap
      map_coact :=
        (HopfAlgebra.PointRepresentation.map_coact_iff_baseChange_comp_action
          V.representation W.representation f.toLinearMap).mpr f.intertwines }
  map_id V := ComoduleCat.hom_ext (R := R) (C := H) fun v ↦
    LinearMap.congr_fun (toLinearMap_id R H V) v
  map_comp f g := ComoduleCat.hom_ext (R := R) (C := H) fun v ↦
    LinearMap.congr_fun (toLinearMap_comp R H f g) v

/-- The comodule functor leaves the underlying bundled semimodule of an object unchanged. -/
@[simp]
theorem toComodule_obj_toSemimoduleCat (V : PointRepresentationCat.{u, v, w} R H) :
    ((toComodule R H).obj V).toSemimoduleCat = V.toSemimoduleCat :=
  rfl

/-- The coaction on the image of a point representation is its recovered coaction. -/
@[simp]
theorem toComodule_obj_coact (V : PointRepresentationCat.{u, v, w} R H) :
    Comodule.coact (R := R) (C := H) (M := (toComodule R H).obj V) =
      (HopfAlgebra.PointRepresentation.toComodule V.representation).coact :=
  rfl

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
  preimage_map _ := PointRepresentationCat.Hom.ext R H rfl

/-- Bundle a right comodule as its associated natural point representation, preserving its
underlying bundled semimodule. -/
@[expose] noncomputable def ofComodule (M : ComoduleCat.{u, v, w} R H) :
    PointRepresentationCat.{u, v, w} R H where
  toSemimoduleCat := M.toSemimoduleCat
  representation := HopfAlgebra.PointRepresentation.ofComodule
    (inferInstance : Comodule R H M)

/-- The point representation associated to a comodule has the same underlying bundled
semimodule. -/
@[simp]
theorem ofComodule_toSemimoduleCat (M : ComoduleCat.{u, v, w} R H) :
    (ofComodule R H M).toSemimoduleCat = M.toSemimoduleCat :=
  rfl

/-- The point action associated to a comodule is the comodule point-action endomorphism. -/
@[simp]
theorem ofComodule_action_val (M : ComoduleCat.{u, v, w} R H)
    (A : CommAlgCat.{max u v w} R) (x : HopfAlgebra.points (H := H) A) :
    (@HopfAlgebra.PointRepresentation.action R H M _ _ _
      (ofComodule R H M).isAddCommMonoid (ofComodule R H M).isModule
      (ofComodule R H M).representation A x).val =
      Comodule.endOfPoint M x.ofConv :=
  HopfAlgebra.PointRepresentation.ofComodule_action_val_eq_endOfPoint
    (inferInstance : Comodule R H M) A x

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

/-- Natural point representations of an affine group and comodules over its coordinate Hopf
algebra form equivalent categories. -/
noncomputable def pointRepresentationCategoryEquivalence :
    PointRepresentationCat.{u, v, w} R H ≌ ComoduleCat.{u, v, w} R H :=
  (PointRepresentationCat.toComodule R H).asEquivalence

/-- The forward functor of the point-representation equivalence is the concrete comodule
functor. -/
@[simp]
theorem pointRepresentationCategoryEquivalence_functor :
    (pointRepresentationCategoryEquivalence R H).functor =
      PointRepresentationCat.toComodule R H := by
  rw [pointRepresentationCategoryEquivalence, Functor.asEquivalence_functor]

/-- The inverse equivalence sends a comodule to its associated point representation, up to the
canonical isomorphism selected by `Functor.inv`. -/
noncomputable def pointRepresentationCategoryEquivalence.inverseObjIsoOfComodule
    (M : ComoduleCat.{u, v, w} R H) :
    (pointRepresentationCategoryEquivalence R H).inverse.obj M ≅
      PointRepresentationCat.ofComodule R H M := by
  let hfunctorObj :
      (pointRepresentationCategoryEquivalence R H).functor.obj
          (PointRepresentationCat.ofComodule R H M) = M :=
    congrArg (fun F ↦ F.obj (PointRepresentationCat.ofComodule R H M))
        (pointRepresentationCategoryEquivalence_functor R H) |>.trans
      (PointRepresentationCat.toComodule_obj_ofComodule R H M)
  exact (pointRepresentationCategoryEquivalence R H).inverse.mapIso
      (eqToIso hfunctorObj.symm) ≪≫
    ((pointRepresentationCategoryEquivalence R H).unitIso.app
      (PointRepresentationCat.ofComodule R H M)).symm

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

/-- Recovering the comodule of a point representation preserves finite generation. -/
@[simp]
theorem PointRepresentationCat.toComodule_obj_isFG_iff
    (V : PointRepresentationCat.{u, v, w} R H) :
    ComoduleCat.isFG (R := R) (C := H) ((PointRepresentationCat.toComodule R H).obj V) ↔
      PointRepresentationCat.isFG (R := R) (H := H) V :=
  Iff.rfl

/-- The category of finitely generated natural point representations. Over a field, this is the
category of finite-dimensional representations of the affine group represented by `H`. -/
abbrev FGPointRepresentationCat :=
  (PointRepresentationCat.isFG (R := R) (H := H)).FullSubcategory

/-- Finite generation of point representations is preserved under categorical isomorphisms. -/
noncomputable instance PointRepresentationCat.isFG_isClosedUnderIsomorphisms :
    (PointRepresentationCat.isFG (R := R) (H := H) :
      ObjectProperty (PointRepresentationCat.{u, v, w} R H)).IsClosedUnderIsomorphisms where
  of_iso {V W} e h := by
    rw [PointRepresentationCat.isFG_iff] at h ⊢
    let _ : Module.Finite R V := h
    exact Module.Finite.equiv (PointRepresentationCat.isoToLinearEquiv (R := R) (H := H) e)

/-- Finitely generated point representations and finitely generated comodules form equivalent
categories. Over a field, this is the representation--comodule equivalence for finite-dimensional
representations. -/
@[expose] noncomputable def fgPointRepresentationCategoryEquivalence :
    FGPointRepresentationCat.{u, v, w} R H ≌ FGComoduleCat.{u, v, w} R H :=
  (PointRepresentationCat.toComodule R H).asEquivalence.congrFullSubcategory <| by
    ext V
    simp only [ObjectProperty.prop_inverseImage_iff, Functor.asEquivalence_functor,
      PointRepresentationCat.toComodule_obj_isFG_iff]

namespace FGPointRepresentationCat

/-- The underlying type of a finitely generated point representation. -/
@[expose, reducible]
def carrier (V : FGPointRepresentationCat.{u, v, w} R H) : Type w :=
  V.obj

instance : CoeSort (FGPointRepresentationCat.{u, v, w} R H) (Type w) :=
  ⟨carrier (R := R) (H := H)⟩

attribute [coe] carrier

instance (V : FGPointRepresentationCat.{u, v, w} R H) : AddCommMonoid V :=
  inferInstanceAs (AddCommMonoid V.obj)

instance (V : FGPointRepresentationCat.{u, v, w} R H) : Module R V :=
  inferInstanceAs (Module R V.obj)

/-- The underlying module of a finitely generated point representation is finitely generated. -/
instance (V : FGPointRepresentationCat.{u, v, w} R H) : Module.Finite R V :=
  V.property

/-- The natural point action of a finitely generated point representation. -/
abbrev representation (V : FGPointRepresentationCat.{u, v, w} R H) :
    HopfAlgebra.PointRepresentation (R := R) (H := H) (V := V) :=
  V.obj.representation

/-- The inclusion of finitely generated point representations into all point representations. -/
abbrev incl :
    FGPointRepresentationCat.{u, v, w} R H ⥤ PointRepresentationCat.{u, v, w} R H :=
  (PointRepresentationCat.isFG (R := R) (H := H)).ι

/-- Recover the finitely generated comodule underlying a finitely generated point
representation. This is the forward functor of `fgPointRepresentationCategoryEquivalence`. -/
noncomputable abbrev toComodule :
    FGPointRepresentationCat.{u, v, w} R H ⥤ FGComoduleCat.{u, v, w} R H :=
  (fgPointRepresentationCategoryEquivalence R H).functor

/-- The ambient comodule underlying the finite comodule functor is the recovered comodule. -/
@[simp]
theorem toComodule_obj_obj (V : FGPointRepresentationCat.{u, v, w} R H) :
    ((toComodule R H).obj V).obj =
      (PointRepresentationCat.toComodule R H).obj V.obj :=
  rfl

/-- The coaction on the finite comodule functor is the recovered coaction. -/
@[simp]
theorem toComodule_obj_coact (V : FGPointRepresentationCat.{u, v, w} R H) :
    Comodule.coact (R := R) (C := H) (M := (toComodule R H).obj V) =
      (HopfAlgebra.PointRepresentation.toComodule V.obj.representation).coact :=
  rfl

/-- The finite comodule functor leaves the underlying linear map of a morphism unchanged. -/
@[simp]
theorem toComodule_map_toLinearMap {V W : FGPointRepresentationCat.{u, v, w} R H}
    (f : V ⟶ W) :
    ((toComodule R H).map f).hom.toLinearMap = f.hom.toLinearMap :=
  rfl

end FGPointRepresentationCat

end TauCeti
