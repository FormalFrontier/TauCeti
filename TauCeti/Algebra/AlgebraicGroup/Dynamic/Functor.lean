/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Parabolic
public import TauCeti.Algebra.AlgebraicGroup.PointsFunctor

/-!
# Dynamic subgroup functors

The dynamic parabolic, Levi, and unipotent subgroups attached to a cocharacter are defined on
points in `TauCeti.Algebra.AlgebraicGroup.Dynamic.Parabolic`. Their change-of-value-algebra
theorems make these families into group-valued functors. This file packages those functors and
their natural inclusions into the ambient functor of points.

The packaging is the interface needed to state representability. In particular, a dynamic
subgroup is represented by an affine group scheme precisely when its functor below is naturally
isomorphic to the functor of points of a commutative Hopf algebra.

## Main declarations

* `TauCeti.Cocharacter.parabolicFunctor`: the dynamic parabolic as a group-valued functor.
* `TauCeti.Cocharacter.leviFunctor`: the dynamic Levi as a group-valued functor.
* `TauCeti.Cocharacter.unipotentFunctor`: the dynamic unipotent subgroup as a group-valued
  functor.
* `TauCeti.Cocharacter.parabolicFunctorIncl`, `leviFunctorIncl`, and `unipotentFunctorIncl`:
  their natural inclusions into the ambient functor of points.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.

This is the functorial interface for the dynamic approach to parabolic, Levi, and unipotent
subgroups in Layer 7, "Structure theory", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.Cocharacter

universe u v w

variable {R : Type u} [CommRing R]
variable {H : Type v} [CommRing H] [HopfAlgebra R H]

/-- Change of value algebra, restricted to a dynamic parabolic subgroup. -/
@[expose] noncomputable def mapParabolic (l : H →ₐc[R] LaurentPolynomial R)
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    parabolic A l →* parabolic B l :=
  ((AlgHom.mapValue (H := H) φ.hom).domRestrict (parabolic A l)).codRestrict
    (parabolic B l) fun g ↦ parabolic_le_comap φ.hom g.2

/-- Change of value algebra, restricted to a dynamic Levi subgroup. -/
@[expose] noncomputable def mapLevi (l : H →ₐc[R] LaurentPolynomial R)
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    levi A l →* levi B l :=
  ((AlgHom.mapValue (H := H) φ.hom).domRestrict (levi A l)).codRestrict
    (levi B l) fun g ↦ levi_le_comap φ.hom g.2

/-- Change of value algebra, restricted to a dynamic unipotent subgroup. -/
@[expose] noncomputable def mapUnipotent (l : H →ₐc[R] LaurentPolynomial R)
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    unipotent A l →* unipotent B l :=
  ((AlgHom.mapValue (H := H) φ.hom).domRestrict (unipotent A l)).codRestrict
    (unipotent B l) fun g ↦ unipotent_le_comap φ.hom g.2

@[simp]
theorem coe_mapParabolic_apply (l : H →ₐc[R] LaurentPolynomial R)
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B) (g : parabolic A l) :
    (mapParabolic l φ g : WithConv (H →ₐ[R] B)) = AlgHom.mapValue φ.hom g :=
  rfl

@[simp]
theorem coe_mapLevi_apply (l : H →ₐc[R] LaurentPolynomial R)
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B) (g : levi A l) :
    (mapLevi l φ g : WithConv (H →ₐ[R] B)) = AlgHom.mapValue φ.hom g :=
  rfl

@[simp]
theorem coe_mapUnipotent_apply (l : H →ₐc[R] LaurentPolynomial R)
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B) (g : unipotent A l) :
    (mapUnipotent l φ g : WithConv (H →ₐ[R] B)) = AlgHom.mapValue φ.hom g :=
  rfl

/-- The dynamic parabolic attached to a cocharacter, as a group-valued functor. -/
@[expose] noncomputable def parabolicFunctor (l : H →ₐc[R] LaurentPolynomial R) :
    CommAlgCat.{w} R ⥤ GrpCat.{max v w} where
  obj A := GrpCat.of (parabolic A l)
  map φ := GrpCat.ofHom (mapParabolic l φ)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The dynamic Levi attached to a cocharacter, as a group-valued functor. -/
@[expose] noncomputable def leviFunctor (l : H →ₐc[R] LaurentPolynomial R) :
    CommAlgCat.{w} R ⥤ GrpCat.{max v w} where
  obj A := GrpCat.of (levi A l)
  map φ := GrpCat.ofHom (mapLevi l φ)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The dynamic unipotent subgroup attached to a cocharacter, as a group-valued functor. -/
@[expose] noncomputable def unipotentFunctor (l : H →ₐc[R] LaurentPolynomial R) :
    CommAlgCat.{w} R ⥤ GrpCat.{max v w} where
  obj A := GrpCat.of (unipotent A l)
  map φ := GrpCat.ofHom (mapUnipotent l φ)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

@[simp]
theorem parabolicFunctor_obj (l : H →ₐc[R] LaurentPolynomial R) (A : CommAlgCat.{w} R) :
    (parabolicFunctor l).obj A = GrpCat.of (parabolic A l) :=
  rfl

@[simp]
theorem leviFunctor_obj (l : H →ₐc[R] LaurentPolynomial R) (A : CommAlgCat.{w} R) :
    (leviFunctor l).obj A = GrpCat.of (levi A l) :=
  rfl

@[simp]
theorem unipotentFunctor_obj (l : H →ₐc[R] LaurentPolynomial R)
    (A : CommAlgCat.{w} R) :
    (unipotentFunctor l).obj A = GrpCat.of (unipotent A l) :=
  rfl

@[simp]
theorem parabolicFunctor_map (l : H →ₐc[R] LaurentPolynomial R)
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    (parabolicFunctor l).map φ = GrpCat.ofHom (mapParabolic l φ) :=
  rfl

@[simp]
theorem leviFunctor_map (l : H →ₐc[R] LaurentPolynomial R)
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    (leviFunctor l).map φ = GrpCat.ofHom (mapLevi l φ) :=
  rfl

@[simp]
theorem unipotentFunctor_map (l : H →ₐc[R] LaurentPolynomial R)
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    (unipotentFunctor l).map φ = GrpCat.ofHom (mapUnipotent l φ) :=
  rfl

/-- The dynamic parabolic functor includes naturally into the ambient functor of points. -/
@[expose] noncomputable def parabolicFunctorIncl (l : H →ₐc[R] LaurentPolynomial R) :
    parabolicFunctor l ⟶ HopfAlgebra.pointsFunctor (R := R) (H := H) where
  app A := GrpCat.ofHom (parabolic A l).subtype
  naturality _ _ _ := by ext; rfl

/-- The dynamic Levi functor includes naturally into the ambient functor of points. -/
@[expose] noncomputable def leviFunctorIncl (l : H →ₐc[R] LaurentPolynomial R) :
    leviFunctor l ⟶ HopfAlgebra.pointsFunctor (R := R) (H := H) where
  app A := GrpCat.ofHom (levi A l).subtype
  naturality _ _ _ := by ext; rfl

/-- The dynamic unipotent functor includes naturally into the ambient functor of points. -/
@[expose] noncomputable def unipotentFunctorIncl (l : H →ₐc[R] LaurentPolynomial R) :
    unipotentFunctor l ⟶ HopfAlgebra.pointsFunctor (R := R) (H := H) where
  app A := GrpCat.ofHom (unipotent A l).subtype
  naturality _ _ _ := by ext; rfl

@[simp]
theorem parabolicFunctorIncl_app (l : H →ₐc[R] LaurentPolynomial R)
    (A : CommAlgCat.{w} R) :
    (parabolicFunctorIncl l).app A = GrpCat.ofHom (parabolic A l).subtype :=
  rfl

@[simp]
theorem leviFunctorIncl_app (l : H →ₐc[R] LaurentPolynomial R)
    (A : CommAlgCat.{w} R) :
    (leviFunctorIncl l).app A = GrpCat.ofHom (levi A l).subtype :=
  rfl

@[simp]
theorem unipotentFunctorIncl_app (l : H →ₐc[R] LaurentPolynomial R)
    (A : CommAlgCat.{w} R) :
    (unipotentFunctorIncl l).app A = GrpCat.ofHom (unipotent A l).subtype :=
  rfl

end TauCeti.Cocharacter
