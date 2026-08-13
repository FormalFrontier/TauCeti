/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- The named additive presentation is used explicitly in the scheme morphism.
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Scheme
-- The ambient root subgroup supplies the matrix calculation and the named `GLₙ` presentation.
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.RootSubgroup
-- The determinant-one quotient supplies the special-linear coordinate Hopf algebra and points.
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Basic

/-!
# The root subgroups of the special linear group

For distinct indices `i ≠ j`, the elementary matrices

`xᵢⱼ(c) = 1 + c Eᵢⱼ`

have determinant one. This file promotes them to a morphism of affine group schemes

`xᵢⱼ : 𝔾ₐ → SLₙ`

over an arbitrary commutative base ring. The construction first forms the natural homomorphism
on algebra-valued points using Mathlib's `Matrix.SpecialLinearGroup.transvection`. Full
faithfulness of the functor of points then recovers the coordinate Hopf-algebra morphism
`O(SLₙ) → O(𝔾ₐ)`, and relative spectrum gives the group-scheme morphism.

The resulting morphism is not merely another presentation of the already constructed
general-linear root subgroup. Its composite with the determinant-kernel inclusion is proved to
be `TauCeti.GeneralLinear.rootSubgroup`. Thus the construction records scheme-theoretically that
the type-A root subgroup lands in determinant one, over every base ring and after every base
change.

## Main definitions

* `TauCeti.SpecialLinear.rootSubgroupPoints`: the homomorphism on algebra-valued points.
* `TauCeti.SpecialLinear.rootSubgroupCoordinateMap`: the coordinate morphism
  `O(SLₙ) → O(𝔾ₐ)`.
* `TauCeti.SpecialLinear.rootSubgroup`: the affine group-scheme morphism `𝔾ₐ → SLₙ`.
## Main results

* `TauCeti.SpecialLinear.schemePointsMulEquiv_rootSubgroup`: the root subgroup is the elementary
  transvection on scheme-valued points.
* `TauCeti.SpecialLinear.coordinateMap_comp_rootSubgroupCoordinateMap`: the coordinate-level
  factorization of the general-linear root subgroup.
* `TauCeti.SpecialLinear.rootSubgroup_comp_groupSchemeιGeneralLinear`: the corresponding
  factorization of group schemes.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.
* R. W. Carter, *Simple Groups of Lie Type* (1972), §11.3.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti

namespace SpecialLinear

universe u w

variable {R : Type u} [CommRing R] {N : ℕ} {i j : Fin N}

section Points

variable {A : Type w} [CommRing A] [Algebra R A]
variable {B : Type w} [CommRing B] [Algebra R B]

/-- The elementary determinant-one matrices at a fixed pair of indices form a one-parameter
subgroup. -/
private def transvectionHom (hij : i ≠ j) :
    Multiplicative A →* Matrix.SpecialLinearGroup (Fin N) A where
  toFun c := Matrix.SpecialLinearGroup.transvection hij (Multiplicative.toAdd c)
  map_one' := Matrix.SpecialLinearGroup.transvection_coeff_zero hij
  map_mul' c d := Matrix.SpecialLinearGroup.transvection_add hij
    (Multiplicative.toAdd c) (Multiplicative.toAdd d)

/-- The root subgroup homomorphism on `A`-points, sending the additive parameter to its
determinant-one elementary matrix. -/
noncomputable def rootSubgroupPoints (hij : i ≠ j) :
    WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R N →ₐ[R] A) :=
  ((pointsMulEquiv (R := R) (A := A) N).symm.toMonoidHom.comp
    ((transvectionHom hij).comp
      (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).toMonoidHom))

/-- Under the special-linear point equivalence, the root subgroup point is the elementary
transvection of its additive parameter. -/
theorem pointsMulEquiv_rootSubgroupPoints (hij : i ≠ j)
    (f : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := A) N (rootSubgroupPoints hij f) =
      Matrix.SpecialLinearGroup.transvection hij
        (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A) f)) := by
  rw [rootSubgroupPoints]
  simp [transvectionHom]

/-- The special-linear root subgroup is a monomorphism on algebra-valued points. -/
theorem rootSubgroupPoints_injective (hij : i ≠ j) :
    Function.Injective (rootSubgroupPoints (R := R) (A := A) hij) := by
  intro f g h
  have hSL := congrArg (pointsMulEquiv (R := R) (A := A) N) h
  rw [pointsMulEquiv_rootSubgroupPoints, pointsMulEquiv_rootSubgroupPoints] at hSL
  have hentry := congrArg
    (fun s : Matrix.SpecialLinearGroup (Fin N) A => (s : Matrix (Fin N) (Fin N) A) i j) hSL
  refine (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).injective ?_
  have hparameter :
      Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A) f) =
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A) g) := by
    simpa [Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply,
      Matrix.single_apply, hij] using hentry
  simpa only [ofAdd_toAdd] using
    congrArg (Multiplicative.ofAdd : A → Multiplicative A) hparameter

/-- Entrywise mapping of a determinant-one transvection maps its parameter. -/
private theorem map_transvection (φ : A →ₐ[R] B) (hij : i ≠ j) (c : A) :
    Matrix.SpecialLinearGroup.map φ.toRingHom
        (Matrix.SpecialLinearGroup.transvection hij c) =
      Matrix.SpecialLinearGroup.transvection hij (φ c) := by
  apply Matrix.SpecialLinearGroup.ext
  intro k l
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply, map_add]
  split_ifs <;> simp_all

/-- The special-linear root subgroup on points is natural in the value algebra. -/
theorem mapValue_rootSubgroupPoints (φ : A →ₐ[R] B) (hij : i ≠ j)
    (f : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R N) φ (rootSubgroupPoints hij f) =
      rootSubgroupPoints hij
        (AlgHom.mapValue (H := AdditiveGroup.coordinateHopfAlgebra R) φ f) := by
  apply (pointsMulEquiv (R := R) (A := B) N).injective
  -- `AlgHom.mapValue` and `HopfAlgebra.mapPoints` expose the same postcomposition map, but there
  -- is no comparison lemma between the bundled applications; restate it in the form used by the
  -- public naturality theorem `pointsMulEquiv_mapValue`.
  change (pointsMulEquiv (R := R) (A := B) N)
      (HopfAlgebra.mapPoints (H := coordinateHopfAlgebra R N)
        (CommAlgCat.ofHom φ) (rootSubgroupPoints hij f)) = _
  rw [pointsMulEquiv_mapValue,
    pointsMulEquiv_rootSubgroupPoints,
    pointsMulEquiv_rootSubgroupPoints, map_transvection,
    AdditiveGroup.toAdd_gaPointsMulEquiv_mapValue]

end Points

section Functor

/-- The natural transformation on group-valued points whose components are the special-linear
root subgroup homomorphisms. -/
noncomputable def rootSubgroupPointsMap (hij : i ≠ j) :
    HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R N) where
  app A := GrpCat.ofHom (rootSubgroupPoints (A := A) hij)
  naturality _ _ φ := by
    ext f
    exact (mapValue_rootSubgroupPoints φ.hom hij f).symm

/-- The component of the natural points map at a value algebra is the special-linear root
subgroup homomorphism. -/
@[simp]
theorem rootSubgroupPointsMap_app (hij : i ≠ j) (A : CommAlgCat.{w} R) :
    (rootSubgroupPointsMap (R := R) (N := N) hij).app A =
      GrpCat.ofHom (rootSubgroupPoints hij) :=
  (rfl)

end Functor

section Scheme

/-- The coordinate morphism of the special-linear root subgroup, recovered from its natural
action on points. -/
noncomputable def rootSubgroupCoordinateMap (hij : i ≠ j) :
    coordinateHopfAlgebra R N ⟶ AdditiveGroup.coordinateHopfAlgebra R :=
  ((CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}).preimage
    (rootSubgroupPointsMap.{u, u} (R := R) (N := N) hij)).unop

/-- Precomposition by the coordinate morphism is the constructed natural map on points. -/
theorem mapPointsFunctor_rootSubgroupCoordinateMap (hij : i ≠ j) :
    (CommHopfAlgCat.mapPointsFunctor.{u, u, u}
      (rootSubgroupCoordinateMap (R := R) (N := N) hij) :
      HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ⟶
        HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R N)) =
      (rootSubgroupPointsMap.{u, u} hij :
        HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ⟶
          HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R N)) := by
  unfold rootSubgroupCoordinateMap
  rw [← CommHopfAlgCat.pointsFunctor_map]
  exact Functor.map_preimage
    (CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}) _

/-- On a same-universe algebra, the coordinate morphism induces the previously constructed
special-linear root subgroup map. -/
@[simp]
theorem mapPointsFunctor_rootSubgroupCoordinateMap_app (hij : i ≠ j)
    (A : CommAlgCat.{u} R)
    (f : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A) :
    (CommHopfAlgCat.mapPointsFunctor
      (rootSubgroupCoordinateMap (R := R) (N := N) hij)).app A f =
      rootSubgroupPoints hij f := by
  rw [mapPointsFunctor_rootSubgroupCoordinateMap, rootSubgroupPointsMap_app]
  rfl

/-- The quotient coordinate map followed by the special-linear root coordinate map is the
general-linear root coordinate map. -/
theorem coordinateMap_comp_rootSubgroupCoordinateMap (hij : i ≠ j) :
    coordinateMap R N ≫ rootSubgroupCoordinateMap hij =
      GeneralLinear.rootSubgroupCoordinateMap hij := by
  apply Quiver.Hom.op_inj
  apply (CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R)).map_injective
  rw [op_comp, Functor.map_comp, CommHopfAlgCat.pointsFunctor_map,
    CommHopfAlgCat.pointsFunctor_map, CommHopfAlgCat.pointsFunctor_map]
  -- Mapping an opposite composite through `pointsFunctor` leaves the same natural
  -- transformation behind several category and opposite wrappers. There is no API lemma exposing
  -- that elaborated type, so restate it using the public `mapPointsFunctor` name before rewriting.
  change CommHopfAlgCat.mapPointsFunctor
      (rootSubgroupCoordinateMap (R := R) (N := N) hij) ≫
        CommHopfAlgCat.mapPointsFunctor (coordinateMap R N) =
    CommHopfAlgCat.mapPointsFunctor
      (GeneralLinear.rootSubgroupCoordinateMap (R := R) (N := N) hij)
  rw [mapPointsFunctor_rootSubgroupCoordinateMap,
    GeneralLinear.mapPointsFunctor_rootSubgroupCoordinateMap]
  ext A f
  rw [NatTrans.comp_app, rootSubgroupPointsMap_app,
    GeneralLinear.rootSubgroupPointsMap_app]
  -- Components of the rewritten natural transformations are still displayed through bundled
  -- categorical coercions; expose their pointwise maps to use the point-equivalence API.
  change (CommHopfAlgCat.mapPointsFunctor (coordinateMap R N)).app A
      (rootSubgroupPoints hij f) = GeneralLinear.rootSubgroupPoints hij f
  apply (GeneralLinear.pointsMulEquiv (R := R) (A := A) N).injective
  -- `coordinateMap` is the quotient map by definition, but the point-map and quotient-point APIs
  -- have no comparison theorem whose left side matches this bundled component. Name the quotient
  -- point explicitly so `pointsMulEquiv_toGL` applies.
  change GeneralLinear.pointsMulEquiv (R := R) (A := A) N
      (CommHopfAlgCat.quotientPointsHom
        (GeneralLinear.coordinateHopfAlgebra R N) (definingHopfIdeal R N) A
        (rootSubgroupPoints hij f)) = _
  rw [pointsMulEquiv_toGL]
  have hSL := pointsMulEquiv_rootSubgroupPoints
    (R := R) (A := A) hij f
  have hGL := GeneralLinear.pointsMulEquiv_rootSubgroupPoints
    (R := R) (A := A) hij f
  rw [hSL, hGL]
  apply Matrix.GeneralLinearGroup.ext
  intro k l
  rw [coe_transvectionUnit]
  rfl

/-- **The root subgroup of `SLₙ` attached to `εᵢ - εⱼ`**, as a morphism of affine group
schemes over the base ring. -/
noncomputable def rootSubgroup (hij : i ≠ j) :
    AdditiveGroup.groupScheme R ⟶ groupScheme R N :=
  eqToHom (AdditiveGroup.groupScheme_def R) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
      (rootSubgroupCoordinateMap hij).op ≫
    eqToHom (groupScheme_def R N).symm

section SchemePoints

variable (A : Type u) [CommRing A] [Algebra R A]

private lemma eqToHom_hom_hom_left {G G' : Grp (Over (Spec (CommRingCat.of R)))} (h : G = G') :
    (eqToHom h).hom.hom.left =
      eqToHom (congrArg (fun K : Grp (Over (Spec (CommRingCat.of R))) ↦ K.X.left) h) := by
  subst h
  rfl

private lemma hopfSpec_map_left {H K : _root_.CommHopfAlgCat.{u} R} (φ : H ⟶ K) :
    ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map φ.op).hom.hom.left =
      Spec.map (CommRingCat.ofHom φ.hom.toAlgHom.toRingHom) :=
  rfl

private lemma rootSubgroup_hom_hom_left (hij : i ≠ j) :
    (rootSubgroup (R := R) (N := N) hij).hom.hom.left =
      eqToHom (AdditiveGroup.groupScheme_X_left R) ≫
        Spec.map (CommRingCat.ofHom
          (rootSubgroupCoordinateMap hij).hom.toAlgHom.toRingHom) ≫
        eqToHom (groupScheme_X_left R N).symm := by
  rw [rootSubgroup]
  -- The underlying scheme morphism of a composite of group-object morphisms is definitionally
  -- the composite of the underlying maps; the category API has no projection lemma for it.
  rw [show ((eqToHom (AdditiveGroup.groupScheme_def R) ≫
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
        (rootSubgroupCoordinateMap (R := R) (N := N) hij).op ≫
      eqToHom (groupScheme_def R N).symm)).hom.hom.left =
    (eqToHom (AdditiveGroup.groupScheme_def R)).hom.hom.left ≫
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
        (rootSubgroupCoordinateMap (R := R) (N := N) hij).op).hom.hom.left ≫
      (eqToHom (groupScheme_def R N).symm).hom.hom.left from rfl]
  rw [eqToHom_hom_hom_left, eqToHom_hom_hom_left, hopfSpec_map_left]
  rfl

private lemma groupSchemePointMulEquiv_comp_rootSubgroup (hij : i ≠ j)
    (q : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    AdditiveGroup.groupSchemePointMulEquiv A q ≫ (rootSubgroup hij).hom.hom =
      groupSchemePointMulEquiv R N A (rootSubgroupPoints hij q) := by
  have hcomp : (rootSubgroupPoints hij q).ofConv =
      q.ofConv.comp (rootSubgroupCoordinateMap hij).hom.toAlgHom := by
    rw [← mapPointsFunctor_rootSubgroupCoordinateMap_app hij (CommAlgCat.of R A) q,
      CommHopfAlgCat.mapPointsFunctor_app_apply, WithConv.ofConv_toConv]
  apply Over.OverMorphism.ext
  rw [groupSchemePointMulEquiv_apply_left]
  rw [Over.comp_left, AdditiveGroup.groupSchemePointMulEquiv_apply_left,
    rootSubgroup_hom_hom_left]
  -- After the named additive presentation is cancelled, the remaining equality is the standard
  -- contravariant spectrum computation; this restatement only exposes those underlying maps.
  change (Spec.map (CommRingCat.ofHom q.ofConv.toRingHom) ≫
      eqToHom (AdditiveGroup.groupScheme_X_left R).symm) ≫
      eqToHom (AdditiveGroup.groupScheme_X_left R) ≫
        Spec.map (CommRingCat.ofHom
          (rootSubgroupCoordinateMap hij).hom.toAlgHom.toRingHom) ≫
        eqToHom (groupScheme_X_left R N).symm =
    Spec.map (CommRingCat.ofHom (rootSubgroupPoints hij q).ofConv.toRingHom) ≫
      eqToHom (groupScheme_X_left R N).symm
  rw [hcomp]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- **The root subgroup on scheme-valued points**: composing an `A`-point of `𝔾ₐ` with the
special-linear root subgroup gives the determinant-one transvection of its additive parameter. -/
@[simp]
theorem schemePointsMulEquiv_rootSubgroup (hij : i ≠ j)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (AdditiveGroup.groupScheme R).X) :
    schemePointsMulEquiv R N A (p ≫ (rootSubgroup hij).hom.hom) =
      Matrix.SpecialLinearGroup.transvection hij
        (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p)) := by
  obtain ⟨q, rfl⟩ :=
    (AdditiveGroup.groupSchemePointMulEquiv (R := R) (A := A)).surjective p
  have hSL : schemePointsMulEquiv R N A
      (groupSchemePointMulEquiv R N A (rootSubgroupPoints hij q)) =
      (pointsMulEquiv (R := R) (A := A) N) (rootSubgroupPoints hij q) := by
    apply (schemePointsMulEquiv R N A).symm.injective
    rw [MulEquiv.symm_apply_apply, schemePointsMulEquiv_symm_apply,
      MulEquiv.symm_apply_apply]
  have hGa : AdditiveGroup.schemePointsMulEquiv A
      (AdditiveGroup.groupSchemePointMulEquiv A q) =
      AdditiveGroup.gaPointsMulEquiv q := by
    apply (AdditiveGroup.schemePointsMulEquiv (R := R) A).symm.injective
    rw [MulEquiv.symm_apply_apply, AdditiveGroup.schemePointsMulEquiv_symm_apply,
      MulEquiv.symm_apply_apply]
  rw [groupSchemePointMulEquiv_comp_rootSubgroup, hSL, hGa,
    pointsMulEquiv_rootSubgroupPoints]

end SchemePoints

/-- The special-linear root subgroup followed by the determinant-kernel inclusion is the
general-linear root subgroup. -/
theorem rootSubgroup_comp_groupSchemeιGeneralLinear (hij : i ≠ j) :
    rootSubgroup hij ≫ groupSchemeιGeneralLinear R N =
      GeneralLinear.rootSubgroup hij := by
  rw [rootSubgroup, groupSchemeιGeneralLinear_def, groupSchemeι_def]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [
    CommHopfAlgCat.kernelSpecι_def, CommHopfAlgCat.quotientSpecι_def,
    GeneralLinear.rootSubgroup_def]
  rw [← Category.assoc
    ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
      (rootSubgroupCoordinateMap hij).op)
    ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (coordinateMap R N).op)
    (eqToHom (GeneralLinear.groupScheme_def R N).symm)]
  rw [← Functor.map_comp, ← op_comp, coordinateMap_comp_rootSubgroupCoordinateMap]

end Scheme

end SpecialLinear

end TauCeti
