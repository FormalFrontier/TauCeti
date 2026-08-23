/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The ambient root subgroups supply the coordinate maps through which the symplectic maps factor.
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.RootSubgroup
-- The symplectic scheme and its point equivalence identify the target of the root maps.
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Basic

/-!
# Long-root subgroups of the symplectic group

For `i : Fin m`, the elementary matrices

```text
x_{2eᵢ}(c)  = 1 + c E_{i,m+i},
x_{-2eᵢ}(c) = 1 + c E_{m+i,i}
```

preserve the standard alternating form. This file promotes these two one-parameter families to
affine group-scheme morphisms `𝔾ₐ → Sp₂ₘ` over an arbitrary commutative base ring. They
are the root subgroups belonging to the positive and negative long roots `±2eᵢ` of type `Cₘ`.

The construction first gives the natural homomorphisms on algebra-valued points using
`TauCeti.GLSymplecticFin.positiveLongRootTransvectionHom` and its negative analogue. Full
faithfulness of the functor of points recovers the two coordinate Hopf-algebra morphisms, and
relative spectrum gives the group-scheme maps. Their composites with the closed immersion
`Sp₂ₘ → GL₂ₘ` are proved to be the corresponding general-linear root subgroups. Thus the
factorization through the symplectic equations is recorded scheme-theoretically, over every base.

The short roots `±eᵢ ± eⱼ` require products of two commuting elementary matrices and are not
constructed here.

## Main definitions

* `TauCeti.Symplectic.positiveLongRootSubgroupPoints` and
  `TauCeti.Symplectic.negativeLongRootSubgroupPoints`: the homomorphisms on algebra-valued points.
* `TauCeti.Symplectic.positiveLongRootSubgroupCoordinateMap` and
  `TauCeti.Symplectic.negativeLongRootSubgroupCoordinateMap`: their coordinate morphisms.
* `TauCeti.Symplectic.positiveLongRootSubgroup` and
  `TauCeti.Symplectic.negativeLongRootSubgroup`: the affine group-scheme morphisms.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21 and §24.6.
* R. W. Carter, *Simple Groups of Lie Type* (1972), §11.3.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.Symplectic

universe u v w

variable {R : Type u} [CommRing R] {m : ℕ} {i : Fin m}

section Points

variable {A : Type w} [CommRing A] [Algebra R A]
variable {B : Type v} [CommRing B] [Algebra R B]

/-- The positive long-root homomorphism on `A`-points, sending `c` to
`1 + c E_{i,m+i}` in `Sp₂ₘ(A)`. -/
noncomputable def positiveLongRootSubgroupPoints (i : Fin m) :
    WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R m →ₐ[R] A) :=
  (pointsMulEquiv (R := R) (A := A) m).symm.toMonoidHom.comp
    ((GLSymplecticFin.positiveLongRootTransvectionHom i).comp
      (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).toMonoidHom)

/-- The negative long-root homomorphism on `A`-points, sending `c` to
`1 + c E_{m+i,i}` in `Sp₂ₘ(A)`. -/
noncomputable def negativeLongRootSubgroupPoints (i : Fin m) :
    WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R m →ₐ[R] A) :=
  (pointsMulEquiv (R := R) (A := A) m).symm.toMonoidHom.comp
    ((GLSymplecticFin.negativeLongRootTransvectionHom i).comp
      (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).toMonoidHom)

/-- Under the symplectic point equivalence, the positive long-root point is its elementary
transvection. -/
@[simp]
theorem pointsMulEquiv_positiveLongRootSubgroupPoints (i : Fin m)
    (f : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := A) m (positiveLongRootSubgroupPoints i f) =
      GLSymplecticFin.positiveLongRootTransvectionUnit i
        (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A) f)) := by
  rw [positiveLongRootSubgroupPoints]
  simp

/-- Under the symplectic point equivalence, the negative long-root point is its elementary
transvection. -/
@[simp]
theorem pointsMulEquiv_negativeLongRootSubgroupPoints (i : Fin m)
    (f : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := A) m (negativeLongRootSubgroupPoints i f) =
      GLSymplecticFin.negativeLongRootTransvectionUnit i
        (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A) f)) := by
  rw [negativeLongRootSubgroupPoints]
  simp

/-- The positive long-root subgroup is injective on algebra-valued points. -/
theorem positiveLongRootSubgroupPoints_injective (i : Fin m) :
    Function.Injective (positiveLongRootSubgroupPoints (R := R) (A := A) i) := by
  intro f g h
  have hSp := congrArg (pointsMulEquiv (R := R) (A := A) m) h
  rw [pointsMulEquiv_positiveLongRootSubgroupPoints,
    pointsMulEquiv_positiveLongRootSubgroupPoints] at hSp
  have hparam := GLSymplecticFin.positiveLongRootTransvectionUnit_injective i hSp
  apply (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).injective
  exact Multiplicative.toAdd.injective hparam

/-- The negative long-root subgroup is injective on algebra-valued points. -/
theorem negativeLongRootSubgroupPoints_injective (i : Fin m) :
    Function.Injective (negativeLongRootSubgroupPoints (R := R) (A := A) i) := by
  intro f g h
  have hSp := congrArg (pointsMulEquiv (R := R) (A := A) m) h
  rw [pointsMulEquiv_negativeLongRootSubgroupPoints,
    pointsMulEquiv_negativeLongRootSubgroupPoints] at hSp
  have hparam := GLSymplecticFin.negativeLongRootTransvectionUnit_injective i hSp
  apply (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).injective
  exact Multiplicative.toAdd.injective hparam

/-- The positive long-root subgroup on points is natural in the value algebra. -/
theorem mapValue_positiveLongRootSubgroupPoints (phi : A →ₐ[R] B) (i : Fin m)
    (f : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R m) phi
        (positiveLongRootSubgroupPoints i f) =
      positiveLongRootSubgroupPoints i
        (AlgHom.mapValue (H := AdditiveGroup.coordinateHopfAlgebra R) phi f) := by
  apply (pointsMulEquiv (R := R) (A := B) m).injective
  rw [pointsMulEquiv_mapValue, pointsMulEquiv_positiveLongRootSubgroupPoints,
    pointsMulEquiv_positiveLongRootSubgroupPoints,
    GLSymplecticFin.map_positiveLongRootTransvectionUnit,
    AdditiveGroup.toAdd_gaPointsMulEquiv_mapValue]
  rfl

/-- The negative long-root subgroup on points is natural in the value algebra. -/
theorem mapValue_negativeLongRootSubgroupPoints (phi : A →ₐ[R] B) (i : Fin m)
    (f : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R m) phi
        (negativeLongRootSubgroupPoints i f) =
      negativeLongRootSubgroupPoints i
        (AlgHom.mapValue (H := AdditiveGroup.coordinateHopfAlgebra R) phi f) := by
  apply (pointsMulEquiv (R := R) (A := B) m).injective
  rw [pointsMulEquiv_mapValue, pointsMulEquiv_negativeLongRootSubgroupPoints,
    pointsMulEquiv_negativeLongRootSubgroupPoints,
    GLSymplecticFin.map_negativeLongRootTransvectionUnit,
    AdditiveGroup.toAdd_gaPointsMulEquiv_mapValue]
  rfl

end Points

section Functor

/-- The natural transformation of group-valued points for the positive long root `2eᵢ`. -/
noncomputable def positiveLongRootSubgroupPointsMap (i : Fin m) :
    HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m) where
  app A := GrpCat.ofHom (positiveLongRootSubgroupPoints (A := A) i)
  naturality _ _ phi := by
    ext f
    exact (mapValue_positiveLongRootSubgroupPoints phi.hom i f).symm

/-- The natural transformation of group-valued points for the negative long root `-2eᵢ`. -/
noncomputable def negativeLongRootSubgroupPointsMap (i : Fin m) :
    HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m) where
  app A := GrpCat.ofHom (negativeLongRootSubgroupPoints (A := A) i)
  naturality _ _ phi := by
    ext f
    exact (mapValue_negativeLongRootSubgroupPoints phi.hom i f).symm

/-- A component of the positive long-root natural transformation is the corresponding point
homomorphism. -/
@[simp]
theorem positiveLongRootSubgroupPointsMap_app (i : Fin m) (A : CommAlgCat.{w} R) :
    (positiveLongRootSubgroupPointsMap (R := R) i).app A =
      GrpCat.ofHom (positiveLongRootSubgroupPoints i) := by
  unfold positiveLongRootSubgroupPointsMap
  rfl

/-- A component of the negative long-root natural transformation is the corresponding point
homomorphism. -/
@[simp]
theorem negativeLongRootSubgroupPointsMap_app (i : Fin m) (A : CommAlgCat.{w} R) :
    (negativeLongRootSubgroupPointsMap (R := R) i).app A =
      GrpCat.ofHom (negativeLongRootSubgroupPoints i) := by
  unfold negativeLongRootSubgroupPointsMap
  rfl

end Functor

section Scheme

/-- The coordinate morphism of the positive long-root subgroup, recovered from its natural
action on points. -/
noncomputable def positiveLongRootSubgroupCoordinateMap (i : Fin m) :
    coordinateHopfAlgebra R m ⟶ AdditiveGroup.coordinateHopfAlgebra R :=
  ((CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}).preimage
    (positiveLongRootSubgroupPointsMap.{u, u} (R := R) i)).unop

/-- The coordinate morphism of the negative long-root subgroup, recovered from its natural
action on points. -/
noncomputable def negativeLongRootSubgroupCoordinateMap (i : Fin m) :
    coordinateHopfAlgebra R m ⟶ AdditiveGroup.coordinateHopfAlgebra R :=
  ((CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}).preimage
    (negativeLongRootSubgroupPointsMap.{u, u} (R := R) i)).unop

/-- Precomposition by the positive long-root coordinate morphism gives its natural point map. -/
theorem mapPointsFunctor_positiveLongRootSubgroupCoordinateMap (i : Fin m) :
    (CommHopfAlgCat.mapPointsFunctor.{u, u, u}
      (positiveLongRootSubgroupCoordinateMap (R := R) i) :
      HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ⟶
        HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m)) =
      positiveLongRootSubgroupPointsMap.{u, u} i := by
  unfold positiveLongRootSubgroupCoordinateMap
  rw [← CommHopfAlgCat.pointsFunctor_map]
  exact Functor.map_preimage
    (CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}) _

/-- Precomposition by the negative long-root coordinate morphism gives its natural point map. -/
theorem mapPointsFunctor_negativeLongRootSubgroupCoordinateMap (i : Fin m) :
    (CommHopfAlgCat.mapPointsFunctor.{u, u, u}
      (negativeLongRootSubgroupCoordinateMap (R := R) i) :
      HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ⟶
        HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m)) =
      negativeLongRootSubgroupPointsMap.{u, u} i := by
  unfold negativeLongRootSubgroupCoordinateMap
  rw [← CommHopfAlgCat.pointsFunctor_map]
  exact Functor.map_preimage
    (CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}) _

/-- On a same-universe algebra, the positive coordinate morphism induces the constructed point
homomorphism. -/
@[simp]
theorem mapPointsFunctor_positiveLongRootSubgroupCoordinateMap_app (i : Fin m)
    (A : CommAlgCat.{u} R)
    (f : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A) :
    (CommHopfAlgCat.mapPointsFunctor
      (positiveLongRootSubgroupCoordinateMap (R := R) i)).app A f =
      positiveLongRootSubgroupPoints i f := by
  rw [mapPointsFunctor_positiveLongRootSubgroupCoordinateMap,
    positiveLongRootSubgroupPointsMap_app]
  rfl

/-- On a same-universe algebra, the negative coordinate morphism induces the constructed point
homomorphism. -/
@[simp]
theorem mapPointsFunctor_negativeLongRootSubgroupCoordinateMap_app (i : Fin m)
    (A : CommAlgCat.{u} R)
    (f : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A) :
    (CommHopfAlgCat.mapPointsFunctor
      (negativeLongRootSubgroupCoordinateMap (R := R) i)).app A f =
      negativeLongRootSubgroupPoints i f := by
  rw [mapPointsFunctor_negativeLongRootSubgroupCoordinateMap,
    negativeLongRootSubgroupPointsMap_app]
  rfl

/-- The positive long-root coordinate morphism factors the matching general-linear root
coordinate morphism through the symplectic quotient. -/
@[simp]
theorem coordinateMap_comp_positiveLongRootSubgroupCoordinateMap (i : Fin m) :
    coordinateMap R m ≫ positiveLongRootSubgroupCoordinateMap i =
      GeneralLinear.rootSubgroupCoordinateMap
        (GLSymplecticFin.positiveLongRoot_indices_ne i) := by
  apply Quiver.Hom.op_inj
  apply (CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R)).map_injective
  rw [op_comp, Functor.map_comp, CommHopfAlgCat.pointsFunctor_map,
    CommHopfAlgCat.pointsFunctor_map, CommHopfAlgCat.pointsFunctor_map]
  -- Mapping an opposite composite reverses it; `change` only removes the functor and
  -- opposite-category wrappers left by the preceding public rewrite lemmas.
  change CommHopfAlgCat.mapPointsFunctor
      (positiveLongRootSubgroupCoordinateMap (R := R) i) ≫
        CommHopfAlgCat.mapPointsFunctor (coordinateMap R m) =
    CommHopfAlgCat.mapPointsFunctor
      (GeneralLinear.rootSubgroupCoordinateMap (R := R)
        (GLSymplecticFin.positiveLongRoot_indices_ne i))
  rw [mapPointsFunctor_positiveLongRootSubgroupCoordinateMap,
    GeneralLinear.mapPointsFunctor_rootSubgroupCoordinateMap]
  ext A f
  rw [NatTrans.comp_app, positiveLongRootSubgroupPointsMap_app,
    GeneralLinear.rootSubgroupPointsMap_app]
  -- The component morphisms are `GrpCat.ofHom` wrappers, whose coercions to functions are
  -- definitionally the displayed point homomorphisms; no separate coercion lemma is provided.
  change (CommHopfAlgCat.mapPointsFunctor (coordinateMap R m)).app A
      (positiveLongRootSubgroupPoints i f) =
    GeneralLinear.rootSubgroupPoints (GLSymplecticFin.positiveLongRoot_indices_ne i) f
  rw [mapPointsFunctor_coordinateMap_app]
  apply (GeneralLinear.pointsMulEquiv (R := R) (A := A) (m + m)).injective
  rw [pointsMulEquiv_coe]
  have hSp := pointsMulEquiv_positiveLongRootSubgroupPoints
    (R := R) (A := A) i f
  have hGL := GeneralLinear.pointsMulEquiv_rootSubgroupPoints
    (R := R) (A := A) (GLSymplecticFin.positiveLongRoot_indices_ne i) f
  rw [hSp, hGL, GLSymplecticFin.coe_positiveLongRootTransvectionUnit]

/-- The negative long-root coordinate morphism factors the matching general-linear root
coordinate morphism through the symplectic quotient. -/
@[simp]
theorem coordinateMap_comp_negativeLongRootSubgroupCoordinateMap (i : Fin m) :
    coordinateMap R m ≫ negativeLongRootSubgroupCoordinateMap i =
      GeneralLinear.rootSubgroupCoordinateMap
        (GLSymplecticFin.negativeLongRoot_indices_ne i) := by
  apply Quiver.Hom.op_inj
  apply (CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R)).map_injective
  rw [op_comp, Functor.map_comp, CommHopfAlgCat.pointsFunctor_map,
    CommHopfAlgCat.pointsFunctor_map, CommHopfAlgCat.pointsFunctor_map]
  -- Mapping an opposite composite reverses it; `change` only removes the functor and
  -- opposite-category wrappers left by the preceding public rewrite lemmas.
  change CommHopfAlgCat.mapPointsFunctor
      (negativeLongRootSubgroupCoordinateMap (R := R) i) ≫
        CommHopfAlgCat.mapPointsFunctor (coordinateMap R m) =
    CommHopfAlgCat.mapPointsFunctor
      (GeneralLinear.rootSubgroupCoordinateMap (R := R)
        (GLSymplecticFin.negativeLongRoot_indices_ne i))
  rw [mapPointsFunctor_negativeLongRootSubgroupCoordinateMap,
    GeneralLinear.mapPointsFunctor_rootSubgroupCoordinateMap]
  ext A f
  rw [NatTrans.comp_app, negativeLongRootSubgroupPointsMap_app,
    GeneralLinear.rootSubgroupPointsMap_app]
  -- The component morphisms are `GrpCat.ofHom` wrappers, whose coercions to functions are
  -- definitionally the displayed point homomorphisms; no separate coercion lemma is provided.
  change (CommHopfAlgCat.mapPointsFunctor (coordinateMap R m)).app A
      (negativeLongRootSubgroupPoints i f) =
    GeneralLinear.rootSubgroupPoints (GLSymplecticFin.negativeLongRoot_indices_ne i) f
  rw [mapPointsFunctor_coordinateMap_app]
  apply (GeneralLinear.pointsMulEquiv (R := R) (A := A) (m + m)).injective
  rw [pointsMulEquiv_coe]
  have hSp := pointsMulEquiv_negativeLongRootSubgroupPoints
    (R := R) (A := A) i f
  have hGL := GeneralLinear.pointsMulEquiv_rootSubgroupPoints
    (R := R) (A := A) (GLSymplecticFin.negativeLongRoot_indices_ne i) f
  rw [hSp, hGL, GLSymplecticFin.coe_negativeLongRootTransvectionUnit]

/-- **The positive long-root subgroup of `Sp₂ₘ` attached to `2eᵢ`**, as an affine
group-scheme morphism. -/
noncomputable def positiveLongRootSubgroup (i : Fin m) :
    AdditiveGroup.groupScheme R ⟶ groupScheme R m :=
  eqToHom (AdditiveGroup.groupScheme_def R) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
      (positiveLongRootSubgroupCoordinateMap i).op ≫
    eqToHom (groupScheme_def R m).symm

/-- The positive long-root subgroup is the relative spectrum of its coordinate morphism,
transported to the named source and target schemes. -/
theorem positiveLongRootSubgroup_def (i : Fin m) :
    positiveLongRootSubgroup (R := R) i =
      eqToHom (AdditiveGroup.groupScheme_def R) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (positiveLongRootSubgroupCoordinateMap i).op ≫
        eqToHom (groupScheme_def R m).symm := by
  unfold positiveLongRootSubgroup
  rfl

/-- **The negative long-root subgroup of `Sp₂ₘ` attached to `-2eᵢ`**, as an affine
group-scheme morphism. -/
noncomputable def negativeLongRootSubgroup (i : Fin m) :
    AdditiveGroup.groupScheme R ⟶ groupScheme R m :=
  eqToHom (AdditiveGroup.groupScheme_def R) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
      (negativeLongRootSubgroupCoordinateMap i).op ≫
    eqToHom (groupScheme_def R m).symm

/-- The negative long-root subgroup is the relative spectrum of its coordinate morphism,
transported to the named source and target schemes. -/
theorem negativeLongRootSubgroup_def (i : Fin m) :
    negativeLongRootSubgroup (R := R) i =
      eqToHom (AdditiveGroup.groupScheme_def R) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (negativeLongRootSubgroupCoordinateMap i).op ≫
        eqToHom (groupScheme_def R m).symm := by
  unfold negativeLongRootSubgroup
  rfl

/-- The positive long-root subgroup followed by the symplectic inclusion is the corresponding
general-linear root subgroup. -/
@[simp]
theorem positiveLongRootSubgroup_comp_inclusion (i : Fin m) :
    positiveLongRootSubgroup (R := R) i ≫ inclusion R m =
      GeneralLinear.rootSubgroup (R := R)
        (GLSymplecticFin.positiveLongRoot_indices_ne i) := by
  rw [positiveLongRootSubgroup_def, inclusion_def, GeneralLinear.rootSubgroup_def]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [CommHopfAlgCat.quotientSpecι_def]
  rw [← coordinateMap_def]
  rw [← Category.assoc
    ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
      (positiveLongRootSubgroupCoordinateMap i).op)
    ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (coordinateMap R m).op)
    ((eqToIso (GeneralLinear.groupScheme_def R (m + m)).symm).hom)]
  rw [← Functor.map_comp, ← op_comp, coordinateMap_comp_positiveLongRootSubgroupCoordinateMap]
  simp only [eqToIso.hom]

/-- The negative long-root subgroup followed by the symplectic inclusion is the corresponding
general-linear root subgroup. -/
@[simp]
theorem negativeLongRootSubgroup_comp_inclusion (i : Fin m) :
    negativeLongRootSubgroup (R := R) i ≫ inclusion R m =
      GeneralLinear.rootSubgroup (R := R)
        (GLSymplecticFin.negativeLongRoot_indices_ne i) := by
  rw [negativeLongRootSubgroup_def, inclusion_def, GeneralLinear.rootSubgroup_def]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [CommHopfAlgCat.quotientSpecι_def]
  rw [← coordinateMap_def]
  rw [← Category.assoc
    ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
      (negativeLongRootSubgroupCoordinateMap i).op)
    ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (coordinateMap R m).op)
    ((eqToIso (GeneralLinear.groupScheme_def R (m + m)).symm).hom)]
  rw [← Functor.map_comp, ← op_comp, coordinateMap_comp_negativeLongRootSubgroupCoordinateMap]
  simp only [eqToIso.hom]

end Scheme

end TauCeti.Symplectic
