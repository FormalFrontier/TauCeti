/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The ambient root subgroups supply the coordinate maps through which the symplectic maps factor.
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Subgroup
-- The symplectic scheme and its point equivalence identify the target of the root maps.
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Basic

/-!
# Root subgroups of the symplectic group

For `i : Fin m`, the elementary matrices

```text
x_{2eᵢ}(c)  = 1 + c E_{i,m+i},
x_{-2eᵢ}(c) = 1 + c E_{m+i,i}
```

preserve the standard alternating form. For distinct `i,j`, products of two commuting elementary
matrices similarly give the short roots `eᵢ-eⱼ`, `eᵢ+eⱼ`, and `-eᵢ-eⱼ`. This file promotes all
five families to affine group-scheme morphisms `𝔾ₐ → Sp₂ₘ` over an arbitrary commutative base
ring.

The construction first selects the matrix homomorphism through
`TauCeti.GLSymplecticFin.RootSubgroupIndex`. One shared pipeline constructs its natural map on
algebra-valued points, recovers the coordinate Hopf-algebra morphism by full faithfulness of the
functor of points, and applies relative spectrum. The long-root composites with the closed immersion
`Sp₂ₘ → GL₂ₘ` are proved to be the corresponding general-linear root subgroups. Thus the
factorization through the symplectic equations is recorded scheme-theoretically, over every base.

## Main definitions

* `TauCeti.Symplectic.positiveLongRootSubgroupPoints` and
  `TauCeti.Symplectic.negativeLongRootSubgroupPoints`: the homomorphisms on algebra-valued points.
* `TauCeti.Symplectic.positiveLongRootSubgroupCoordinateMap` and
  `TauCeti.Symplectic.negativeLongRootSubgroupCoordinateMap`: their coordinate morphisms.
* `TauCeti.Symplectic.positiveLongRootSubgroup` and
  `TauCeti.Symplectic.negativeLongRootSubgroup`: the affine group-scheme morphisms.
* `TauCeti.Symplectic.shortRootSubgroup`: the affine group-scheme morphism for any short root.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21 and §24.6.
* R. W. Carter, *Simple Groups of Lie Type* (1972), §11.3.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.Symplectic

universe u v w

variable {R : Type u} [CommRing R] {m : ℕ} {i j : Fin m}

section Points

variable {A : Type w} [CommRing A] [Algebra R A]
variable {B : Type v} [CommRing B] [Algebra R B]

/-- The homomorphism on `A`-valued points selected by a symplectic root index. -/
noncomputable def rootSubgroupPoints (root : GLSymplecticFin.RootSubgroupIndex m) :
    WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R m →ₐ[R] A) :=
  (pointsMulEquiv (R := R) (A := A) m).symm.toMonoidHom.comp
    (root.hom.comp (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).toMonoidHom)

/-- Under the symplectic point equivalence, a root point is the selected matrix homomorphism. -/
@[simp]
theorem pointsMulEquiv_rootSubgroupPoints (root : GLSymplecticFin.RootSubgroupIndex m)
    (q : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := A) m (rootSubgroupPoints root q) =
      root.hom (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A) q) := by
  rw [rootSubgroupPoints]
  simp

/-- Every symplectic root subgroup is injective on algebra-valued points. -/
theorem rootSubgroupPoints_injective (root : GLSymplecticFin.RootSubgroupIndex m) :
    Function.Injective (rootSubgroupPoints (R := R) (A := A) root) :=
  (pointsMulEquiv (R := R) (A := A) m).symm.injective.comp <|
    root.hom_injective.comp
      (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).injective

/-- Symplectic root point homomorphisms are natural in the value algebra. -/
theorem mapValue_rootSubgroupPoints (root : GLSymplecticFin.RootSubgroupIndex m)
    (φ : A →ₐ[R] B) (q : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R m) φ (rootSubgroupPoints root q) =
      rootSubgroupPoints root
        (AlgHom.mapValue (H := AdditiveGroup.coordinateHopfAlgebra R) φ q) := by
  apply (pointsMulEquiv (R := R) (A := B) m).injective
  rw [pointsMulEquiv_mapValue, pointsMulEquiv_rootSubgroupPoints,
    pointsMulEquiv_rootSubgroupPoints, GLSymplecticFin.RootSubgroupIndex.map_hom_apply]
  apply congrArg root.hom
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd, AdditiveGroup.toAdd_gaPointsMulEquiv_mapValue]
  rfl

/-- The positive long-root homomorphism on `A`-points, sending `c` to
`1 + c E_{i,m+i}` in `Sp₂ₘ(A)`. -/
noncomputable def positiveLongRootSubgroupPoints (i : Fin m) :
    WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R m →ₐ[R] A) :=
  rootSubgroupPoints (.positiveLong i)

/-- The negative long-root homomorphism on `A`-points, sending `c` to
`1 + c E_{m+i,i}` in `Sp₂ₘ(A)`. -/
noncomputable def negativeLongRootSubgroupPoints (i : Fin m) :
    WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R m →ₐ[R] A) :=
  rootSubgroupPoints (.negativeLong i)

/-- The short-root homomorphism on algebra-valued points. -/
noncomputable def shortRootSubgroupPoints (family : GLSymplecticFin.ShortRootFamily)
    (hij : i ≠ j) :
    WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R m →ₐ[R] A) :=
  rootSubgroupPoints (.short family i j hij)

/-- Under the symplectic point equivalence, the positive long-root point is its elementary
transvection. -/
@[simp]
theorem pointsMulEquiv_positiveLongRootSubgroupPoints (i : Fin m)
    (f : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := A) m (positiveLongRootSubgroupPoints i f) =
      GLSymplecticFin.positiveLongRootTransvectionUnit i
        (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A) f)) := by
  rw [positiveLongRootSubgroupPoints, pointsMulEquiv_rootSubgroupPoints]
  rw [GLSymplecticFin.RootSubgroupIndex.hom_positiveLong,
    GLSymplecticFin.positiveLongRootTransvectionHom_apply]

/-- Under the symplectic point equivalence, the negative long-root point is its elementary
transvection. -/
@[simp]
theorem pointsMulEquiv_negativeLongRootSubgroupPoints (i : Fin m)
    (f : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := A) m (negativeLongRootSubgroupPoints i f) =
      GLSymplecticFin.negativeLongRootTransvectionUnit i
        (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A) f)) := by
  rw [negativeLongRootSubgroupPoints, pointsMulEquiv_rootSubgroupPoints]
  rw [GLSymplecticFin.RootSubgroupIndex.hom_negativeLong,
    GLSymplecticFin.negativeLongRootTransvectionHom_apply]

/-- Under the symplectic point equivalence, a short-root point is its paired elementary-matrix
one-parameter subgroup. -/
@[simp]
theorem pointsMulEquiv_shortRootSubgroupPoints
    (family : GLSymplecticFin.ShortRootFamily) (hij : i ≠ j)
    (q : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := A) m (shortRootSubgroupPoints family hij q) =
      family.hom hij (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A) q) := by
  rw [shortRootSubgroupPoints, pointsMulEquiv_rootSubgroupPoints]
  rw [GLSymplecticFin.RootSubgroupIndex.hom_short]

/-- The positive long-root subgroup is injective on algebra-valued points. -/
theorem positiveLongRootSubgroupPoints_injective (i : Fin m) :
    Function.Injective (positiveLongRootSubgroupPoints (R := R) (A := A) i) :=
  rootSubgroupPoints_injective (.positiveLong i)

/-- The negative long-root subgroup is injective on algebra-valued points. -/
theorem negativeLongRootSubgroupPoints_injective (i : Fin m) :
    Function.Injective (negativeLongRootSubgroupPoints (R := R) (A := A) i) :=
  rootSubgroupPoints_injective (.negativeLong i)

/-- A short-root subgroup is injective on points over every value algebra. -/
theorem shortRootSubgroupPoints_injective (family : GLSymplecticFin.ShortRootFamily)
    (hij : i ≠ j) :
    Function.Injective (shortRootSubgroupPoints (R := R) (A := A) family hij) :=
  rootSubgroupPoints_injective (.short family i j hij)

/-- The positive long-root subgroup on points is natural in the value algebra. -/
theorem mapValue_positiveLongRootSubgroupPoints (phi : A →ₐ[R] B) (i : Fin m)
    (f : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R m) phi
        (positiveLongRootSubgroupPoints i f) =
      positiveLongRootSubgroupPoints i
        (AlgHom.mapValue (H := AdditiveGroup.coordinateHopfAlgebra R) phi f) :=
  mapValue_rootSubgroupPoints (.positiveLong i) phi f

/-- The negative long-root subgroup on points is natural in the value algebra. -/
theorem mapValue_negativeLongRootSubgroupPoints (phi : A →ₐ[R] B) (i : Fin m)
    (f : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R m) phi
        (negativeLongRootSubgroupPoints i f) =
      negativeLongRootSubgroupPoints i
        (AlgHom.mapValue (H := AdditiveGroup.coordinateHopfAlgebra R) phi f) :=
  mapValue_rootSubgroupPoints (.negativeLong i) phi f

/-- Short-root point homomorphisms are natural in the value algebra. -/
theorem mapValue_shortRootSubgroupPoints (family : GLSymplecticFin.ShortRootFamily)
    (φ : A →ₐ[R] B) (hij : i ≠ j)
    (q : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R m) φ (shortRootSubgroupPoints family hij q) =
      shortRootSubgroupPoints family hij
        (AlgHom.mapValue (H := AdditiveGroup.coordinateHopfAlgebra R) φ q) :=
  mapValue_rootSubgroupPoints (.short family i j hij) φ q

end Points

section Functor

/-- The natural transformation of group-valued points selected by a symplectic root index. -/
noncomputable def rootSubgroupPointsMap (root : GLSymplecticFin.RootSubgroupIndex m) :
    HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m) where
  app A := GrpCat.ofHom (rootSubgroupPoints (A := A) root)
  naturality _ _ φ := by
    ext q
    exact (mapValue_rootSubgroupPoints root φ.hom q).symm

/-- The natural transformation of group-valued points for the positive long root `2eᵢ`. -/
noncomputable def positiveLongRootSubgroupPointsMap (i : Fin m) :
    HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m) :=
  rootSubgroupPointsMap (.positiveLong i)

/-- The natural transformation of group-valued points for the negative long root `-2eᵢ`. -/
noncomputable def negativeLongRootSubgroupPointsMap (i : Fin m) :
    HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m) :=
  rootSubgroupPointsMap (.negativeLong i)

/-- The natural transformation of group-valued points attached to a short root. -/
noncomputable def shortRootSubgroupPointsMap (family : GLSymplecticFin.ShortRootFamily)
    (hij : i ≠ j) :
    HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m) :=
  rootSubgroupPointsMap (.short family i j hij)

/-- A component of the generic root points map is the constructed point homomorphism. -/
@[simp]
theorem rootSubgroupPointsMap_app (root : GLSymplecticFin.RootSubgroupIndex m)
    (A : CommAlgCat.{w} R) :
    (rootSubgroupPointsMap (R := R) root).app A =
      GrpCat.ofHom (rootSubgroupPoints root) := by
  unfold rootSubgroupPointsMap
  rfl

/-- A component of the positive long-root natural transformation is the corresponding point
homomorphism. -/
@[simp]
theorem positiveLongRootSubgroupPointsMap_app (i : Fin m) (A : CommAlgCat.{w} R) :
    (positiveLongRootSubgroupPointsMap (R := R) i).app A =
      GrpCat.ofHom (positiveLongRootSubgroupPoints i) := by
  rw [positiveLongRootSubgroupPointsMap, positiveLongRootSubgroupPoints,
    rootSubgroupPointsMap_app]

/-- A component of the negative long-root natural transformation is the corresponding point
homomorphism. -/
@[simp]
theorem negativeLongRootSubgroupPointsMap_app (i : Fin m) (A : CommAlgCat.{w} R) :
    (negativeLongRootSubgroupPointsMap (R := R) i).app A =
      GrpCat.ofHom (negativeLongRootSubgroupPoints i) := by
  rw [negativeLongRootSubgroupPointsMap, negativeLongRootSubgroupPoints,
    rootSubgroupPointsMap_app]

/-- A component of the natural short-root points map is the constructed point homomorphism. -/
@[simp]
theorem shortRootSubgroupPointsMap_app (family : GLSymplecticFin.ShortRootFamily)
    (hij : i ≠ j) (A : CommAlgCat.{w} R) :
    (shortRootSubgroupPointsMap (R := R) family hij).app A =
      GrpCat.ofHom (shortRootSubgroupPoints family hij) := by
  rw [shortRootSubgroupPointsMap, shortRootSubgroupPoints, rootSubgroupPointsMap_app]

end Functor

section Scheme

/-- The coordinate Hopf-algebra morphism selected by a symplectic root index. -/
noncomputable def rootSubgroupCoordinateMap (root : GLSymplecticFin.RootSubgroupIndex m) :
    coordinateHopfAlgebra R m ⟶ AdditiveGroup.coordinateHopfAlgebra R :=
  CommHopfAlgCat.homOfPointsMap (rootSubgroupPointsMap.{u, u} (R := R) root)

/-- The coordinate morphism of the positive long-root subgroup, recovered from its natural
action on points. -/
noncomputable def positiveLongRootSubgroupCoordinateMap (i : Fin m) :
    coordinateHopfAlgebra R m ⟶ AdditiveGroup.coordinateHopfAlgebra R :=
  rootSubgroupCoordinateMap (.positiveLong i)

/-- The coordinate morphism of the negative long-root subgroup, recovered from its natural
action on points. -/
noncomputable def negativeLongRootSubgroupCoordinateMap (i : Fin m) :
    coordinateHopfAlgebra R m ⟶ AdditiveGroup.coordinateHopfAlgebra R :=
  rootSubgroupCoordinateMap (.negativeLong i)

/-- The coordinate Hopf-algebra morphism of a short-root subgroup. -/
noncomputable def shortRootSubgroupCoordinateMap (family : GLSymplecticFin.ShortRootFamily)
    (hij : i ≠ j) : coordinateHopfAlgebra R m ⟶ AdditiveGroup.coordinateHopfAlgebra R :=
  rootSubgroupCoordinateMap (.short family i j hij)

/-- Precomposition by a root coordinate morphism is its natural map on points. -/
theorem mapPointsFunctor_rootSubgroupCoordinateMap
    (root : GLSymplecticFin.RootSubgroupIndex m) :
    (CommHopfAlgCat.mapPointsFunctor.{u, u, u}
      (rootSubgroupCoordinateMap (R := R) root) :
      HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ⟶
        HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m)) =
      rootSubgroupPointsMap.{u, u} root :=
  CommHopfAlgCat.mapPointsFunctor_homOfPointsMap _

/-- Precomposition by the positive long-root coordinate morphism gives its natural point map. -/
theorem mapPointsFunctor_positiveLongRootSubgroupCoordinateMap (i : Fin m) :
    (CommHopfAlgCat.mapPointsFunctor.{u, u, u}
      (positiveLongRootSubgroupCoordinateMap (R := R) i) :
      HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ⟶
        HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m)) =
      positiveLongRootSubgroupPointsMap.{u, u} i := by
  rw [positiveLongRootSubgroupCoordinateMap, positiveLongRootSubgroupPointsMap,
    mapPointsFunctor_rootSubgroupCoordinateMap]

/-- Precomposition by the negative long-root coordinate morphism gives its natural point map. -/
theorem mapPointsFunctor_negativeLongRootSubgroupCoordinateMap (i : Fin m) :
    (CommHopfAlgCat.mapPointsFunctor.{u, u, u}
      (negativeLongRootSubgroupCoordinateMap (R := R) i) :
      HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ⟶
        HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m)) =
      negativeLongRootSubgroupPointsMap.{u, u} i := by
  rw [negativeLongRootSubgroupCoordinateMap, negativeLongRootSubgroupPointsMap,
    mapPointsFunctor_rootSubgroupCoordinateMap]

/-- Precomposition by the short-root coordinate morphism is its natural map on points. -/
theorem mapPointsFunctor_shortRootSubgroupCoordinateMap
    (family : GLSymplecticFin.ShortRootFamily) (hij : i ≠ j) :
    (CommHopfAlgCat.mapPointsFunctor.{u, u, u}
      (shortRootSubgroupCoordinateMap (R := R) family hij) :
      HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ⟶
        HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m)) =
      shortRootSubgroupPointsMap.{u, u} family hij := by
  rw [shortRootSubgroupCoordinateMap, shortRootSubgroupPointsMap,
    mapPointsFunctor_rootSubgroupCoordinateMap]

/-- On a same-universe algebra, a root coordinate morphism induces the constructed point map. -/
@[simp]
theorem mapPointsFunctor_rootSubgroupCoordinateMap_app
    (root : GLSymplecticFin.RootSubgroupIndex m) (A : CommAlgCat.{u} R)
    (q : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A) :
    (CommHopfAlgCat.mapPointsFunctor
      (rootSubgroupCoordinateMap (R := R) root)).app A q = rootSubgroupPoints root q := by
  rw [mapPointsFunctor_rootSubgroupCoordinateMap, rootSubgroupPointsMap_app]
  rfl

/-- On a same-universe algebra, the positive coordinate morphism induces the constructed point
homomorphism. -/
@[simp]
theorem mapPointsFunctor_positiveLongRootSubgroupCoordinateMap_app (i : Fin m)
    (A : CommAlgCat.{u} R)
    (f : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A) :
    (CommHopfAlgCat.mapPointsFunctor
      (positiveLongRootSubgroupCoordinateMap (R := R) i)).app A f =
      positiveLongRootSubgroupPoints i f := by
  rw [positiveLongRootSubgroupCoordinateMap, positiveLongRootSubgroupPoints,
    mapPointsFunctor_rootSubgroupCoordinateMap_app]

/-- On a same-universe algebra, the negative coordinate morphism induces the constructed point
homomorphism. -/
@[simp]
theorem mapPointsFunctor_negativeLongRootSubgroupCoordinateMap_app (i : Fin m)
    (A : CommAlgCat.{u} R)
    (f : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A) :
    (CommHopfAlgCat.mapPointsFunctor
      (negativeLongRootSubgroupCoordinateMap (R := R) i)).app A f =
      negativeLongRootSubgroupPoints i f := by
  rw [negativeLongRootSubgroupCoordinateMap, negativeLongRootSubgroupPoints,
    mapPointsFunctor_rootSubgroupCoordinateMap_app]

/-- On a same-universe algebra, a short-root coordinate morphism induces its point homomorphism. -/
@[simp]
theorem mapPointsFunctor_shortRootSubgroupCoordinateMap_app
    (family : GLSymplecticFin.ShortRootFamily) (hij : i ≠ j) (A : CommAlgCat.{u} R)
    (q : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A) :
    (CommHopfAlgCat.mapPointsFunctor
      (shortRootSubgroupCoordinateMap (R := R) family hij)).app A q =
      shortRootSubgroupPoints family hij q := by
  rw [shortRootSubgroupCoordinateMap, shortRootSubgroupPoints,
    mapPointsFunctor_rootSubgroupCoordinateMap_app]

/-- The positive long-root coordinate morphism factors the matching general-linear root
coordinate morphism through the symplectic quotient. -/
@[simp]
theorem coordinateMap_comp_positiveLongRootSubgroupCoordinateMap (i : Fin m) :
    coordinateMap R m ≫ positiveLongRootSubgroupCoordinateMap i =
      GeneralLinear.rootSubgroupCoordinateMap
        (GLSymplecticFin.finSumFinEquiv_inl_ne_inr i i) := by
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
        (GLSymplecticFin.finSumFinEquiv_inl_ne_inr i i))
  rw [mapPointsFunctor_positiveLongRootSubgroupCoordinateMap,
    GeneralLinear.mapPointsFunctor_rootSubgroupCoordinateMap]
  ext A f
  rw [NatTrans.comp_app, positiveLongRootSubgroupPointsMap_app,
    GeneralLinear.rootSubgroupPointsMap_app]
  -- The component morphisms are `GrpCat.ofHom` wrappers, whose coercions to functions are
  -- definitionally the displayed point homomorphisms; no separate coercion lemma is provided.
  change (CommHopfAlgCat.mapPointsFunctor (coordinateMap R m)).app A
      (positiveLongRootSubgroupPoints i f) =
    GeneralLinear.rootSubgroupPoints (GLSymplecticFin.finSumFinEquiv_inl_ne_inr i i) f
  rw [ConstantForm.mapPointsFunctor_coordinateMap_app]
  apply (GeneralLinear.pointsMulEquiv (R := R) (A := A) (m + m)).injective
  rw [pointsMulEquiv_coe]
  have hSp := pointsMulEquiv_positiveLongRootSubgroupPoints
    (R := R) (A := A) i f
  have hGL := GeneralLinear.pointsMulEquiv_rootSubgroupPoints
    (R := R) (A := A) (GLSymplecticFin.finSumFinEquiv_inl_ne_inr i i) f
  rw [hSp, hGL, GLSymplecticFin.coe_positiveLongRootTransvectionUnit]

/-- The negative long-root coordinate morphism factors the matching general-linear root
coordinate morphism through the symplectic quotient. -/
@[simp]
theorem coordinateMap_comp_negativeLongRootSubgroupCoordinateMap (i : Fin m) :
    coordinateMap R m ≫ negativeLongRootSubgroupCoordinateMap i =
      GeneralLinear.rootSubgroupCoordinateMap
        (GLSymplecticFin.finSumFinEquiv_inr_ne_inl i i) := by
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
        (GLSymplecticFin.finSumFinEquiv_inr_ne_inl i i))
  rw [mapPointsFunctor_negativeLongRootSubgroupCoordinateMap,
    GeneralLinear.mapPointsFunctor_rootSubgroupCoordinateMap]
  ext A f
  rw [NatTrans.comp_app, negativeLongRootSubgroupPointsMap_app,
    GeneralLinear.rootSubgroupPointsMap_app]
  -- The component morphisms are `GrpCat.ofHom` wrappers, whose coercions to functions are
  -- definitionally the displayed point homomorphisms; no separate coercion lemma is provided.
  change (CommHopfAlgCat.mapPointsFunctor (coordinateMap R m)).app A
      (negativeLongRootSubgroupPoints i f) =
    GeneralLinear.rootSubgroupPoints (GLSymplecticFin.finSumFinEquiv_inr_ne_inl i i) f
  rw [ConstantForm.mapPointsFunctor_coordinateMap_app]
  apply (GeneralLinear.pointsMulEquiv (R := R) (A := A) (m + m)).injective
  rw [pointsMulEquiv_coe]
  have hSp := pointsMulEquiv_negativeLongRootSubgroupPoints
    (R := R) (A := A) i f
  have hGL := GeneralLinear.pointsMulEquiv_rootSubgroupPoints
    (R := R) (A := A) (GLSymplecticFin.finSumFinEquiv_inr_ne_inl i i) f
  rw [hSp, hGL, GLSymplecticFin.coe_negativeLongRootTransvectionUnit]

/-- The affine group-scheme morphism selected by a symplectic root index. -/
noncomputable def rootSubgroup (root : GLSymplecticFin.RootSubgroupIndex m) :
    AdditiveGroup.groupScheme R ⟶ groupScheme R m :=
  eqToHom (AdditiveGroup.groupScheme_def R) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
      (rootSubgroupCoordinateMap root).op ≫
    eqToHom (groupScheme_def R m).symm

/-- A root subgroup is relative spectrum applied to its coordinate morphism. -/
theorem rootSubgroup_def (root : GLSymplecticFin.RootSubgroupIndex m) :
    rootSubgroup (R := R) root =
      eqToHom (AdditiveGroup.groupScheme_def R) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (rootSubgroupCoordinateMap root).op ≫
        eqToHom (groupScheme_def R m).symm := by
  unfold rootSubgroup
  rfl

/-- **The positive long-root subgroup of `Sp₂ₘ` attached to `2eᵢ`**, as an affine
group-scheme morphism. -/
noncomputable def positiveLongRootSubgroup (i : Fin m) :
    AdditiveGroup.groupScheme R ⟶ groupScheme R m :=
  rootSubgroup (.positiveLong i)

/-- The positive long-root subgroup is the relative spectrum of its coordinate morphism,
transported to the named source and target schemes. -/
theorem positiveLongRootSubgroup_def (i : Fin m) :
    positiveLongRootSubgroup (R := R) i =
      eqToHom (AdditiveGroup.groupScheme_def R) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (positiveLongRootSubgroupCoordinateMap i).op ≫
        eqToHom (groupScheme_def R m).symm := by
  rw [positiveLongRootSubgroup, positiveLongRootSubgroupCoordinateMap, rootSubgroup_def]

/-- **The negative long-root subgroup of `Sp₂ₘ` attached to `-2eᵢ`**, as an affine
group-scheme morphism. -/
noncomputable def negativeLongRootSubgroup (i : Fin m) :
    AdditiveGroup.groupScheme R ⟶ groupScheme R m :=
  rootSubgroup (.negativeLong i)

/-- The negative long-root subgroup is the relative spectrum of its coordinate morphism,
transported to the named source and target schemes. -/
theorem negativeLongRootSubgroup_def (i : Fin m) :
    negativeLongRootSubgroup (R := R) i =
      eqToHom (AdditiveGroup.groupScheme_def R) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (negativeLongRootSubgroupCoordinateMap i).op ≫
        eqToHom (groupScheme_def R m).symm := by
  rw [negativeLongRootSubgroup, negativeLongRootSubgroupCoordinateMap, rootSubgroup_def]

/-- The affine group-scheme morphism `𝔾ₐ → Sp₂ₘ` attached to a short root. -/
noncomputable def shortRootSubgroup (family : GLSymplecticFin.ShortRootFamily) (hij : i ≠ j) :
    AdditiveGroup.groupScheme R ⟶ groupScheme R m :=
  rootSubgroup (.short family i j hij)

/-- The short-root subgroup is relative spectrum applied to its coordinate morphism. -/
theorem shortRootSubgroup_def (family : GLSymplecticFin.ShortRootFamily) (hij : i ≠ j) :
    shortRootSubgroup (R := R) family hij =
      eqToHom (AdditiveGroup.groupScheme_def R) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (shortRootSubgroupCoordinateMap family hij).op ≫
        eqToHom (groupScheme_def R m).symm := by
  rw [shortRootSubgroup, shortRootSubgroupCoordinateMap, rootSubgroup_def]

/-- The positive long-root subgroup followed by the symplectic inclusion is the corresponding
general-linear root subgroup. -/
@[simp]
theorem positiveLongRootSubgroup_comp_inclusion (i : Fin m) :
    positiveLongRootSubgroup (R := R) i ≫ inclusion R m =
      GeneralLinear.rootSubgroup (R := R)
        (GLSymplecticFin.finSumFinEquiv_inl_ne_inr i i) := by
  rw [positiveLongRootSubgroup_def, inclusion_def,
    GeneralLinear.hopfIdealInclusion_def, GeneralLinear.rootSubgroup_def]
  simp only [Category.assoc, eqToHom_refl, Category.id_comp]
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
        (GLSymplecticFin.finSumFinEquiv_inr_ne_inl i i) := by
  rw [negativeLongRootSubgroup_def, inclusion_def,
    GeneralLinear.hopfIdealInclusion_def, GeneralLinear.rootSubgroup_def]
  simp only [Category.assoc, eqToHom_refl, Category.id_comp]
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
