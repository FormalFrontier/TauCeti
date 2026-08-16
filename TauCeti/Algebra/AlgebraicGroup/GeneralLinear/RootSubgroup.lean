/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- The named scheme presentation and its points equivalence describe the target.
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Scheme
-- `TauCeti.AdditiveGroup.gaPointsMulEquiv` and the coordinate Hopf algebra of `𝔾ₐ` are its source.
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Scheme
-- Full faithfulness recovers the coordinate morphism from its natural action on points.
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
-- `TauCeti.transvectionUnit` is the matrix the homomorphism is built from.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection

/-!
# The root subgroups of the general linear group

For a pair of distinct indices `i ≠ j`, the elementary matrices `xᵢⱼ(c) = 1 + c Eᵢⱼ` form a
one-parameter subgroup of `GLₙ`. This file promotes that family to a homomorphism of affine group
schemes

`xᵢⱼ : 𝔾ₐ → GLₙ`

over an arbitrary commutative base ring `R`. On the
`A`-points of `𝔾ₐ`, which are the additive group of `A`, it is the map `c ↦ xᵢⱼ(c)` into the
`A`-points of `GLₙ`, which are `GL n A`. The natural family of point maps determines a
coordinate Hopf-algebra morphism by full faithfulness of the functor of points, and relative
spectrum gives `TauCeti.GeneralLinear.rootSubgroup` as a morphism of affine group schemes.

Reading the index pair `(i, j)` as the root `εᵢ - εⱼ` of the diagonal torus of `GLₙ`, this is the
**root subgroup** of that root. The relations it satisfies — additivity in the parameter, the
Chevalley commutator relations, and the rescaling of the parameter under conjugation by the torus
— all hold at the level of the matrices, and are proved in
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/Transvection.lean`; the points equivalences
`TauCeti.GeneralLinear.pointsMulEquiv` and `TauCeti.AdditiveGroup.gaPointsMulEquiv` transport them
to any of the three views of the group. Nothing here needs `R` to be a field, and nothing needs the
base to be reduced or the rank to be positive: the construction is the one over `ℤ` that a
Chevalley–Demazure group of type `A` base changes from.

## Main definitions

* `TauCeti.GeneralLinear.rootSubgroupPoints`: the homomorphism on `A`-points, from the additive
  group of `A` to `GL n A`, read through the two points equivalences.
* `TauCeti.GeneralLinear.rootSubgroupCoordinateMap`: the corresponding coordinate Hopf-algebra
  morphism `O(GLₙ) → O(𝔾ₐ)`.
* `TauCeti.GeneralLinear.rootSubgroup`: the resulting affine group-scheme morphism
  `𝔾ₐ → GLₙ`.

## Main results

* `TauCeti.GeneralLinear.pointsMulEquiv_rootSubgroupPoints`: the homomorphism on points is the
  elementary matrix of the parameter.
* `TauCeti.GeneralLinear.rootSubgroupPoints_injective`: the homomorphism on points is injective.
* `TauCeti.GeneralLinear.mapValue_rootSubgroupPoints`: it is natural in the value algebra.
* `TauCeti.GeneralLinear.schemePointsMulEquiv_rootSubgroup`: on scheme-valued points, composing
  with the group-scheme morphism is again the elementary matrix of the parameter.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21, where the root subgroups of a split reductive group
  are characterised by exactly these equations.
* R. W. Carter, *Simple Groups of Lie Type* (1972), §11.3.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti

namespace GeneralLinear

universe u w

variable {R : Type u} [CommRing R] {N : ℕ} {i j : Fin N}

section Points

variable {A : Type w} [CommRing A] [Algebra R A] {B : Type w} [CommRing B] [Algebra R B]

/-- The root subgroup homomorphism on `A`-points: it sends the `A`-point `c` of `𝔾ₐ` to the
elementary matrix `xᵢⱼ(c)`, an `A`-point of `GLₙ`. -/
noncomputable def rootSubgroupPoints (hij : i ≠ j) :
    WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R N →ₐ[R] A) :=
  ((pointsMulEquiv (R := R) (A := A) N).symm.toMonoidHom.comp
    ((transvectionHom hij).comp
      (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).toMonoidHom))

/-- On points, the root subgroup homomorphism is the elementary matrix of the parameter. This is
not a `simp` lemma, since `TauCeti.GeneralLinear.pointsMulEquiv_apply` rewrites its left-hand
side. -/
theorem pointsMulEquiv_rootSubgroupPoints (hij : i ≠ j)
    (f : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    pointsMulEquiv N (rootSubgroupPoints hij f) =
      transvectionUnit hij
        (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A) f)) := by
  rw [rootSubgroupPoints]
  simp

/-- The root subgroup homomorphism on points is injective. -/
theorem rootSubgroupPoints_injective (hij : i ≠ j) :
    Function.Injective (rootSubgroupPoints (R := R) (A := A) hij) := by
  intro f g h
  apply (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).injective
  have h' :
      transvectionUnit hij
          (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A) f)) =
        transvectionUnit hij
          (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A) g)) := by
    rw [← pointsMulEquiv_rootSubgroupPoints, ← pointsMulEquiv_rootSubgroupPoints]
    exact congrArg (pointsMulEquiv (R := R) (A := A) N) h
  simpa only [ofAdd_toAdd] using
    congrArg Multiplicative.ofAdd (transvectionUnit_injective (A := A) hij h')

/-- The root subgroup homomorphism is natural in the value algebra: the elementary matrix of the
image parameter is the image of the elementary matrix. -/
theorem mapValue_rootSubgroupPoints (φ : A →ₐ[R] B) (hij : i ≠ j)
    (f : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R N) φ (rootSubgroupPoints hij f) =
      rootSubgroupPoints hij
        (AlgHom.mapValue (H := AdditiveGroup.coordinateHopfAlgebra R) φ f) := by
  apply (pointsMulEquiv (R := R) (A := B) N).injective
  rw [pointsMulEquiv_mapValue, pointsMulEquiv_rootSubgroupPoints,
    pointsMulEquiv_rootSubgroupPoints, map_transvectionUnit,
    AdditiveGroup.toAdd_gaPointsMulEquiv_mapValue]
  rfl

end Points

section Functor

/-- The natural transformation of group-valued functors whose component at an `A`-point sends
`c` to the elementary matrix `xᵢⱼ(c)`. -/
noncomputable def rootSubgroupPointsMap (hij : i ≠ j) :
    HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R N) where
  app A := GrpCat.ofHom (rootSubgroupPoints (A := A) hij)
  naturality _ _ φ := by
    ext f
    exact (mapValue_rootSubgroupPoints φ.hom hij f).symm

/-- The component of the natural points map at a value algebra is the root subgroup
homomorphism on points. -/
@[simp]
theorem rootSubgroupPointsMap_app (hij : i ≠ j) (A : CommAlgCat.{w} R) :
    (rootSubgroupPointsMap (R := R) (N := N) hij).app A =
      GrpCat.ofHom (rootSubgroupPoints hij) :=
  (rfl)

end Functor

section Scheme

/-- The coordinate morphism of the root subgroup, recovered from its natural action on points.
Its direction is `O(GLₙ) → O(𝔾ₐ)`, opposite to the represented group-scheme morphism. -/
noncomputable def rootSubgroupCoordinateMap (hij : i ≠ j) :
    coordinateHopfAlgebra R N ⟶ AdditiveGroup.coordinateHopfAlgebra R :=
  ((CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}).preimage
    (rootSubgroupPointsMap.{u, u} (R := R) (N := N) hij)).unop

/-- Precomposition by the root-subgroup coordinate morphism is the previously constructed
natural map on convolution points. -/
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

/-- On every same-universe value algebra, the map induced by the root-subgroup coordinate
morphism is the elementary root subgroup homomorphism already constructed on points. -/
@[simp]
theorem mapPointsFunctor_rootSubgroupCoordinateMap_app (hij : i ≠ j)
    (A : CommAlgCat.{u} R)
    (f : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A) :
    (CommHopfAlgCat.mapPointsFunctor
      (rootSubgroupCoordinateMap (R := R) (N := N) hij)).app A f =
      rootSubgroupPoints hij f := by
  rw [mapPointsFunctor_rootSubgroupCoordinateMap, rootSubgroupPointsMap_app]
  rfl

/-- **The root subgroup of `GLₙ` attached to the root `εᵢ - εⱼ`**: the affine
group-scheme morphism `𝔾ₐ → GLₙ` whose value on points is `c ↦ xᵢⱼ(c)`. -/
noncomputable def rootSubgroup (hij : i ≠ j) :
    AdditiveGroup.groupScheme R ⟶ groupScheme R N :=
  eqToHom (AdditiveGroup.groupScheme_def R) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
      (rootSubgroupCoordinateMap hij).op ≫
    eqToHom (groupScheme_def R N).symm

/-- The root subgroup is relative spectrum applied contravariantly to its coordinate
Hopf-algebra morphism, transported across the named presentations of `𝔾ₐ` and `GLₙ`. -/
theorem rootSubgroup_def (hij : i ≠ j) :
    rootSubgroup (R := R) (N := N) hij =
      eqToHom (AdditiveGroup.groupScheme_def R) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (rootSubgroupCoordinateMap hij).op ≫
        eqToHom (groupScheme_def R N).symm := by
  unfold rootSubgroup
  rfl

section SchemePoints

variable (A : Type u) [CommRing A] [Algebra R A]

private lemma groupSchemePointMulEquiv_comp_rootSubgroup (hij : i ≠ j)
    (q : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    AdditiveGroup.groupSchemePointMulEquiv A q ≫ (rootSubgroup hij).hom.hom =
      groupSchemePointMulEquiv N A (rootSubgroupPoints hij q) := by
  rw [rootSubgroup_def,
    ← mapPointsFunctor_rootSubgroupCoordinateMap_app hij (CommAlgCat.of R A) q]
  exact CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain
    (R := R) A (groupScheme_def R N) (AdditiveGroup.groupScheme_def R)
      (groupSchemePointMulEquiv N A) (AdditiveGroup.groupSchemePointMulEquiv A)
      (groupSchemePointMulEquiv_apply_left N A)
      (AdditiveGroup.groupSchemePointMulEquiv_apply_left A)
      (rootSubgroupCoordinateMap hij) q

/-- **The root subgroup on scheme-valued points**: composing an `A`-point of `𝔾ₐ` with the root
subgroup morphism gives the elementary matrix `xᵢⱼ(c)` of its parameter `c`, as an `A`-point of
`GLₙ`. -/
@[simp]
theorem schemePointsMulEquiv_rootSubgroup (hij : i ≠ j)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (AdditiveGroup.groupScheme R).X) :
    schemePointsMulEquiv N A (p ≫ (rootSubgroup hij).hom.hom) =
      transvectionUnit hij
        (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p)) := by
  obtain ⟨q, rfl⟩ := (AdditiveGroup.groupSchemePointMulEquiv A).surjective p
  rw [groupSchemePointMulEquiv_comp_rootSubgroup,
    schemePointsMulEquiv_groupSchemePointMulEquiv,
    pointsMulEquiv_rootSubgroupPoints,
    AdditiveGroup.schemePointsMulEquiv_groupSchemePointMulEquiv]

end SchemePoints

end Scheme

end GeneralLinear

end TauCeti
