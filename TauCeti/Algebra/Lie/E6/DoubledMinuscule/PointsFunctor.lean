/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Functor
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.GroupScheme

/-!
# The points of the doubled type-E6 minuscule carrier, functorially

`TauCeti.E6DoubledMinuscule.groupScheme` is the explicit full-weight type-`E₆` carrier over `ℤ`
built from `V(ϖ₁) ⊕ V(ϖ₆)`, and `TauCeti.E6DoubledMinuscule.points A` realizes its `A`-valued
points as a subgroup of `GL₅₄(A)`. This file supplies the homomorphism induced by an arbitrary
homomorphism of value rings and assembles these point groups into a functor on commutative
`ℤ`-algebras.

The induced map is entrywise and preserves the two pinned families:

```text
f (x_i(u)) = x_i(f(u)),        f (t(s)) = t(f ∘ s).
```

The quotient of the ambient general-linear coordinate Hopf algebra by the doubled carrier's
defining ideal represents this functor. Nothing here asserts reductivity, maximality of the weight
torus, or an identification of the carrier's root datum, and no declaration mentions the `E₆`
diagram symmetry that the doubled index set was assembled to carry.

## Main declarations

* `TauCeti.E6DoubledMinuscule.pointsMap`: the map on carrier points induced by a ring
  homomorphism.
* `TauCeti.E6DoubledMinuscule.pointsFunctor`: the group-valued functor of points.
* `TauCeti.E6DoubledMinuscule.pointsMulEquiv`: the pointwise representing isomorphism.
* `TauCeti.E6DoubledMinuscule.pointsFunctorNatIso`: the natural representing isomorphism.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*,
  Sections 1.15 and 1.17.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2, for the doubled minuscule realization.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1--2.

The interface specializes the carrier-independent functor in
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Functor`, and follows the formal
template of `TauCeti.Algebra.Lie.E6.Minuscule.PointsFunctor`, which does the same for the
`27`-dimensional carrier, as the analogous full-weight type-`A` and type-`C` carrier interfaces
do for theirs.

## Roadmap

This advances the target "points over an algebraically closed field as a group, functorially in
the field" in Layer 9, "pinned Chevalley--Demazure group schemes over `ℤ`", of
`TauCetiRoadmap/ReductiveGroups/README.md`. Its consumer is the `²E₆(q)` branch of milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md`, whose Steinberg map is the graph automorphism composed
with the `q`-power Frobenius, and the Frobenius of a carrier is the endomorphism this
functoriality induces from the `q`-power map of its value ring.
-/

public section

open CategoryTheory

namespace TauCeti.E6DoubledMinuscule

universe v v'

noncomputable section

section Map

variable {A : Type v} {B : Type v'} [CommRing A] [CommRing B]

/-- The map on the points of the doubled type-`E₆` minuscule carrier induced by a homomorphism of
value rings. It is the entrywise map on `GL₅₄`, restricted to the subgroup cut out by the
carrier's defining ideal. -/
def pointsMap (f : A →+* B) : points A →* points B :=
  ((MulEquiv.subgroupCongr (points_def B)).symm.toMonoidHom).comp
    ((GeneralLinear.mapHopfIdealPointsSubgroup 54 definingIdeal f.toIntAlgHom).comp
      (MulEquiv.subgroupCongr (points_def A)).toMonoidHom)

/-- The induced map on doubled type-`E₆` carrier points is the entrywise map. -/
@[simp]
theorem coe_pointsMap (f : A →+* B) (g : points A) :
    (pointsMap f g : Matrix.GeneralLinearGroup (Fin 54) B) =
      Matrix.GeneralLinearGroup.map f g := by
  have hring : f.toIntAlgHom.toRingHom = f := RingHom.ext (RingHom.toIntAlgHom_apply f)
  rw [pointsMap]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.subgroupCongr_symm_apply, GeneralLinear.coe_mapHopfIdealPointsSubgroup,
    MulEquiv.subgroupCongr_apply, hring]

/-- Entrywise, the induced map applies the homomorphism of value rings to each matrix entry. -/
theorem coe_pointsMap_apply (f : A →+* B) (g : points A) (i j : Fin 54) :
    ((pointsMap f g : Matrix.GeneralLinearGroup (Fin 54) B) :
        Matrix (Fin 54) (Fin 54) B) i j =
      f (((g : Matrix.GeneralLinearGroup (Fin 54) A) : Matrix (Fin 54) (Fin 54) A) i j) := by
  rw [coe_pointsMap, Matrix.GeneralLinearGroup.map_apply]

/-- The identity homomorphism induces the identity on doubled type-`E₆` carrier points. -/
@[simp]
theorem pointsMap_id : pointsMap (RingHom.id A) = MonoidHom.id _ := by
  have hid : (RingHom.id A).toIntAlgHom = AlgHom.id ℤ A := AlgHom.ext fun _ ↦ rfl
  rw [pointsMap, hid, GeneralLinear.mapHopfIdealPointsSubgroup_id]
  apply MonoidHom.ext
  intro g
  exact (MulEquiv.subgroupCongr (points_def A)).symm_apply_apply g

/-- The induced maps on doubled type-`E₆` carrier points compose. -/
@[simp]
theorem pointsMap_comp {C : Type*} [CommRing C] (f : A →+* B) (g : B →+* C) :
    pointsMap (g.comp f) = (pointsMap g).comp (pointsMap f) := by
  have hcomp : (g.comp f).toIntAlgHom = g.toIntAlgHom.comp f.toIntAlgHom :=
    AlgHom.ext fun _ ↦ rfl
  apply MonoidHom.ext
  intro x
  simp only [pointsMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hcomp,
    GeneralLinear.mapHopfIdealPointsSubgroup_comp, MulEquiv.apply_symm_apply]

/-- An injective homomorphism of value rings induces an injective map on doubled type-`E₆` carrier
points. -/
theorem pointsMap_injective {f : A →+* B} (hf : Function.Injective f) :
    Function.Injective (pointsMap f) := by
  rw [pointsMap]
  exact (MulEquiv.subgroupCongr (points_def B)).symm.injective.comp
    ((GeneralLinear.mapHopfIdealPointsSubgroup_injective 54 definingIdeal hf).comp
      (MulEquiv.subgroupCongr (points_def A)).injective)

/-- The induced map carries a numbered root-subgroup parameter along the homomorphism of value
rings. -/
@[simp]
theorem pointsMap_rootSubgroupPoints (f : A →+* B) (k : Fin 6 ⊕ Fin 6)
    (u : Multiplicative A) :
    pointsMap f (rootSubgroupPoints k A u) =
      rootSubgroupPoints k B (Multiplicative.ofAdd (f (Multiplicative.toAdd u))) := by
  apply Subtype.ext
  rw [coe_pointsMap, coe_rootSubgroupPoints, coe_rootSubgroupPoints,
    UniversalEnvelopingAlgebra.map_kostantRootSubgroupMatrix,
    AdditiveGroup.mapValue_gaPointsMulEquiv_symm_apply, RingHom.toIntAlgHom_apply]

/-- The induced map carries a point of the pinned split weight torus coordinatewise along the
homomorphism of value rings. -/
@[simp]
theorem pointsMap_weightTorusPoints (f : A →+* B) (s : Fin 6 → Aˣ) :
    pointsMap f (weightTorusPoints A s) =
      weightTorusPoints B fun i ↦ Units.map (f : A →* B) (s i) := by
  apply Subtype.ext
  rw [coe_pointsMap, coe_weightTorusPoints, coe_weightTorusPoints]
  exact UniversalEnvelopingAlgebra.map_kostantTorusMatrix
    (M := lattice.toAddSubgroup) (b := matrixBasis) (wt := matrixWeight) f s

end Map

/-! ## The functor of points -/

/-- The group-valued functor of points of the doubled type-`E₆` minuscule carrier. -/
def pointsFunctor : CommAlgCat.{v} ℤ ⥤ GrpCat.{v} where
  obj A := GrpCat.of (points A)
  map f := GrpCat.ofHom (pointsMap f.hom.toRingHom)
  map_id _A := congrArg GrpCat.ofHom pointsMap_id
  map_comp f g := congrArg GrpCat.ofHom
    (pointsMap_comp f.hom.toRingHom g.hom.toRingHom)

/-- The object part of the doubled type-`E₆` carrier's points functor is its named point group. -/
@[simp]
theorem pointsFunctor_obj (A : CommAlgCat.{v} ℤ) :
    pointsFunctor.obj A = GrpCat.of (points A) :=
  (rfl)

/-- The morphism part of the doubled type-`E₆` carrier's points functor is the induced entrywise
map. -/
@[simp]
theorem pointsFunctor_map {A B : CommAlgCat.{v} ℤ} (f : A ⟶ B) :
    pointsFunctor.map f =
      eqToHom (pointsFunctor_obj A) ≫ GrpCat.ofHom (pointsMap f.hom.toRingHom) ≫
        eqToHom (pointsFunctor_obj B).symm :=
  (rfl)

/-- At a bundled `ℤ`-algebra, the named carrier points are the ambient general-linear subgroup cut
out by the defining ideal. -/
private theorem points_eq_hopfIdealPointsSubgroup (A : CommAlgCat.{v} ℤ) :
    points A = GeneralLinear.hopfIdealPointsSubgroup 54 definingIdeal A := by
  rw [points_def A]
  congr 1
  exact Subsingleton.elim _ _

/-- The points of the quotient coordinate Hopf algebra are the named doubled type-`E₆` carrier
points. -/
def pointsMulEquiv (A : CommAlgCat.{v} ℤ) :
    HopfAlgebra.points
        (R := ℤ) (H := CommHopfAlgCat.quotient
          (GeneralLinear.coordinateHopfAlgebra ℤ 54) definingIdeal) A ≃*
      points A :=
  (GeneralLinear.hopfIdealPointsSubgroupMulEquiv 54 definingIdeal A).trans
    (MulEquiv.subgroupCongr (points_eq_hopfIdealPointsSubgroup A)).symm

/-- A quotient point, read through `pointsMulEquiv`, is its ambient point viewed as an invertible
matrix. -/
@[simp]
theorem coe_pointsMulEquiv_apply (A : CommAlgCat.{v} ℤ)
    (q : HopfAlgebra.points
      (R := ℤ) (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra ℤ 54) definingIdeal) A) :
    (pointsMulEquiv A q : Matrix.GeneralLinearGroup (Fin 54) A) =
      GeneralLinear.pointsMulEquiv 54
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra ℤ 54) definingIdeal A q) := by
  simp only [pointsMulEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_symm_apply]
  exact GeneralLinear.coe_hopfIdealPointsSubgroupMulEquiv_apply 54 definingIdeal A q

/-- Including the ambient Hopf-algebra point underlying the inverse of `pointsMulEquiv` recovers
the point corresponding to the underlying matrix. -/
@[simp]
theorem quotientPointsHom_pointsMulEquiv_symm (A : CommAlgCat.{v} ℤ) (g : points A) :
    CommHopfAlgCat.quotientPointsHom
        (GeneralLinear.coordinateHopfAlgebra ℤ 54) definingIdeal A
        ((pointsMulEquiv A).symm g) =
      (GeneralLinear.pointsMulEquiv (R := ℤ) 54).symm
        (g : Matrix.GeneralLinearGroup (Fin 54) A) := by
  simp only [pointsMulEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
  rw [GeneralLinear.quotientPointsHom_hopfIdealPointsSubgroupMulEquiv_symm,
    MulEquiv.subgroupCongr_apply]

/-- The pointwise identification with quotient Hopf-algebra points is natural in the value
algebra. -/
@[simp]
theorem pointsMulEquiv_mapPoints {A B : CommAlgCat.{v} ℤ} (f : A ⟶ B)
    (q : HopfAlgebra.points
      (R := ℤ) (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra ℤ 54) definingIdeal) A) :
    pointsMulEquiv B
        (HopfAlgebra.mapPoints
          (H := CommHopfAlgCat.quotient
            (GeneralLinear.coordinateHopfAlgebra ℤ 54) definingIdeal) f q) =
      pointsMap f.hom.toRingHom (pointsMulEquiv A q) := by
  apply Subtype.ext
  rw [coe_pointsMap]
  simp only [pointsMulEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_symm_apply]
  exact (congrArg Subtype.val
      (GeneralLinear.hopfIdealPointsSubgroupMulEquiv_mapPoints 54 definingIdeal f q)).trans
    (GeneralLinear.coe_mapHopfIdealPointsSubgroup 54 definingIdeal f.hom _)

/-- The quotient coordinate Hopf algebra represents the points functor of the doubled type-`E₆`
minuscule carrier. -/
def pointsFunctorNatIso :
    HopfAlgebra.pointsFunctor
        (R := ℤ) (H := CommHopfAlgCat.quotient
          (GeneralLinear.coordinateHopfAlgebra ℤ 54) definingIdeal) ≅
      pointsFunctor :=
  NatIso.ofComponents (fun A ↦ (pointsMulEquiv A).toGrpIso)
    (by
      intro A B f
      ext q
      exact pointsMulEquiv_mapPoints f q)

/-- The forward component of the representing natural isomorphism is the pointwise
identification. -/
@[simp]
theorem pointsFunctorNatIso_hom_app_apply (A : CommAlgCat.{v} ℤ)
    (q : HopfAlgebra.points
      (R := ℤ) (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra ℤ 54) definingIdeal) A) :
    eqToHom (pointsFunctor_obj A) (pointsFunctorNatIso.hom.app A q) = pointsMulEquiv A q :=
  (rfl)

/-- The inverse component of the representing natural isomorphism is the inverse pointwise
identification. -/
@[simp]
theorem pointsFunctorNatIso_inv_app_apply (A : CommAlgCat.{v} ℤ) (g : points A) :
    pointsFunctorNatIso.inv.app A (eqToHom (pointsFunctor_obj A).symm g) =
      (pointsMulEquiv A).symm g :=
  (rfl)

end

end TauCeti.E6DoubledMinuscule
