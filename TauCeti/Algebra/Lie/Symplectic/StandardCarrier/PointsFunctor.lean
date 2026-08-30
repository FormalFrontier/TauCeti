/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Functor
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Scheme

/-!
# The points of the full-weight type-C carrier, functorially

`TauCeti.SpStd.groupScheme n` is the explicit full-weight type-`C_(n+1)` carrier over `ℤ`, and
`TauCeti.SpStd.points n A` reads its `A`-valued points as a subgroup of `GL_(2n+2)(A)`. This file
supplies the group homomorphism induced by an arbitrary homomorphism of value rings and assembles
these point groups into a functor on commutative `ℤ`-algebras.

The induced map is entrywise and carries the pinned families by

```text
f (x_i(u)) = x_i(f(u)),        f (t(s)) = t(f ∘ s).
```

The quotient of the ambient general-linear coordinate Hopf algebra by the carrier's defining
ideal represents this functor. Nothing here asserts reductivity, maximality of the weight torus,
or an identification with the separately constructed symplectic group scheme.

## Main definitions

* `TauCeti.SpStd.pointsMap`: the map on carrier points induced by a ring homomorphism.
* `TauCeti.SpStd.pointsFunctor`: the group-valued functor of points of the carrier.
* `TauCeti.SpStd.pointsMulEquiv` and `TauCeti.SpStd.pointsFunctorNatIso`: the pointwise and
  natural representing isomorphisms.

## Main results

* `TauCeti.SpStd.coe_pointsMap`: the induced map is entrywise.
* `TauCeti.SpStd.pointsMap_id` and `TauCeti.SpStd.pointsMap_comp`: functoriality.
* `TauCeti.SpStd.pointsMap_rootSubgroupPoints` and
  `TauCeti.SpStd.pointsMap_weightTorusPoints`: naturality of the pinned families.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*,
  Sections 1.15 and 1.17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

The interface follows the carrier-independent functor in
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Functor` and the pinned Geck-carrier
specialization. This completes the target "points over an algebraically closed field as a group,
functorially in the field" for the full-weight type-C carrier in Layer 9 of the ReductiveGroups
roadmap. Its consumer is the type-C branch of milestone L0 of the CFSGStatement roadmap.
-/

public section

open CategoryTheory

namespace TauCeti.SpStd

universe v v'

noncomputable section

variable (n : ℕ)

section Map

variable {A : Type v} {B : Type v'} [CommRing A] [CommRing B]

/-- The map on the points of the full-weight type-C carrier induced by a homomorphism of value
rings. It is the entrywise map on the ambient general linear group, restricted to the subgroup
cut out by the carrier's defining ideal. -/
def pointsMap (f : A →+* B) : points n A →* points n B :=
  ((MulEquiv.subgroupCongr (points_def n B)).symm.toMonoidHom).comp
    ((GeneralLinear.mapHopfIdealPointsSubgroup ((n + 1) + (n + 1)) (definingIdeal n)
          f.toIntAlgHom).comp
      (MulEquiv.subgroupCongr (points_def n A)).toMonoidHom)

/-- The induced map on type-C carrier points is the entrywise map. -/
@[simp]
theorem coe_pointsMap (f : A →+* B) (g : points n A) :
    (pointsMap n f g : Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) B) =
      Matrix.GeneralLinearGroup.map f g := by
  have hring : f.toIntAlgHom.toRingHom = f := RingHom.ext (RingHom.toIntAlgHom_apply f)
  rw [pointsMap]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.subgroupCongr_symm_apply,
    GeneralLinear.coe_mapHopfIdealPointsSubgroup, MulEquiv.subgroupCongr_apply, hring]

/-- Entrywise, the induced map applies the homomorphism of value rings to each matrix entry. -/
theorem coe_pointsMap_apply (f : A →+* B) (g : points n A)
    (i j : Fin ((n + 1) + (n + 1))) :
    ((pointsMap n f g : Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) B) :
        Matrix (Fin ((n + 1) + (n + 1))) (Fin ((n + 1) + (n + 1))) B) i j =
      f (((g : Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) :
        Matrix (Fin ((n + 1) + (n + 1))) (Fin ((n + 1) + (n + 1))) A) i j) := by
  rw [coe_pointsMap, Matrix.GeneralLinearGroup.map_apply]

/-- The identity homomorphism induces the identity on type-C carrier points. -/
@[simp]
theorem pointsMap_id : pointsMap n (RingHom.id A) = MonoidHom.id _ := by
  have hid : (RingHom.id A).toIntAlgHom = AlgHom.id ℤ A :=
    AlgHom.ext fun _ ↦ rfl
  rw [pointsMap, hid,
    GeneralLinear.mapHopfIdealPointsSubgroup_id]
  apply MonoidHom.ext
  intro g
  exact (MulEquiv.subgroupCongr (points_def n A)).symm_apply_apply g

/-- The induced maps on type-C carrier points compose. -/
@[simp]
theorem pointsMap_comp {C : Type*} [CommRing C] (f : A →+* B) (g : B →+* C) :
    pointsMap n (g.comp f) = (pointsMap n g).comp (pointsMap n f) := by
  have hcomp : (g.comp f).toIntAlgHom = g.toIntAlgHom.comp f.toIntAlgHom :=
    AlgHom.ext fun _ ↦ rfl
  apply MonoidHom.ext
  intro x
  simp only [pointsMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hcomp,
    GeneralLinear.mapHopfIdealPointsSubgroup_comp, MulEquiv.apply_symm_apply]

/-- An injective homomorphism of value rings induces an injective map on type-C carrier points. -/
theorem pointsMap_injective {f : A →+* B} (hf : Function.Injective f) :
    Function.Injective (pointsMap n f) := by
  rw [pointsMap]
  exact (MulEquiv.subgroupCongr (points_def n B)).symm.injective.comp
    ((GeneralLinear.mapHopfIdealPointsSubgroup_injective
      ((n + 1) + (n + 1)) (definingIdeal n) hf).comp
        (MulEquiv.subgroupCongr (points_def n A)).injective)

/-- The induced map carries a numbered root-subgroup parameter along the homomorphism of value
rings. -/
@[simp]
theorem pointsMap_rootSubgroupPoints (f : A →+* B)
    (i : Fin (n + 1) ⊕ Fin (n + 1)) (u : Multiplicative A) :
    pointsMap n f (rootSubgroupPoints n i A u) =
      rootSubgroupPoints n i B (Multiplicative.ofAdd (f (Multiplicative.toAdd u))) := by
  apply Subtype.ext
  rw [coe_pointsMap, coe_rootSubgroupPoints, coe_rootSubgroupPoints,
    UniversalEnvelopingAlgebra.map_kostantRootSubgroupMatrix,
    AdditiveGroup.mapValue_gaPointsMulEquiv_symm_apply, RingHom.toIntAlgHom_apply]

/-- The induced map carries a point of the pinned split weight torus coordinatewise along the
homomorphism of value rings. -/
@[simp]
theorem pointsMap_weightTorusPoints (f : A →+* B) (s : Fin (n + 1) → Aˣ) :
    pointsMap n f (weightTorusPoints n A s) =
      weightTorusPoints n B fun i ↦ Units.map (f : A →* B) (s i) := by
  apply Subtype.ext
  rw [coe_pointsMap, coe_weightTorusPoints, coe_weightTorusPoints]
  exact UniversalEnvelopingAlgebra.map_kostantTorusMatrix
    (M := (lattice n).toAddSubgroup) (b := latticeBasis n) (wt := basisWeight n) f s

end Map

/-! ## The functor of points -/

section Functor

/-- The group-valued functor of points of the full-weight type-C carrier. -/
def pointsFunctor : CommAlgCat.{v} ℤ ⥤ GrpCat.{v} where
  obj A := GrpCat.of (points n A)
  map f := GrpCat.ofHom (pointsMap n f.hom.toRingHom)
  map_id _A := congrArg GrpCat.ofHom (pointsMap_id n)
  map_comp f g := congrArg GrpCat.ofHom
    (pointsMap_comp n f.hom.toRingHom g.hom.toRingHom)

/-- The object part of the type-C carrier's points functor is its named point group. -/
@[simp]
theorem pointsFunctor_obj (A : CommAlgCat.{v} ℤ) :
    (pointsFunctor n).obj A = GrpCat.of (points n A) :=
  (rfl)

/-- The morphism part of the type-C carrier's points functor is the induced entrywise map. -/
@[simp]
theorem pointsFunctor_map {A B : CommAlgCat.{v} ℤ} (f : A ⟶ B) :
    (pointsFunctor n).map f =
      eqToHom (pointsFunctor_obj n A) ≫
        GrpCat.ofHom (pointsMap n f.hom.toRingHom) ≫
        eqToHom (pointsFunctor_obj n B).symm :=
  (rfl)

/-- At a bundled `ℤ`-algebra, the named carrier points are the ambient general-linear subgroup
cut out by the defining ideal. -/
private theorem points_eq_hopfIdealPointsSubgroup (A : CommAlgCat.{v} ℤ) :
    points n A =
      GeneralLinear.hopfIdealPointsSubgroup ((n + 1) + (n + 1)) (definingIdeal n) A := by
  rw [points_def n A]
  congr 1
  exact Subsingleton.elim _ _

/-- The points of the quotient coordinate Hopf algebra are the named type-C carrier points. -/
def pointsMulEquiv (A : CommAlgCat.{v} ℤ) :
    HopfAlgebra.points
        (R := ℤ) (H := CommHopfAlgCat.quotient
          (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))) (definingIdeal n)) A ≃*
      points n A :=
  (GeneralLinear.hopfIdealPointsSubgroupMulEquiv ((n + 1) + (n + 1))
      (definingIdeal n) A).trans
    (MulEquiv.subgroupCongr (points_eq_hopfIdealPointsSubgroup n A)).symm

/-- A quotient point, read through `pointsMulEquiv`, is its ambient point viewed as an invertible
matrix. -/
@[simp]
theorem coe_pointsMulEquiv_apply (A : CommAlgCat.{v} ℤ)
    (q : HopfAlgebra.points
      (R := ℤ) (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))) (definingIdeal n)) A) :
    (pointsMulEquiv n A q : Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) =
      GeneralLinear.pointsMulEquiv ((n + 1) + (n + 1))
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))) (definingIdeal n)
          A q) := by
  simp only [pointsMulEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_symm_apply]
  exact GeneralLinear.coe_hopfIdealPointsSubgroupMulEquiv_apply
    ((n + 1) + (n + 1)) (definingIdeal n) A q

/-- Including the ambient Hopf-algebra point underlying the inverse of `pointsMulEquiv` recovers
the point corresponding to the underlying matrix. -/
@[simp]
theorem quotientPointsHom_pointsMulEquiv_symm (A : CommAlgCat.{v} ℤ) (g : points n A) :
    CommHopfAlgCat.quotientPointsHom
        (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))) (definingIdeal n) A
        ((pointsMulEquiv n A).symm g) =
      (GeneralLinear.pointsMulEquiv (R := ℤ) ((n + 1) + (n + 1))).symm
        (g : Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) := by
  simp only [pointsMulEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
  rw [GeneralLinear.quotientPointsHom_hopfIdealPointsSubgroupMulEquiv_symm,
    MulEquiv.subgroupCongr_apply]

/-- The pointwise identification with quotient Hopf-algebra points is natural in the value
algebra. -/
@[simp]
theorem pointsMulEquiv_mapPoints {A B : CommAlgCat.{v} ℤ} (f : A ⟶ B)
    (q : HopfAlgebra.points
      (R := ℤ) (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))) (definingIdeal n)) A) :
    pointsMulEquiv n B
        (HopfAlgebra.mapPoints
          (H := CommHopfAlgCat.quotient
            (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))) (definingIdeal n))
          f q) =
      pointsMap n f.hom.toRingHom (pointsMulEquiv n A q) := by
  apply Subtype.ext
  rw [coe_pointsMap]
  simp only [pointsMulEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_symm_apply]
  exact (congrArg Subtype.val
      (GeneralLinear.hopfIdealPointsSubgroupMulEquiv_mapPoints
        ((n + 1) + (n + 1)) (definingIdeal n) f q)).trans
    (GeneralLinear.coe_mapHopfIdealPointsSubgroup ((n + 1) + (n + 1)) (definingIdeal n)
      f.hom _)

/-- The quotient coordinate Hopf algebra represents the points functor of the full-weight type-C
carrier. -/
def pointsFunctorNatIso :
    HopfAlgebra.pointsFunctor
        (R := ℤ) (H := CommHopfAlgCat.quotient
          (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))) (definingIdeal n)) ≅
      pointsFunctor n :=
  NatIso.ofComponents (fun A ↦ (pointsMulEquiv n A).toGrpIso)
    (by
      intro A B f
      ext q
      exact pointsMulEquiv_mapPoints n f q)

/-- The forward component of the representing natural isomorphism is the pointwise
identification. -/
@[simp]
theorem pointsFunctorNatIso_hom_app_apply (A : CommAlgCat.{v} ℤ)
    (q : HopfAlgebra.points
      (R := ℤ) (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))) (definingIdeal n)) A) :
    eqToHom (pointsFunctor_obj n A) ((pointsFunctorNatIso n).hom.app A q) =
      pointsMulEquiv n A q :=
  (rfl)

/-- The inverse component of the representing natural isomorphism is the inverse pointwise
identification. -/
@[simp]
theorem pointsFunctorNatIso_inv_app_apply (A : CommAlgCat.{v} ℤ) (g : points n A) :
    (pointsFunctorNatIso n).inv.app A (eqToHom (pointsFunctor_obj n A).symm g) =
      (pointsMulEquiv n A).symm g :=
  (rfl)

end Functor

end

end TauCeti.SpStd
