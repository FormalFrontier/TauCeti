/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Basic

/-!
# Functorial matrix points cut out by a Hopf ideal

For a Hopf ideal `I` in the coordinate ring of `GLₙ` over a commutative ring `R`,
`TauCeti.GeneralLinear.hopfIdealPointsSubgroup n I A` is the group of `A`-valued points of the
corresponding closed subgroup scheme, in its matrix realization. This file assembles the existing
entrywise maps between these groups into a functor on commutative `R`-algebras and proves that the
quotient coordinate Hopf algebra represents this matrix-valued functor.

The construction is independent of any particular Chevalley carrier. An eventual explicit pinned
simply connected carrier can instantiate it with its defining Hopf ideal. In the integral case,
`TauCeti.GeneralLinear.iterateFrobeniusHopfIdealPoints` supplies the `p ^ k`-power Frobenius
endomorphism and its fixed-point interface.

## Main declarations

* `TauCeti.GeneralLinear.quotientPointsMulEquiv`: the pointwise group equivalence between quotient
  Hopf-algebra points and the matrix subgroup cut out by the ideal.
* `TauCeti.GeneralLinear.hopfIdealPointsSubgroupFunctor`: the group-valued functor of matrix points
  cut out by a fixed Hopf ideal.
* `TauCeti.GeneralLinear.hopfIdealPointsSubgroupNatIso`: the representing natural isomorphism.

## Roadmap

This advances the carrier-independent infrastructure for "Points over an algebraically closed
field as a group, functorially in the field" in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. The consumer is the explicit pinned simply connected
Chevalley--Demazure carrier required by milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md`; this file does not identify any provisional carrier with
that simply connected group.
-/

public section

open CategoryTheory

namespace TauCeti.GeneralLinear

universe u w

noncomputable section

variable {R : Type u} [CommRing R] (n : ℕ)
variable (I : HopfIdeal R (coordinateHopfAlgebra R n))

/-- Quotient Hopf-algebra points are multiplicatively equivalent to the matrix subgroup cut out by
the Hopf ideal. The equivalence first includes a quotient point among the ambient Hopf-algebra
points, then reads that point as an invertible matrix. -/
@[expose] noncomputable def quotientPointsMulEquiv (A : CommAlgCat.{w} R) :
    HopfAlgebra.points
        (R := R) (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I) A ≃*
      hopfIdealPointsSubgroup n I A :=
  (CommHopfAlgCat.quotientPointsSubgroupIso
      (coordinateHopfAlgebra R n) I A).groupIsoToMulEquiv.trans
    ((pointsMulEquiv n).subgroupMap
      (CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R n) I A))

/-- A quotient point, viewed through `quotientPointsMulEquiv`, is its included ambient point read as
an invertible matrix. -/
@[simp]
theorem coe_quotientPointsMulEquiv_apply (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points
      (R := R) (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I) A) :
    (quotientPointsMulEquiv n I A f : Matrix.GeneralLinearGroup (Fin n) A) =
      pointsMulEquiv n
        (CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R n) I A f) :=
  rfl

/-- The group-valued functor sending a commutative `R`-algebra to the matrix point group cut out by
a fixed Hopf ideal, before the universe lift used by `hopfIdealPointsSubgroupFunctor`. -/
private noncomputable abbrev hopfIdealPointsSubgroupFunctorUnlifted :
    CommAlgCat.{w} R ⥤ GrpCat.{w} where
  obj A := GrpCat.of (hopfIdealPointsSubgroup n I A)
  map f := GrpCat.ofHom (mapHopfIdealPointsSubgroup n I f.hom)
  map_id A := congrArg GrpCat.ofHom (mapHopfIdealPointsSubgroup_id n I A)
  map_comp f g := congrArg GrpCat.ofHom (mapHopfIdealPointsSubgroup_comp n I f.hom g.hom)

/-- The group-valued functor sending a commutative `R`-algebra to the matrix point group cut out by
a fixed Hopf ideal in the coordinate ring of `GLₙ`. Its values are universe-lifted so that its
codomain agrees with the generic Hopf-algebra points functor. -/
noncomputable def hopfIdealPointsSubgroupFunctor :
    CommAlgCat.{w} R ⥤ GrpCat.{max u w} :=
  hopfIdealPointsSubgroupFunctorUnlifted n I ⋙ GrpCat.uliftFunctor.{u, w}

/-- The object part of the Hopf-ideal matrix-points functor is the universe lift of the subgroup cut
out by the fixed Hopf ideal. -/
theorem hopfIdealPointsSubgroupFunctor_obj (A : CommAlgCat.{w} R) :
    (hopfIdealPointsSubgroupFunctor n I).obj A =
      GrpCat.of (ULift.{u, w} (hopfIdealPointsSubgroup n I A)) :=
  (rfl)

/-- The morphism part of the Hopf-ideal matrix-points functor is the universe lift of the restricted
entrywise matrix map. -/
theorem hopfIdealPointsSubgroupFunctor_map {A B : CommAlgCat.{w} R} (f : A ⟶ B) :
    (hopfIdealPointsSubgroupFunctor n I).map f =
      eqToHom (hopfIdealPointsSubgroupFunctor_obj n I A) ≫
        GrpCat.ofHom
          (MulEquiv.ulift.symm.toMonoidHom.comp
            ((mapHopfIdealPointsSubgroup n I f.hom).comp
              MulEquiv.ulift.toMonoidHom)) ≫
        eqToHom (hopfIdealPointsSubgroupFunctor_obj n I B).symm :=
  (rfl)

/-- The matrix-subgroup equivalence is natural in the value algebra. -/
theorem quotientPointsMulEquiv_mapValue {A B : CommAlgCat.{w} R} (f : A ⟶ B)
    (q : HopfAlgebra.points
      (R := R) (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I) A) :
    mapHopfIdealPointsSubgroup n I f.hom (quotientPointsMulEquiv n I A q) =
      quotientPointsMulEquiv n I B
        (HopfAlgebra.mapPoints
          (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I) f q) := by
  apply Subtype.ext
  rw [coe_mapHopfIdealPointsSubgroup, coe_quotientPointsMulEquiv_apply,
    coe_quotientPointsMulEquiv_apply]
  rw [← CommHopfAlgCat.mapPoints_quotientPointsHom]
  exact (pointsMulEquiv_mapValue n f.hom
    (CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R n) I A q)).symm

/-- The component isomorphism from quotient Hopf-algebra points to the universe-lifted matrix point
subgroup. -/
@[expose] noncomputable def hopfIdealPointsSubgroupIso (A : CommAlgCat.{w} R) :
    GrpCat.of (HopfAlgebra.points
        (R := R) (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I) A) ≅
      GrpCat.of (ULift.{u, w} (hopfIdealPointsSubgroup n I A)) :=
  ((quotientPointsMulEquiv n I A).trans
    (MulEquiv.ulift.symm : _ ≃* ULift.{u, w} (hopfIdealPointsSubgroup n I A))).toGrpIso

/-- The forward component is the universe lift of the pointwise matrix-subgroup equivalence. -/
@[simp]
theorem hopfIdealPointsSubgroupIso_hom_apply (A : CommAlgCat.{w} R)
    (q : HopfAlgebra.points
      (R := R) (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I) A) :
    CategoryTheory.ConcreteCategory.hom (hopfIdealPointsSubgroupIso n I A).hom q =
      ULift.up (quotientPointsMulEquiv n I A q) :=
  rfl

/-- The inverse component removes the universe lift and applies the inverse pointwise
matrix-subgroup equivalence. -/
@[simp]
theorem hopfIdealPointsSubgroupIso_inv_apply (A : CommAlgCat.{w} R)
    (g : ULift.{u, w} (hopfIdealPointsSubgroup n I A)) :
    CategoryTheory.ConcreteCategory.hom (hopfIdealPointsSubgroupIso n I A).inv g =
      (quotientPointsMulEquiv n I A).symm g.down :=
  rfl

/-- The quotient coordinate Hopf algebra represents the matrix point subgroup functor cut out by
the Hopf ideal. -/
noncomputable def hopfIdealPointsSubgroupNatIso :
    HopfAlgebra.pointsFunctor
        (R := R) (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I) ≅
      hopfIdealPointsSubgroupFunctor n I :=
  NatIso.ofComponents
    (hopfIdealPointsSubgroupIso n I)
    (by
      intro A B f
      ext q
      apply ULift.ext
      exact (quotientPointsMulEquiv_mapValue n I f q).symm)

/-- After transport along `hopfIdealPointsSubgroupFunctor_obj`, the forward component of the
representing natural isomorphism is the pointwise matrix-subgroup equivalence. -/
@[simp]
theorem hopfIdealPointsSubgroupNatIso_hom_app_apply (A : CommAlgCat.{w} R)
    (q : HopfAlgebra.points
      (R := R) (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I) A) :
    (eqToHom (hopfIdealPointsSubgroupFunctor_obj n I A)
      ((hopfIdealPointsSubgroupNatIso n I).hom.app A q)).down =
        quotientPointsMulEquiv n I A q := by
  exact congrArg ULift.down (hopfIdealPointsSubgroupIso_hom_apply n I A q)

/-- After transport back along `hopfIdealPointsSubgroupFunctor_obj`, the inverse component of the
representing natural isomorphism is the inverse pointwise matrix-subgroup equivalence. -/
@[simp]
theorem hopfIdealPointsSubgroupNatIso_inv_app_apply (A : CommAlgCat.{w} R)
    (g : ULift.{u, w} (hopfIdealPointsSubgroup n I A)) :
    (hopfIdealPointsSubgroupNatIso n I).inv.app A
        (eqToHom (hopfIdealPointsSubgroupFunctor_obj n I A).symm g) =
      (quotientPointsMulEquiv n I A).symm g.down := by
  exact hopfIdealPointsSubgroupIso_inv_apply n I A g

end

end TauCeti.GeneralLinear
