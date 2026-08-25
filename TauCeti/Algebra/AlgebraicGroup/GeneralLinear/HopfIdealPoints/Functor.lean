/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Basic
public import TauCeti.Algebra.Group.Subgroup.Map

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

* `TauCeti.GeneralLinear.hopfIdealPointsSubgroupMulEquiv`: the pointwise group equivalence between
  quotient Hopf-algebra points and the matrix subgroup cut out by the ideal.
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

private theorem map_pointsMulEquiv_quotientPointsSubgroup_eq (A : CommAlgCat.{w} R) :
    (CommHopfAlgCat.quotientPointsSubgroup
        (coordinateHopfAlgebra R n) I A).map
      (pointsMulEquiv (R := R) (A := A) n :
        WithConv (coordinateHopfAlgebra R n →ₐ[R] A) →*
          Matrix.GeneralLinearGroup (Fin n) A) =
      hopfIdealPointsSubgroup n I A := by
  ext g
  rw [← (pointsMulEquiv n).toMonoidHom_eq_coe, Subgroup.mem_map_equiv,
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff, mem_hopfIdealPointsSubgroup_iff]

/-- Quotient Hopf-algebra points are multiplicatively equivalent to the matrix subgroup cut out by
the Hopf ideal. The equivalence first includes a quotient point among the ambient Hopf-algebra
points, then reads that point as an invertible matrix. -/
noncomputable def hopfIdealPointsSubgroupMulEquiv (A : CommAlgCat.{w} R) :
    HopfAlgebra.points
        (R := R) (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I) A ≃*
      hopfIdealPointsSubgroup n I A :=
  (CommHopfAlgCat.quotientPointsSubgroupIso
      (coordinateHopfAlgebra R n) I A).groupIsoToMulEquiv.trans
    (Subgroup.congrOfMapEq (pointsMulEquiv n)
      (map_pointsMulEquiv_quotientPointsSubgroup_eq n I A))

/-- Internally, the matrix-subgroup equivalence first forms the cut-out ambient subgroup point and
then restricts the general-linear point equivalence to it. -/
private theorem hopfIdealPointsSubgroupMulEquiv_apply_eq (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points
      (R := R) (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I) A) :
    hopfIdealPointsSubgroupMulEquiv n I A f =
      Subgroup.congrOfMapEq (pointsMulEquiv n)
        (map_pointsMulEquiv_quotientPointsSubgroup_eq n I A)
        ((CommHopfAlgCat.quotientPointsSubgroupIso (coordinateHopfAlgebra R n) I A).hom f) :=
  (rfl)

/-- A quotient point, viewed through `hopfIdealPointsSubgroupMulEquiv`, is its included ambient
point read as an invertible matrix. -/
@[simp]
theorem coe_hopfIdealPointsSubgroupMulEquiv_apply (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points
      (R := R) (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I) A) :
    (hopfIdealPointsSubgroupMulEquiv n I A f : Matrix.GeneralLinearGroup (Fin n) A) =
      pointsMulEquiv n
        (CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R n) I A f) := by
  rw [hopfIdealPointsSubgroupMulEquiv_apply_eq, Subgroup.coe_congrOfMapEq_apply,
    CommHopfAlgCat.quotientPointsSubgroupIso_hom_apply]

/-- Including the ambient Hopf-algebra point underlying the inverse matrix-subgroup equivalence
recovers the point corresponding to the underlying matrix. -/
@[simp]
theorem quotientPointsHom_hopfIdealPointsSubgroupMulEquiv_symm
    (A : CommAlgCat.{w} R) (g : hopfIdealPointsSubgroup n I A) :
    CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R n) I A
        ((hopfIdealPointsSubgroupMulEquiv n I A).symm g) =
      (pointsMulEquiv (R := R) n).symm
        (g : Matrix.GeneralLinearGroup (Fin n) A) := by
  apply (pointsMulEquiv (R := R) n).injective
  rw [MulEquiv.apply_symm_apply, ← coe_hopfIdealPointsSubgroupMulEquiv_apply,
    MulEquiv.apply_symm_apply]

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
@[simp]
theorem hopfIdealPointsSubgroupFunctor_obj (A : CommAlgCat.{w} R) :
    (hopfIdealPointsSubgroupFunctor n I).obj A =
      GrpCat.of (ULift.{u, w} (hopfIdealPointsSubgroup n I A)) :=
  (rfl)

/-- The morphism part of the Hopf-ideal matrix-points functor is the universe lift of the restricted
entrywise matrix map. -/
@[simp]
theorem hopfIdealPointsSubgroupFunctor_map {A B : CommAlgCat.{w} R} (f : A ⟶ B) :
    (hopfIdealPointsSubgroupFunctor n I).map f =
      eqToHom (hopfIdealPointsSubgroupFunctor_obj n I A) ≫
        GrpCat.ofHom
          (MulEquiv.ulift.symm.toMonoidHom.comp
            ((mapHopfIdealPointsSubgroup n I f.hom).comp
              MulEquiv.ulift.toMonoidHom)) ≫
        eqToHom (hopfIdealPointsSubgroupFunctor_obj n I B).symm :=
  (rfl)

/-- The morphism part of the Hopf-ideal matrix-points functor applies the value-algebra morphism
entrywise after removing the universe lift. -/
@[simp]
theorem hopfIdealPointsSubgroupFunctor_map_apply {A B : CommAlgCat.{w} R} (f : A ⟶ B)
    (g : ULift.{u, w} (hopfIdealPointsSubgroup n I A)) :
    (eqToHom (hopfIdealPointsSubgroupFunctor_obj n I B)
      (eqToHom (hopfIdealPointsSubgroupFunctor_obj n I B).symm
        (MulEquiv.ulift.symm
          (mapHopfIdealPointsSubgroup n I f.hom
            (MulEquiv.ulift
              (eqToHom (hopfIdealPointsSubgroupFunctor_obj n I A)
                (eqToHom (hopfIdealPointsSubgroupFunctor_obj n I A).symm g))))))).down =
      mapHopfIdealPointsSubgroup n I f.hom g.down :=
  (rfl)

/-- The matrix-subgroup equivalence is natural in the value algebra. -/
@[simp]
theorem hopfIdealPointsSubgroupMulEquiv_mapPoints {A B : CommAlgCat.{w} R} (f : A ⟶ B)
    (q : HopfAlgebra.points
      (R := R) (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I) A) :
    hopfIdealPointsSubgroupMulEquiv n I B
        (HopfAlgebra.mapPoints
          (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I) f q) =
      mapHopfIdealPointsSubgroup n I f.hom (hopfIdealPointsSubgroupMulEquiv n I A q) := by
  apply Subtype.ext
  rw [coe_mapHopfIdealPointsSubgroup, coe_hopfIdealPointsSubgroupMulEquiv_apply,
    coe_hopfIdealPointsSubgroupMulEquiv_apply]
  rw [← CommHopfAlgCat.mapPoints_quotientPointsHom]
  exact pointsMulEquiv_mapValue n f.hom
    (CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R n) I A q)

/-- The quotient coordinate Hopf algebra represents the matrix point subgroup functor cut out by
the Hopf ideal. -/
noncomputable def hopfIdealPointsSubgroupNatIso :
    HopfAlgebra.pointsFunctor
        (R := R) (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I) ≅
      hopfIdealPointsSubgroupFunctor n I :=
  NatIso.ofComponents
    (fun A ↦ ((hopfIdealPointsSubgroupMulEquiv n I A).trans
      (MulEquiv.ulift.symm : _ ≃* ULift.{u, w} (hopfIdealPointsSubgroup n I A))).toGrpIso)
    (by
      intro A B f
      ext q
      apply ULift.ext
      exact hopfIdealPointsSubgroupMulEquiv_mapPoints n I f q)

/-- After transport along `hopfIdealPointsSubgroupFunctor_obj`, the forward component of the
representing natural isomorphism is the pointwise matrix-subgroup equivalence. -/
@[simp]
theorem hopfIdealPointsSubgroupNatIso_hom_app_apply (A : CommAlgCat.{w} R)
    (q : HopfAlgebra.points
      (R := R) (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I) A) :
    (eqToHom (hopfIdealPointsSubgroupFunctor_obj n I A)
      ((hopfIdealPointsSubgroupNatIso n I).hom.app A q)).down =
        hopfIdealPointsSubgroupMulEquiv n I A q :=
  (rfl)

/-- After transport back along `hopfIdealPointsSubgroupFunctor_obj`, the inverse component of the
representing natural isomorphism is the inverse pointwise matrix-subgroup equivalence. -/
@[simp]
theorem hopfIdealPointsSubgroupNatIso_inv_app_apply (A : CommAlgCat.{w} R)
    (g : ULift.{u, w} (hopfIdealPointsSubgroup n I A)) :
    (hopfIdealPointsSubgroupNatIso n I).inv.app A
        (eqToHom (hopfIdealPointsSubgroupFunctor_obj n I A).symm g) =
      (hopfIdealPointsSubgroupMulEquiv n I A).symm g.down :=
  (rfl)

end

end TauCeti.GeneralLinear
