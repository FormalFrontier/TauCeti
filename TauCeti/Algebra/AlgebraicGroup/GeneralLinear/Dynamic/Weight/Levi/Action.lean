/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Levi.Decomposition
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Product.Basic

/-!
# The represented conjugation action in a weight parabolic

Let `P(w)`, `U(w)`, and `L(w)` be the represented weight parabolic, unipotent subgroup, and
Levi subgroup of `GL_N`. Normality of `U(w)` in `P(w)` supplies a categorical conjugation action
of `L(w)` on `U(w)`. This file transports that action through the coordinate identifications of
the two relative quotient subgroups and proves that it is exactly the dynamic conjugation action
used in the pointwise Levi decomposition.

Thus the categorical semidirect product constructed from the two closed subgroup schemes has
the same multiplication law on algebra-valued points as the dynamic semidirect product.

## Main declarations

* `TauCeti.GeneralLinear.Dynamic.weightLeviInParabolicPointsMulEquiv`: relative Levi quotient
  points are dynamic Levi points.
* `TauCeti.GeneralLinear.Dynamic.weightUnipotentInParabolicPointsMulEquiv`: relative unipotent
  quotient points are dynamic unipotent points.
* `TauCeti.GeneralLinear.Dynamic.representedWeightLeviConjugation`: categorical conjugation,
  evaluated after transport to dynamic points.
* `TauCeti.GeneralLinear.Dynamic.representedWeightLeviConjugation_eq_dynamic`: transported
  categorical conjugation is the dynamic Levi action.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.

This advances the dynamic route to parabolic subgroups and Levi decomposition in Layer 7,
"Structure theory", of the ReductiveGroups roadmap. It supplies the action comparison needed
to identify the represented categorical semidirect product with the pointwise dynamic one.
-/

public section

open CategoryTheory Opposite WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.GeneralLinear.Dynamic

universe u

noncomputable section

variable (R : Type u) [CommRing R] {N : ℕ}

/-- Points of the relative Levi quotient inside the weight parabolic are canonically the
dynamic Levi points of the weight cocharacter. -/
noncomputable def weightLeviInParabolicPointsMulEquiv (w : Fin N → ℤ)
    (A : CommAlgCat.{u} R) :
    HopfAlgebra.points (R := R)
        (H := CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
          (weightLeviInParabolicHopfIdeal R w)) A ≃*
      Cocharacter.levi A (weightCocharacter (R := R) w) :=
  (AlgHom.mapDomainMulEquiv (A := A)
      (CommHopfAlgCat.ofIso (weightLeviInParabolicCoordinateIso R w))).trans
    ((weightLeviPointsIso R w).app A).groupIsoToMulEquiv

/-- Points of the relative unipotent quotient inside the weight parabolic are canonically the
dynamic unipotent points of the weight cocharacter. -/
noncomputable def weightUnipotentInParabolicPointsMulEquiv (w : Fin N → ℤ)
    (A : CommAlgCat.{u} R) :
    HopfAlgebra.points (R := R)
        (H := CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
          (weightUnipotentInParabolicHopfIdeal R w)) A ≃*
      Cocharacter.unipotent A (weightCocharacter (R := R) w) :=
  (AlgHom.mapDomainMulEquiv (A := A)
      (CommHopfAlgCat.ofIso (weightUnipotentInParabolicCoordinateIso R w))).trans
    ((weightUnipotentPointsIso R w).app A).groupIsoToMulEquiv

/-- The relative Levi point equivalence preserves the underlying point of the ambient general
linear group. -/
@[simp]
theorem coe_weightLeviInParabolicPointsMulEquiv_apply (w : Fin N → ℤ)
    (A : CommAlgCat.{u} R)
    (z : HopfAlgebra.points (R := R)
      (H := CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
        (weightLeviInParabolicHopfIdeal R w)) A) :
    ((weightLeviInParabolicPointsMulEquiv R w A z :
        Cocharacter.levi A (weightCocharacter (R := R) w)) :
      HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N) A) =
      CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
        (weightParabolicDefiningHopfIdeal R w) A
        (CommHopfAlgCat.quotientPointsHom (weightParabolicCoordinateHopfAlgebra R w)
          (weightLeviInParabolicHopfIdeal R w) A z) := by
  rcases A with ⟨A⟩
  change (((eqToHom (Cocharacter.leviFunctor_obj
      (weightCocharacter (R := R) w) (CommAlgCat.of R A)))
    ((weightLeviPointsIso R w).hom.app (CommAlgCat.of R A)
      (AlgHom.mapDomainMulEquiv
        (A := CommAlgCat.of R A)
        (CommHopfAlgCat.ofIso (weightLeviInParabolicCoordinateIso R w)) z)) :
      Cocharacter.levi (CommAlgCat.of R A) (weightCocharacter (R := R) w)) :
        HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N)
          (CommAlgCat.of R A)) = _
  rw [coe_weightLeviPointsIso_hom_app_apply, AlgHom.mapDomainMulEquiv_apply]
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro x
  rw [CommHopfAlgCat.quotientPointsHom_apply_apply,
    CommHopfAlgCat.quotientPointsHom_apply_apply, AlgHom.mapDomain_apply_apply,
    CommHopfAlgCat.quotientPointsHom_apply_apply]
  have h := congrArg
    (fun f : coordinateHopfAlgebra R N ⟶
        CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
          (weightLeviInParabolicHopfIdeal R w) ↦ f.hom x)
    (mkQuotient_weightLevi_comp_weightLeviInParabolicCoordinateIso_hom R w)
  rw [_root_.CommHopfAlgCat.comp_apply, _root_.CommHopfAlgCat.comp_apply,
    CommHopfAlgCat.mkQuotient_apply, CommHopfAlgCat.mkQuotient_apply,
    weightParabolicCoordinateMap_apply] at h
  exact congrArg z.ofConv h

/-- The relative unipotent point equivalence preserves the underlying point of the ambient
general linear group. -/
@[simp]
theorem coe_weightUnipotentInParabolicPointsMulEquiv_apply (w : Fin N → ℤ)
    (A : CommAlgCat.{u} R)
    (g : HopfAlgebra.points (R := R)
      (H := CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
        (weightUnipotentInParabolicHopfIdeal R w)) A) :
    ((weightUnipotentInParabolicPointsMulEquiv R w A g :
        Cocharacter.unipotent A (weightCocharacter (R := R) w)) :
      HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N) A) =
      CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
        (weightParabolicDefiningHopfIdeal R w) A
        (CommHopfAlgCat.quotientPointsHom (weightParabolicCoordinateHopfAlgebra R w)
          (weightUnipotentInParabolicHopfIdeal R w) A g) := by
  rcases A with ⟨A⟩
  change (((eqToHom (Cocharacter.unipotentFunctor_obj
      (weightCocharacter (R := R) w) (CommAlgCat.of R A)))
    ((weightUnipotentPointsIso R w).hom.app (CommAlgCat.of R A)
      (AlgHom.mapDomainMulEquiv
        (A := CommAlgCat.of R A)
        (CommHopfAlgCat.ofIso (weightUnipotentInParabolicCoordinateIso R w)) g)) :
      Cocharacter.unipotent (CommAlgCat.of R A) (weightCocharacter (R := R) w)) :
        HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N)
          (CommAlgCat.of R A)) = _
  rw [coe_weightUnipotentPointsIso_hom_app_apply, AlgHom.mapDomainMulEquiv_apply]
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro x
  rw [CommHopfAlgCat.quotientPointsHom_apply_apply,
    CommHopfAlgCat.quotientPointsHom_apply_apply, AlgHom.mapDomain_apply_apply,
    CommHopfAlgCat.quotientPointsHom_apply_apply]
  have h := congrArg
    (fun f : coordinateHopfAlgebra R N ⟶
        CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
          (weightUnipotentInParabolicHopfIdeal R w) ↦ f.hom x)
    (mkQuotient_weightUnipotent_comp_weightUnipotentInParabolicCoordinateIso_hom R w)
  rw [_root_.CommHopfAlgCat.comp_apply, _root_.CommHopfAlgCat.comp_apply,
    CommHopfAlgCat.mkQuotient_apply, CommHopfAlgCat.mkQuotient_apply,
    weightParabolicCoordinateMap_apply] at h
  exact congrArg g.ofConv h

private theorem quotientPointsHom_quotientNormalConjugation_apply
    (H : _root_.CommHopfAlgCat.{u} R) (I J : HopfIdeal R H) (hI : I.IsNormal)
    (A : CommAlgCat.{u} R)
    (z : HopfAlgebra.points (R := R) (H := CommHopfAlgCat.quotient H J) A)
    (g : HopfAlgebra.points (R := R) (H := CommHopfAlgCat.quotient H I) A) :
    CommHopfAlgCat.quotientPointsHom H I A
        (CommHopfAlgCat.grpObjPointsMulEquiv (CommHopfAlgCat.quotient H I) (op A)
          ((CommHopfAlgCat.quotientNormalConjugation H I J hI).act
            ((CommHopfAlgCat.grpObjPointsMulEquiv
              (CommHopfAlgCat.quotient H J) (op A)).symm z)
            ((CommHopfAlgCat.grpObjPointsMulEquiv
              (CommHopfAlgCat.quotient H I) (op A)).symm g))) =
      CommHopfAlgCat.quotientPointsHom H J A z *
        CommHopfAlgCat.quotientPointsHom H I A g *
          (CommHopfAlgCat.quotientPointsHom H J A z)⁻¹ := by
  let i := CommHopfAlgCat.quotientGrpObjInclusion H I
  let j := CommHopfAlgCat.quotientGrpObjInclusion H J
  let z' := (CommHopfAlgCat.grpObjPointsMulEquiv
    (CommHopfAlgCat.quotient H J) (op A)).symm z
  let g' := (CommHopfAlgCat.grpObjPointsMulEquiv
    (CommHopfAlgCat.quotient H I) (op A)).symm g
  let _ : IsMonHom.Normal i :=
    (CommHopfAlgCat.quotientGrpObjInclusion_normal_iff H I).2 hI
  have hact :
      (CommHopfAlgCat.quotientNormalConjugation H I J hI).act z' g' ≫ i =
        (z' ≫ j) * (g' ≫ i) * (z' ≫ j)⁻¹ := by
    change (GrpObj.Action.normalConjugation i j).act z' g' ≫ i = _
    rw [GrpObj.Action.normalConjugation_act, Category.assoc]
    exact TauCeti.lift_normalConjugation_comp i (z' ≫ j) g'
  have hpoints := congrArg (CommHopfAlgCat.grpObjPointsMulEquiv H (op A)) hact
  simp only [i, j, z', g', map_mul, map_inv] at hpoints
  rw [CommHopfAlgCat.grpObjPointsMulEquiv_comp_quotientGrpObjInclusion,
    CommHopfAlgCat.grpObjPointsMulEquiv_comp_quotientGrpObjInclusion,
    CommHopfAlgCat.grpObjPointsMulEquiv_comp_quotientGrpObjInclusion] at hpoints
  simpa only [MulEquiv.apply_symm_apply] using hpoints

/-- Conjugation of the relative Levi quotient on the normal relative unipotent quotient. -/
private noncomputable def weightRelativeLeviConjugation (w : Fin N → ℤ) :
    GrpObj.Action
      (CommHopfAlgCat.grpObj
        (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
          (weightLeviInParabolicHopfIdeal R w)))
      (CommHopfAlgCat.grpObj
        (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
          (weightUnipotentInParabolicHopfIdeal R w))) :=
  CommHopfAlgCat.quotientNormalConjugation (weightParabolicCoordinateHopfAlgebra R w)
    (weightUnipotentInParabolicHopfIdeal R w) (weightLeviInParabolicHopfIdeal R w)
    (isNormal_weightUnipotentInParabolicHopfIdeal R w)

/-- Evaluation of represented relative conjugation after transport to dynamic points. -/
private noncomputable def representedWeightLeviConjugationApply (w : Fin N → ℤ)
    (A : CommAlgCat.{u} R)
    (z : Cocharacter.levi A (weightCocharacter (R := R) w))
    (g : Cocharacter.unipotent A (weightCocharacter (R := R) w)) :
    Cocharacter.unipotent A (weightCocharacter (R := R) w) := by
  letI : GrpObj (CommHopfAlgCat.grpObj
      (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
        (weightLeviInParabolicHopfIdeal R w))) := CommAlgCat.grpObjOpOf
  letI : GrpObj (CommHopfAlgCat.grpObj
      (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
        (weightUnipotentInParabolicHopfIdeal R w))) := CommAlgCat.grpObjOpOf
  exact weightUnipotentInParabolicPointsMulEquiv R w A
    ((CommHopfAlgCat.grpObjPointsMulEquiv
      (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
        (weightUnipotentInParabolicHopfIdeal R w)) (op A))
      ((weightRelativeLeviConjugation R w).act
        ((CommHopfAlgCat.grpObjPointsMulEquiv
          (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
            (weightLeviInParabolicHopfIdeal R w)) (op A)).symm
          ((weightLeviInParabolicPointsMulEquiv R w A).symm z))
        ((CommHopfAlgCat.grpObjPointsMulEquiv
          (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
            (weightUnipotentInParabolicHopfIdeal R w)) (op A)).symm
          ((weightUnipotentInParabolicPointsMulEquiv R w A).symm g))))

/-- The categorical conjugation action of the represented relative Levi subgroup on the
represented relative unipotent subgroup, transported to dynamic points. -/
noncomputable def representedWeightLeviConjugation (w : Fin N → ℤ)
    (A : CommAlgCat.{u} R) :
    Cocharacter.levi A (weightCocharacter (R := R) w) →*
      MulAut (Cocharacter.unipotent A (weightCocharacter (R := R) w)) := by
  letI : GrpObj (CommHopfAlgCat.grpObj
      (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
        (weightLeviInParabolicHopfIdeal R w))) := CommAlgCat.grpObjOpOf
  letI : GrpObj (CommHopfAlgCat.grpObj
      (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
        (weightUnipotentInParabolicHopfIdeal R w))) := CommAlgCat.grpObjOpOf
  exact (MulAut.congr
    ((CommHopfAlgCat.grpObjPointsMulEquiv
      (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
        (weightUnipotentInParabolicHopfIdeal R w)) (op A)).trans
        (weightUnipotentInParabolicPointsMulEquiv R w A))).toMonoidHom.comp
    ((weightRelativeLeviConjugation R w).toMulAutHom (op A) |>.comp
      ((weightLeviInParabolicPointsMulEquiv R w A).symm.trans
        (CommHopfAlgCat.grpObjPointsMulEquiv
          (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
            (weightLeviInParabolicHopfIdeal R w)) (op A)).symm).toMonoidHom)

/-- The categorical conjugation action of the represented Levi subgroup is exactly the dynamic
Levi conjugation action on every commutative algebra of points. -/
@[simp]
theorem representedWeightLeviConjugation_eq_dynamic (w : Fin N → ℤ)
    (A : CommAlgCat.{u} R) :
    representedWeightLeviConjugation R w A =
      Cocharacter.leviConjugation A (weightCocharacter (R := R) w) := by
  apply MonoidHom.ext
  intro z
  apply MulEquiv.ext
  intro g
  unfold representedWeightLeviConjugation
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply, GrpObj.Action.toMulAutHom_apply]
  change representedWeightLeviConjugationApply R w A z g = _
  apply Subtype.ext
  rw [Cocharacter.coe_leviConjugation_apply]
  unfold representedWeightLeviConjugationApply
  rw [coe_weightUnipotentInParabolicPointsMulEquiv_apply,
    weightRelativeLeviConjugation,
    quotientPointsHom_quotientNormalConjugation_apply]
  simp only [map_mul, map_inv]
  rw [← coe_weightLeviInParabolicPointsMulEquiv_apply,
    ← coe_weightUnipotentInParabolicPointsMulEquiv_apply]
  simp

end

end TauCeti.GeneralLinear.Dynamic
