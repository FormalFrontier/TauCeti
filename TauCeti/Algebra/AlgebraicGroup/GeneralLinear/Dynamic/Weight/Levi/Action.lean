/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Normal
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
  -- Unwrap the category object and the equality transport defining `leviFunctor_obj` so
  -- the pointwise comparison lemma for `weightLeviPointsIso` matches the goal.
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
  -- Unwrap the category object and the equality transport defining `unipotentFunctor_obj`
  -- so the pointwise comparison lemma for `weightUnipotentPointsIso` matches the goal.
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

/-- The represented conjugation action on categorical quotient points is conjugation after
transporting both quotient-point groups to their dynamic models. -/
theorem representedWeightLeviConjugation_apply (w : Fin N → ℤ)
    (A : CommAlgCat.{u} R)
    (z : op A ⟶ CommHopfAlgCat.grpObj
      (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
        (weightLeviInParabolicHopfIdeal R w)))
    (g : op A ⟶ CommHopfAlgCat.grpObj
      (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
        (weightUnipotentInParabolicHopfIdeal R w))) :
    representedWeightLeviConjugation R w A
        (weightLeviInParabolicPointsMulEquiv R w A
          (CommHopfAlgCat.grpObjPointsMulEquiv _ (op A) z))
        (weightUnipotentInParabolicPointsMulEquiv R w A
          (CommHopfAlgCat.grpObjPointsMulEquiv _ (op A) g)) =
      weightUnipotentInParabolicPointsMulEquiv R w A
        (CommHopfAlgCat.grpObjPointsMulEquiv _ (op A)
          ((CommHopfAlgCat.quotientNormalConjugation
            (weightParabolicCoordinateHopfAlgebra R w)
            (weightUnipotentInParabolicHopfIdeal R w)
            (weightLeviInParabolicHopfIdeal R w)
            (isNormal_weightUnipotentInParabolicHopfIdeal R w)).toMulAutHom (op A) z g)) := by
  unfold representedWeightLeviConjugation
  simp only [MulEquiv.toMonoidHom_eq_coe, MulEquiv.coe_monoidHom_trans,
    MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply,
    MulEquiv.symm_apply_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_trans_apply, GrpObj.Action.toMulAutHom_apply,
    EmbeddingLike.apply_eq_iff_eq]
  rw [weightRelativeLeviConjugation]

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
    MulEquiv.trans_apply, MulEquiv.symm_trans_apply, GrpObj.Action.toMulAutHom_apply]
  apply Subtype.ext
  rw [Cocharacter.coe_leviConjugation_apply]
  rw [coe_weightUnipotentInParabolicPointsMulEquiv_apply,
    weightRelativeLeviConjugation,
    CommHopfAlgCat.quotientPointsHom_quotientNormalConjugation_apply]
  simp only [map_mul, map_inv]
  rw [← coe_weightLeviInParabolicPointsMulEquiv_apply,
    ← coe_weightUnipotentInParabolicPointsMulEquiv_apply]
  simp

end

end TauCeti.GeneralLinear.Dynamic
