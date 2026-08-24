/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Functor
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Naturality

/-!
# Representability of dynamic weight parabolics

The weight-parabolic subgroup scheme of `GL_N` represents the dynamic parabolic attached to the
cocharacter `t ↦ diag(t ^ w i)`. On points, both descriptions say exactly that the `(i,j)` entry
vanishes whenever `w i < w j`.

## Main declarations

* `TauCeti.GeneralLinear.Dynamic.mem_weightParabolicDefiningPointsSubgroup_iff`: membership in
  the Hopf-ideal cut-out agrees with dynamic-parabolic membership.
* `TauCeti.GeneralLinear.Dynamic.weightParabolicPointsIso`: the natural representing
  isomorphism.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.

This completes representability of the weight-cocharacter parabolic in the dynamic route of
Layer 7, "Structure theory", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear.Dynamic

universe u v

variable (R : Type u) [CommRing R] {N : ℕ}

section Points

variable {A : Type v} [CommRing A] [Algebra R A]

/-- The Hopf-ideal cut-out is exactly the dynamic parabolic of the weight cocharacter. -/
theorem mem_weightParabolicDefiningPointsSubgroup_iff (w : Fin N → ℤ)
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N)
      (CommAlgCat.of R A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R N)
        (weightParabolicDefiningHopfIdeal R w) (CommAlgCat.of R A) ↔
      g ∈ Cocharacter.parabolic (CommAlgCat.of R A) (weightCocharacter (R := R) w) := by
  rw [mem_weightParabolicDefiningPointsSubgroup_iff_blockTriangular,
    mem_parabolic_weightCocharacter_iff]

/-- Identify the cut-out ambient point subgroup with the dynamic parabolic point subgroup. -/
private noncomputable def weightParabolicPointsSubgroupMulEquiv (w : Fin N → ℤ) :
    CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R N)
        (weightParabolicDefiningHopfIdeal R w) (CommAlgCat.of R A) ≃*
      Cocharacter.parabolic (CommAlgCat.of R A) (weightCocharacter (R := R) w) :=
  MulEquiv.subgroupCongr <| Subgroup.ext fun g ↦
    mem_weightParabolicDefiningPointsSubgroup_iff R w g

private theorem weightParabolicPointsSubgroupMulEquiv_natural (w : Fin N → ℤ)
    {B : CommAlgCat.{v} R} (phi : CommAlgCat.of R A ⟶ B)
    (g : CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R N)
      (weightParabolicDefiningHopfIdeal R w) (CommAlgCat.of R A)) :
    weightParabolicPointsSubgroupMulEquiv R w
        (CommHopfAlgCat.mapQuotientPointsSubgroup (coordinateHopfAlgebra R N)
          (weightParabolicDefiningHopfIdeal R w) phi g) =
      Cocharacter.mapParabolic (weightCocharacter (R := R) w) phi
        (weightParabolicPointsSubgroupMulEquiv R w g) := by
  apply Subtype.ext
  calc
    _ = ((CommHopfAlgCat.mapQuotientPointsSubgroup (coordinateHopfAlgebra R N)
          (weightParabolicDefiningHopfIdeal R w) phi g) :
        HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N) B) :=
      MulEquiv.subgroupCongr_apply _ _
    _ = HopfAlgebra.mapPoints (H := coordinateHopfAlgebra R N) phi g :=
      CommHopfAlgCat.coe_mapQuotientPointsSubgroup_apply _ _ _ _
    _ = AlgHom.mapValue phi.hom g := rfl
    _ = AlgHom.mapValue phi.hom
        ((weightParabolicPointsSubgroupMulEquiv R w g :
            Cocharacter.parabolic (CommAlgCat.of R A) (weightCocharacter (R := R) w)) :
          HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N)
            (CommAlgCat.of R A)) := by
      congr 1
    _ = ((Cocharacter.mapParabolic (weightCocharacter (R := R) w) phi
          (weightParabolicPointsSubgroupMulEquiv R w g) :
            Cocharacter.parabolic B (weightCocharacter (R := R) w)) :
        HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N) B) :=
      (Cocharacter.coe_mapParabolic_apply _ _ _).symm

end Points

/-- The cut-out subgroup functor is naturally the dynamic parabolic functor. -/
private noncomputable def weightParabolicSubgroupPointsIso (w : Fin N → ℤ) :
    CommHopfAlgCat.quotientPointsSubgroupFunctor (R := R) (coordinateHopfAlgebra R N)
        (weightParabolicDefiningHopfIdeal R w) ≅
      Cocharacter.parabolicFunctor (weightCocharacter (R := R) w) :=
  NatIso.ofComponents
    (fun _ ↦ (weightParabolicPointsSubgroupMulEquiv R w).toGrpIso)
    (by
      intro A B phi
      ext g
      exact weightParabolicPointsSubgroupMulEquiv_natural R w phi g)

/-- The weight-parabolic coordinate Hopf algebra represents the dynamic parabolic functor of the
weight cocharacter, naturally in the commutative value algebra. -/
noncomputable def weightParabolicPointsIso (w : Fin N → ℤ) :
    HopfAlgebra.pointsFunctor (R := R) (H := weightParabolicCoordinateHopfAlgebra R w) ≅
      Cocharacter.parabolicFunctor (weightCocharacter (R := R) w) :=
  (CommHopfAlgCat.quotientPointsSubgroupNatIso (coordinateHopfAlgebra R N)
      (weightParabolicDefiningHopfIdeal R w)).trans
    (weightParabolicSubgroupPointsIso R w)

/-- The ambient point underlying the represented dynamic-parabolic point is induced by the
quotient coordinate map. -/
@[simp]
theorem coe_weightParabolicPointsIso_hom_app_apply (w : Fin N → ℤ)
    {A : Type v} [CommRing A] [Algebra R A]
    (f : HopfAlgebra.points
      (R := R) (H := weightParabolicCoordinateHopfAlgebra R w) (CommAlgCat.of R A)) :
    (((eqToHom (Cocharacter.parabolicFunctor_obj
        (weightCocharacter (R := R) w) (CommAlgCat.of R A)))
      ((weightParabolicPointsIso R w).hom.app (CommAlgCat.of R A) f) :
        Cocharacter.parabolic (CommAlgCat.of R A) (weightCocharacter (R := R) w)) :
      HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N) (CommAlgCat.of R A)) =
      CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
        (weightParabolicDefiningHopfIdeal R w) (CommAlgCat.of R A) f := by
  have hcomponent := CommHopfAlgCat.quotientPointsSubgroupNatIso_hom_app_apply
    (coordinateHopfAlgebra R N) (weightParabolicDefiningHopfIdeal R w)
    (CommAlgCat.of R A) f
  unfold weightParabolicPointsIso
  exact congrArg
    (fun g => ((weightParabolicPointsSubgroupMulEquiv R w g :
        Cocharacter.parabolic (CommAlgCat.of R A) (weightCocharacter (R := R) w)) :
      HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N) (CommAlgCat.of R A)))
    hcomponent

/-- Applying the quotient inclusion to the inverse representing isomorphism recovers the ambient
dynamic-parabolic point. -/
@[simp]
theorem quotientPointsHom_weightParabolicPointsIso_inv_app_apply (w : Fin N → ℤ)
    {A : Type v} [CommRing A] [Algebra R A]
    (g : Cocharacter.parabolic (CommAlgCat.of R A) (weightCocharacter (R := R) w)) :
    CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
        (weightParabolicDefiningHopfIdeal R w) (CommAlgCat.of R A)
        ((weightParabolicPointsIso R w).inv.app (CommAlgCat.of R A) g) = g.1 := by
  let f := (weightParabolicPointsIso R w).inv.app (CommAlgCat.of R A) g
  calc
    CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
        (weightParabolicDefiningHopfIdeal R w) (CommAlgCat.of R A) f =
      (((eqToHom (Cocharacter.parabolicFunctor_obj
          (weightCocharacter (R := R) w) (CommAlgCat.of R A)))
        ((weightParabolicPointsIso R w).hom.app (CommAlgCat.of R A) f) :
          Cocharacter.parabolic (CommAlgCat.of R A) (weightCocharacter (R := R) w)) :
          HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N)
            (CommAlgCat.of R A)) :=
      (coe_weightParabolicPointsIso_hom_app_apply R w f).symm
    _ = g.1 := by
      have hinv := CategoryTheory.Iso.inv_hom_id_apply
        ((weightParabolicPointsIso R w).app (CommAlgCat.of R A))
        (eqToHom (Cocharacter.parabolicFunctor_obj
          (weightCocharacter (R := R) w) (CommAlgCat.of R A)).symm g)
      exact congrArg Subtype.val hinv

end TauCeti.GeneralLinear.Dynamic
