/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Levi
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Functor
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Naturality

/-!
# Representability of dynamic weight Levis

The weight-Levi subgroup scheme of `GL_N` represents the dynamic Levi attached to the
cocharacter `t ↦ diag(t ^ w i)`. On points, both descriptions say exactly that the `(i,j)`
entry vanishes whenever `w i ≠ w j`.

The construction and its naturality follow the representing interface for the weight parabolic
in `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Parabolic`, with the Levi cut out
as the intersection of the two opposite weight parabolics.

## Main declarations

* `TauCeti.GeneralLinear.Dynamic.mem_weightLeviDefiningPointsSubgroup_iff`: membership in the
  Hopf-ideal cut-out agrees with dynamic-Levi membership.
* `TauCeti.GeneralLinear.Dynamic.weightLeviPointsIso`: the natural representing isomorphism.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.

This completes representability of the weight-cocharacter Levi in the dynamic route of Layer 7,
"Structure theory", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear.Dynamic

universe u v

variable (R : Type u) [CommRing R] {N : ℕ}

section Points

variable {A : Type v} [CommRing A] [Algebra R A]

/-- The Hopf-ideal cut-out is exactly the dynamic Levi of the weight cocharacter. -/
theorem mem_weightLeviDefiningPointsSubgroup_iff (w : Fin N → ℤ)
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N)
      (CommAlgCat.of R A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R N)
        (weightLeviDefiningHopfIdeal R w) (CommAlgCat.of R A) ↔
      g ∈ Cocharacter.levi (CommAlgCat.of R A) (weightCocharacter (R := R) w) := by
  rw [GeneralLinear.mem_weightLeviDefiningPointsSubgroup_iff,
    mem_levi_weightCocharacter_iff]

/-- Identify the cut-out ambient point subgroup with the dynamic Levi point subgroup. -/
private noncomputable def weightLeviPointsSubgroupMulEquiv (w : Fin N → ℤ) :
    CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R N)
        (weightLeviDefiningHopfIdeal R w) (CommAlgCat.of R A) ≃*
      Cocharacter.levi (CommAlgCat.of R A) (weightCocharacter (R := R) w) :=
  MulEquiv.subgroupCongr <| Subgroup.ext fun g ↦
    mem_weightLeviDefiningPointsSubgroup_iff R w g

private theorem weightLeviPointsSubgroupMulEquiv_natural (w : Fin N → ℤ)
    {B : CommAlgCat.{v} R} (phi : CommAlgCat.of R A ⟶ B)
    (g : CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R N)
      (weightLeviDefiningHopfIdeal R w) (CommAlgCat.of R A)) :
    weightLeviPointsSubgroupMulEquiv R w
        (CommHopfAlgCat.mapQuotientPointsSubgroup (coordinateHopfAlgebra R N)
          (weightLeviDefiningHopfIdeal R w) phi g) =
      Cocharacter.mapLevi (weightCocharacter (R := R) w) phi
        (weightLeviPointsSubgroupMulEquiv R w g) := by
  apply Subtype.ext
  calc
    _ = ((CommHopfAlgCat.mapQuotientPointsSubgroup (coordinateHopfAlgebra R N)
          (weightLeviDefiningHopfIdeal R w) phi g) :
        HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N) B) :=
      MulEquiv.subgroupCongr_apply _ _
    _ = HopfAlgebra.mapPoints (H := coordinateHopfAlgebra R N) phi g :=
      CommHopfAlgCat.coe_mapQuotientPointsSubgroup_apply _ _ _ _
    _ = AlgHom.mapValue phi.hom g := rfl
    _ = AlgHom.mapValue phi.hom
        ((weightLeviPointsSubgroupMulEquiv R w g :
            Cocharacter.levi (CommAlgCat.of R A) (weightCocharacter (R := R) w)) :
          HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N)
            (CommAlgCat.of R A)) := by
      congr 1
    _ = ((Cocharacter.mapLevi (weightCocharacter (R := R) w) phi
          (weightLeviPointsSubgroupMulEquiv R w g) :
            Cocharacter.levi B (weightCocharacter (R := R) w)) :
        HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N) B) :=
      (Cocharacter.coe_mapLevi_apply _ _ _).symm

end Points

/-- The cut-out subgroup functor is naturally the dynamic Levi functor. -/
private noncomputable def weightLeviSubgroupPointsIso (w : Fin N → ℤ) :
    CommHopfAlgCat.quotientPointsSubgroupFunctor (R := R) (coordinateHopfAlgebra R N)
        (weightLeviDefiningHopfIdeal R w) ≅
      Cocharacter.leviFunctor (weightCocharacter (R := R) w) :=
  NatIso.ofComponents
    (fun _ ↦ (weightLeviPointsSubgroupMulEquiv R w).toGrpIso)
    (by
      intro A B phi
      ext g
      exact weightLeviPointsSubgroupMulEquiv_natural R w phi g)

/-- The weight-Levi coordinate Hopf algebra represents the dynamic Levi functor of the weight
cocharacter, naturally in the commutative value algebra. -/
noncomputable def weightLeviPointsIso (w : Fin N → ℤ) :
    HopfAlgebra.pointsFunctor (R := R) (H := weightLeviCoordinateHopfAlgebra R w) ≅
      Cocharacter.leviFunctor (weightCocharacter (R := R) w) :=
  (CommHopfAlgCat.quotientPointsSubgroupNatIso (coordinateHopfAlgebra R N)
      (weightLeviDefiningHopfIdeal R w)).trans
    (weightLeviSubgroupPointsIso R w)

/-- The ambient point underlying the represented dynamic-Levi point is induced by the quotient
coordinate map. -/
@[simp]
theorem coe_weightLeviPointsIso_hom_app_apply (w : Fin N → ℤ)
    {A : Type v} [CommRing A] [Algebra R A]
    (f : HopfAlgebra.points
      (R := R) (H := weightLeviCoordinateHopfAlgebra R w) (CommAlgCat.of R A)) :
    (((eqToHom (Cocharacter.leviFunctor_obj
        (weightCocharacter (R := R) w) (CommAlgCat.of R A)))
      ((weightLeviPointsIso R w).hom.app (CommAlgCat.of R A) f) :
        Cocharacter.levi (CommAlgCat.of R A) (weightCocharacter (R := R) w)) :
      HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N) (CommAlgCat.of R A)) =
      CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
        (weightLeviDefiningHopfIdeal R w) (CommAlgCat.of R A) f := by
  have hcomponent := CommHopfAlgCat.quotientPointsSubgroupNatIso_hom_app_apply
    (coordinateHopfAlgebra R N) (weightLeviDefiningHopfIdeal R w)
    (CommAlgCat.of R A) f
  unfold weightLeviPointsIso
  exact congrArg
    (fun g => ((weightLeviPointsSubgroupMulEquiv R w g :
        Cocharacter.levi (CommAlgCat.of R A) (weightCocharacter (R := R) w)) :
      HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N) (CommAlgCat.of R A)))
    hcomponent

/-- Applying the quotient inclusion to the inverse representing isomorphism recovers the ambient
dynamic-Levi point. -/
@[simp]
theorem quotientPointsHom_weightLeviPointsIso_inv_app_apply (w : Fin N → ℤ)
    {A : Type v} [CommRing A] [Algebra R A]
    (g : Cocharacter.levi (CommAlgCat.of R A) (weightCocharacter (R := R) w)) :
    CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
        (weightLeviDefiningHopfIdeal R w) (CommAlgCat.of R A)
        ((weightLeviPointsIso R w).inv.app (CommAlgCat.of R A) g) = g.1 := by
  let f := (weightLeviPointsIso R w).inv.app (CommAlgCat.of R A) g
  calc
    CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
        (weightLeviDefiningHopfIdeal R w) (CommAlgCat.of R A) f =
      (((eqToHom (Cocharacter.leviFunctor_obj
          (weightCocharacter (R := R) w) (CommAlgCat.of R A)))
        ((weightLeviPointsIso R w).hom.app (CommAlgCat.of R A) f) :
          Cocharacter.levi (CommAlgCat.of R A) (weightCocharacter (R := R) w)) :
          HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N)
            (CommAlgCat.of R A)) :=
      (coe_weightLeviPointsIso_hom_app_apply R w f).symm
    _ = g.1 := by
      have hinv := CategoryTheory.Iso.inv_hom_id_apply
        ((weightLeviPointsIso R w).app (CommAlgCat.of R A))
        (eqToHom (Cocharacter.leviFunctor_obj
          (weightCocharacter (R := R) w) (CommAlgCat.of R A)).symm g)
      exact congrArg Subtype.val hinv

end TauCeti.GeneralLinear.Dynamic
