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

private theorem mapWeightLevi_id (w : Fin N → ℤ) (A : CommAlgCat.{v} R)
    (g : Cocharacter.levi A (weightCocharacter (R := R) w)) :
    Cocharacter.mapLevi (weightCocharacter (R := R) w) (𝟙 A) g = g := by
  apply Subtype.ext
  rw [Cocharacter.coe_mapLevi_apply, CommAlgCat.hom_id,
    AlgHom.mapValue_id, MonoidHom.id_apply]

private theorem mapWeightLevi_comp (w : Fin N → ℤ)
    {A B C : CommAlgCat.{v} R} (φ : A ⟶ B) (ψ : B ⟶ C)
    (g : Cocharacter.levi A (weightCocharacter (R := R) w)) :
    Cocharacter.mapLevi (weightCocharacter (R := R) w) (φ ≫ ψ) g =
      Cocharacter.mapLevi (weightCocharacter (R := R) w) ψ
        (Cocharacter.mapLevi (weightCocharacter (R := R) w) φ g) := by
  apply Subtype.ext
  rw [Cocharacter.coe_mapLevi_apply, Cocharacter.coe_mapLevi_apply,
    Cocharacter.coe_mapLevi_apply, CommAlgCat.hom_comp,
    AlgHom.mapValue_comp, MonoidHom.comp_apply]

private theorem mem_weightLeviSubgroup_iff (w : Fin N → ℤ)
    (A : CommAlgCat.{v} R)
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N) A) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R N)
        (weightLeviDefiningHopfIdeal R w) A ↔
      g ∈ Cocharacter.levi A (weightCocharacter (R := R) w) :=
  by
    rw [GeneralLinear.mem_weightLeviDefiningPointsSubgroup_iff_apply_eq_zero,
      mem_levi_weightCocharacter_iff]

private theorem coe_mapWeightLevi_apply (w : Fin N → ℤ)
    {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (g : Cocharacter.levi A (weightCocharacter (R := R) w)) :
    (Cocharacter.mapLevi (weightCocharacter (R := R) w) φ g :
      HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N) B) =
      HopfAlgebra.mapPoints (H := coordinateHopfAlgebra R N) φ g :=
  Cocharacter.coe_mapLevi_apply (weightCocharacter (R := R) w) φ g

section Points

variable {A : Type v} [CommRing A] [Algebra R A]

/-- The Hopf-ideal cut-out is exactly the dynamic Levi of the weight cocharacter. -/
theorem mem_weightLeviDefiningPointsSubgroup_iff (w : Fin N → ℤ)
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N)
      (CommAlgCat.of R A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R N)
        (weightLeviDefiningHopfIdeal R w) (CommAlgCat.of R A) ↔
      g ∈ Cocharacter.levi (CommAlgCat.of R A) (weightCocharacter (R := R) w) := by
  rw [GeneralLinear.mem_weightLeviDefiningPointsSubgroup_iff_apply_eq_zero,
    mem_levi_weightCocharacter_iff]

end Points

/-- The weight-Levi coordinate Hopf algebra represents the dynamic Levi functor of the weight
cocharacter, naturally in the commutative value algebra. -/
noncomputable def weightLeviPointsIso (w : Fin N → ℤ) :
    HopfAlgebra.pointsFunctor (R := R) (H := weightLeviCoordinateHopfAlgebra R w) ≅
      Cocharacter.leviFunctor (weightCocharacter (R := R) w) :=
  CommHopfAlgCat.quotientPointsSubgroupRepresentingIso
    (coordinateHopfAlgebra R N) (weightLeviDefiningHopfIdeal R w)
    (fun A ↦ Cocharacter.levi A (weightCocharacter (R := R) w))
    (fun φ ↦ Cocharacter.mapLevi (weightCocharacter (R := R) w) φ)
    (mapWeightLevi_id R w) (mapWeightLevi_comp R w)
    (mem_weightLeviSubgroup_iff R w) (coe_mapWeightLevi_apply R w)

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
  unfold weightLeviPointsIso
  convert
    (CommHopfAlgCat.coe_quotientPointsSubgroupRepresentingIso_hom_app_apply
      (coordinateHopfAlgebra R N) (weightLeviDefiningHopfIdeal R w)
      (fun B ↦ Cocharacter.levi B (weightCocharacter (R := R) w))
      (fun φ ↦ Cocharacter.mapLevi (weightCocharacter (R := R) w) φ)
      (mapWeightLevi_id R w) (mapWeightLevi_comp R w)
      (mem_weightLeviSubgroup_iff R w) (coe_mapWeightLevi_apply R w)
      (CommAlgCat.of R A) f) using 1
  rfl

/-- Applying the quotient inclusion to the inverse representing isomorphism recovers the ambient
dynamic-Levi point. -/
@[simp]
theorem quotientPointsHom_weightLeviPointsIso_inv_app_apply (w : Fin N → ℤ)
    {A : Type v} [CommRing A] [Algebra R A]
    (g : Cocharacter.levi (CommAlgCat.of R A) (weightCocharacter (R := R) w)) :
    CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
        (weightLeviDefiningHopfIdeal R w) (CommAlgCat.of R A)
        ((weightLeviPointsIso R w).inv.app (CommAlgCat.of R A) g) = g.1 := by
  unfold weightLeviPointsIso
  convert
    (CommHopfAlgCat.quotientPointsHom_quotientPointsSubgroupRepresentingIso_inv_app_apply
      (coordinateHopfAlgebra R N) (weightLeviDefiningHopfIdeal R w)
      (fun B ↦ Cocharacter.levi B (weightCocharacter (R := R) w))
      (fun φ ↦ Cocharacter.mapLevi (weightCocharacter (R := R) w) φ)
      (mapWeightLevi_id R w) (mapWeightLevi_comp R w)
      (mem_weightLeviSubgroup_iff R w) (coe_mapWeightLevi_apply R w)
      (CommAlgCat.of R A) g) using 1
  rfl

end TauCeti.GeneralLinear.Dynamic
