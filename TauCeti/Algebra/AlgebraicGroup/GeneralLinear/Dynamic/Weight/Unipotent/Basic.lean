/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Unipotent
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Functor
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Naturality

/-!
# Representability of dynamic weight-unipotent subgroups

The weight-unipotent subgroup scheme of `GL_N` represents the dynamic unipotent subgroup attached
to the cocharacter `t ↦ diag(t ^ w i)`. On points, both descriptions say that the matrix is block
triangular for the weight filtration and acts as the identity on every associated-graded weight
space.

Together with the weight-parabolic and weight-Levi representing isomorphisms, this supplies all
three scheme-level pieces attached to an arbitrary diagonal weight cocharacter.

## Main declarations

* `TauCeti.GeneralLinear.Dynamic.mem_weightUnipotentDefiningPointsSubgroup_iff`: membership in
  the Hopf-ideal cut-out agrees with dynamic-unipotent membership.
* `TauCeti.GeneralLinear.Dynamic.weightUnipotentPointsIso`: the natural representing
  isomorphism.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.

This completes representability of the parabolic, Levi, and unipotent functors attached to a
weight cocharacter in the dynamic route of Layer 7, "Structure theory", of the ReductiveGroups
roadmap.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear.Dynamic

universe u v

variable (R : Type u) [CommRing R] {N : ℕ}

private theorem mapWeightUnipotent_id (w : Fin N → ℤ) (A : CommAlgCat.{v} R)
    (g : Cocharacter.unipotent A (weightCocharacter (R := R) w)) :
    Cocharacter.mapUnipotent (weightCocharacter (R := R) w) (𝟙 A) g = g := by
  apply Subtype.ext
  rw [Cocharacter.coe_mapUnipotent_apply, CommAlgCat.hom_id,
    AlgHom.mapValue_id, MonoidHom.id_apply]

private theorem mapWeightUnipotent_comp (w : Fin N → ℤ)
    {A B C : CommAlgCat.{v} R} (φ : A ⟶ B) (ψ : B ⟶ C)
    (g : Cocharacter.unipotent A (weightCocharacter (R := R) w)) :
    Cocharacter.mapUnipotent (weightCocharacter (R := R) w) (φ ≫ ψ) g =
      Cocharacter.mapUnipotent (weightCocharacter (R := R) w) ψ
        (Cocharacter.mapUnipotent (weightCocharacter (R := R) w) φ g) := by
  apply Subtype.ext
  rw [Cocharacter.coe_mapUnipotent_apply, Cocharacter.coe_mapUnipotent_apply,
    Cocharacter.coe_mapUnipotent_apply, CommAlgCat.hom_comp,
    AlgHom.mapValue_comp, MonoidHom.comp_apply]

private theorem mem_weightUnipotentSubgroup_iff (w : Fin N → ℤ)
    (A : CommAlgCat.{v} R)
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N) A) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R N)
        (weightUnipotentDefiningHopfIdeal R w) A ↔
      g ∈ Cocharacter.unipotent A (weightCocharacter (R := R) w) := by
  rw [GeneralLinear.mem_weightUnipotentDefiningPointsSubgroup_iff,
    mem_unipotent_weightCocharacter_iff]
  constructor
  · intro h
    refine ⟨fun i j hij ↦ ?_, fun i j hij ↦ h i j hij.le⟩
    have hne : i ≠ j := fun hEq ↦ hij.ne (congrArg w hEq.symm)
    simpa [Matrix.one_apply, hne] using h i j hij.le
  · rintro ⟨htri, hgraded⟩ i j hij
    rcases hij.eq_or_lt with hEq | hlt
    · exact hgraded i j hEq
    · have hne : i ≠ j := fun hij ↦ hlt.ne (congrArg w hij)
      simpa [Matrix.one_apply, hne] using htri hlt

private theorem coe_mapWeightUnipotent_apply (w : Fin N → ℤ)
    {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (g : Cocharacter.unipotent A (weightCocharacter (R := R) w)) :
    (Cocharacter.mapUnipotent (weightCocharacter (R := R) w) φ g :
      HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N) B) =
      HopfAlgebra.mapPoints (H := coordinateHopfAlgebra R N) φ g :=
  Cocharacter.coe_mapUnipotent_apply (weightCocharacter (R := R) w) φ g

section Points

variable {A : Type v} [CommRing A] [Algebra R A]

/-- The Hopf-ideal cut-out is exactly the dynamic unipotent subgroup of the weight
cocharacter. -/
theorem mem_weightUnipotentDefiningPointsSubgroup_iff (w : Fin N → ℤ)
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N)
      (CommAlgCat.of R A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R N)
        (weightUnipotentDefiningHopfIdeal R w) (CommAlgCat.of R A) ↔
      g ∈ Cocharacter.unipotent (CommAlgCat.of R A) (weightCocharacter (R := R) w) :=
  mem_weightUnipotentSubgroup_iff R w (CommAlgCat.of R A) g

end Points

/-- The weight-unipotent coordinate Hopf algebra represents the dynamic unipotent functor of the
weight cocharacter, naturally in the commutative value algebra. -/
noncomputable def weightUnipotentPointsIso (w : Fin N → ℤ) :
    HopfAlgebra.pointsFunctor (R := R) (H := weightUnipotentCoordinateHopfAlgebra R w) ≅
      Cocharacter.unipotentFunctor (weightCocharacter (R := R) w) :=
  CommHopfAlgCat.quotientPointsSubgroupRepresentingIso
    (coordinateHopfAlgebra R N) (weightUnipotentDefiningHopfIdeal R w)
    (fun A ↦ Cocharacter.unipotent A (weightCocharacter (R := R) w))
    (fun φ ↦ Cocharacter.mapUnipotent (weightCocharacter (R := R) w) φ)
    (mapWeightUnipotent_id R w) (mapWeightUnipotent_comp R w)
    (mem_weightUnipotentSubgroup_iff R w) (coe_mapWeightUnipotent_apply R w)

/-- The ambient point underlying the represented dynamic-unipotent point is induced by the
quotient coordinate map. -/
@[simp]
theorem coe_weightUnipotentPointsIso_hom_app_apply (w : Fin N → ℤ)
    {A : Type v} [CommRing A] [Algebra R A]
    (f : HopfAlgebra.points
      (R := R) (H := weightUnipotentCoordinateHopfAlgebra R w) (CommAlgCat.of R A)) :
    (((eqToHom (Cocharacter.unipotentFunctor_obj
        (weightCocharacter (R := R) w) (CommAlgCat.of R A)))
      ((weightUnipotentPointsIso R w).hom.app (CommAlgCat.of R A) f) :
        Cocharacter.unipotent (CommAlgCat.of R A) (weightCocharacter (R := R) w)) :
      HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N) (CommAlgCat.of R A)) =
      CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
        (weightUnipotentDefiningHopfIdeal R w) (CommAlgCat.of R A) f := by
  unfold weightUnipotentPointsIso
  convert
    (CommHopfAlgCat.coe_quotientPointsSubgroupRepresentingIso_hom_app_apply
      (coordinateHopfAlgebra R N) (weightUnipotentDefiningHopfIdeal R w)
      (fun B ↦ Cocharacter.unipotent B (weightCocharacter (R := R) w))
      (fun φ ↦ Cocharacter.mapUnipotent (weightCocharacter (R := R) w) φ)
      (mapWeightUnipotent_id R w) (mapWeightUnipotent_comp R w)
      (mem_weightUnipotentSubgroup_iff R w) (coe_mapWeightUnipotent_apply R w)
      (CommAlgCat.of R A) f) using 1
  rfl

/-- Applying the quotient inclusion to the inverse representing isomorphism recovers the ambient
dynamic-unipotent point. -/
@[simp]
theorem quotientPointsHom_weightUnipotentPointsIso_inv_app_apply (w : Fin N → ℤ)
    {A : Type v} [CommRing A] [Algebra R A]
    (g : Cocharacter.unipotent (CommAlgCat.of R A) (weightCocharacter (R := R) w)) :
    CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
        (weightUnipotentDefiningHopfIdeal R w) (CommAlgCat.of R A)
        ((weightUnipotentPointsIso R w).inv.app (CommAlgCat.of R A) g) = g.1 := by
  unfold weightUnipotentPointsIso
  convert
    (CommHopfAlgCat.quotientPointsHom_quotientPointsSubgroupRepresentingIso_inv_app_apply
      (coordinateHopfAlgebra R N) (weightUnipotentDefiningHopfIdeal R w)
      (fun B ↦ Cocharacter.unipotent B (weightCocharacter (R := R) w))
      (fun φ ↦ Cocharacter.mapUnipotent (weightCocharacter (R := R) w) φ)
      (mapWeightUnipotent_id R w) (mapWeightUnipotent_comp R w)
      (mem_weightUnipotentSubgroup_iff R w) (coe_mapWeightUnipotent_apply R w)
      (CommAlgCat.of R A) g) using 1
  rfl

end TauCeti.GeneralLinear.Dynamic
