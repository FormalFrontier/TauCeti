/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Functor
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Borel
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.GL2.Subgroups
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Parabolic.Basic

/-!
# Representability of the dynamic subgroups of `GL₂`

For the cocharacter `t ↦ diag(t, 1)`, the dynamic parabolic, Levi, and unipotent subgroup
functors are represented by the standard upper-triangular Borel, diagonal torus, and positive
root subgroup. This upgrades the pointwise calculations in
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.GL2.Subgroups` to natural isomorphisms of
group-valued functors.

Concretely, the three representing coordinate Hopf algebras are

* `Borel.coordinateHopfAlgebra R` for the dynamic parabolic;
* the rank-two split-torus group algebra for the dynamic Levi;
* `AdditiveGroup.coordinateHopfAlgebra R` for the dynamic unipotent subgroup.

The natural isomorphisms commute with the inclusions into `GL₂`: on every value algebra their
components are the existing Borel point equivalence, diagonal-torus point map, and positive
root-subgroup point map.

## Main declarations

* `TauCeti.GeneralLinear.Dynamic.GL2.borelPointsIsoParabolicFunctor` represents the dynamic
  parabolic functor by the Borel coordinate Hopf algebra.
* `TauCeti.GeneralLinear.Dynamic.GL2.splitTorusPointsIsoLeviFunctor` represents the dynamic
  Levi functor by the rank-two split torus.
* `TauCeti.GeneralLinear.Dynamic.GL2.additivePointsIsoUnipotentFunctor` represents the dynamic
  unipotent functor by the additive group.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.

This supplies scheme-level representability for the rank-one dynamic-parabolic route in Layer 7,
"Structure theory", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear.Dynamic.GL2

universe u w

variable {R : Type u} [CommRing R]

/-- The Borel coordinate Hopf algebra represents the dynamic parabolic functor for
`t ↦ diag(t, 1)`. -/
noncomputable def borelPointsIsoParabolicFunctor :
    HopfAlgebra.pointsFunctor (R := R) (H := Borel.coordinateHopfAlgebra R) ≅
      Cocharacter.parabolicFunctor (dynamicCocharacter (R := R)) := by
  rw [dynamicCocharacter_eq_weightCocharacter]
  exact weightParabolicPointsIso R Borel.weights

/-! ## The dynamic Levi -/

/-- The diagonal-torus point map, with codomain restricted to the dynamic Levi. -/
noncomputable def splitTorusToLevi (A : CommAlgCat.{w} R) :
    HopfAlgebra.points
        (R := R)
        (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin 2) →₀ ℤ))) A →*
      Cocharacter.levi A (dynamicCocharacter (R := R)) :=
  (diagonalTorusPoints (R := R) (N := 2) (A := A)).codRestrict _ fun f ↦
    (mem_dynamicLevi_iff_exists_diagonalTorusPoint
      (R := R) (A := A) (diagonalTorusPoints f)).mpr ⟨f, rfl⟩

/-- The pointwise equivalence from the rank-two split torus to the dynamic Levi. -/
noncomputable def splitTorusLeviMulEquiv (A : CommAlgCat.{w} R) :
    HopfAlgebra.points
        (R := R)
        (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin 2) →₀ ℤ))) A ≃*
      Cocharacter.levi A (dynamicCocharacter (R := R)) :=
  MulEquiv.ofBijective (splitTorusToLevi A) ⟨
    fun _ _ h ↦ diagonalTorusPoints_injective (congrArg Subtype.val h),
    fun g ↦ by
      obtain ⟨f, hf⟩ :=
        (mem_dynamicLevi_iff_exists_diagonalTorusPoint (R := R) (A := A) g).mp g.2
      exact ⟨f, Subtype.ext hf⟩⟩

@[simp]
theorem coe_splitTorusLeviMulEquiv_apply (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points
      (R := R)
      (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin 2) →₀ ℤ))) A) :
    ((splitTorusLeviMulEquiv A f :
        Cocharacter.levi A (dynamicCocharacter (R := R))) :
      WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) =
      diagonalTorusPoints f := by
  unfold splitTorusLeviMulEquiv splitTorusToLevi
  rfl

/-- The rank-two split-torus coordinate Hopf algebra represents the dynamic Levi functor for
`t ↦ diag(t, 1)`. -/
noncomputable def splitTorusPointsIsoLeviFunctor :
    HopfAlgebra.pointsFunctor
        (R := R)
        (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin 2) →₀ ℤ))) ≅
      Cocharacter.leviFunctor (dynamicCocharacter (R := R)) :=
  NatIso.ofComponents
    (fun A ↦ (splitTorusLeviMulEquiv A).toGrpIso)
    (by
      intro A B φ
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro (f : HopfAlgebra.points
        (R := R)
        (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin 2) →₀ ℤ))) A)
      apply Subtype.ext
      -- Both component maps are restrictions of the corresponding ambient point maps.
      unfold HopfAlgebra.pointsFunctor Cocharacter.leviFunctor
      change ((splitTorusLeviMulEquiv B
          (HopfAlgebra.mapPoints
            (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin 2) →₀ ℤ))) φ f) :
              Cocharacter.levi B (dynamicCocharacter (R := R))) :
            WithConv (coordinateHopfAlgebra R 2 →ₐ[R] B)) =
        ((Cocharacter.mapLevi (dynamicCocharacter (R := R)) φ
            (splitTorusLeviMulEquiv A f) :
              Cocharacter.levi B (dynamicCocharacter (R := R))) :
            WithConv (coordinateHopfAlgebra R 2 →ₐ[R] B))
      rw [coe_splitTorusLeviMulEquiv_apply, Cocharacter.coe_mapLevi_apply,
        coe_splitTorusLeviMulEquiv_apply]
      exact (mapValue_diagonalTorusPoints φ.hom f).symm)

/-- The forward component of `splitTorusPointsIsoLeviFunctor` is the pointwise split-torus
equivalence. -/
@[simp]
theorem splitTorusPointsIsoLeviFunctor_hom_app_apply (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points
      (R := R)
      (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin 2) →₀ ℤ))) A) :
    (splitTorusPointsIsoLeviFunctor (R := R)).hom.app A f =
      splitTorusLeviMulEquiv A f := by
  unfold splitTorusPointsIsoLeviFunctor
  rfl

/-- The inverse component of `splitTorusPointsIsoLeviFunctor` is the inverse pointwise
split-torus equivalence. -/
@[simp]
theorem splitTorusPointsIsoLeviFunctor_inv_app_apply (A : CommAlgCat.{w} R)
    (g : Cocharacter.levi A (dynamicCocharacter (R := R))) :
    (splitTorusPointsIsoLeviFunctor (R := R)).inv.app A g =
      (splitTorusLeviMulEquiv A).symm g := by
  unfold splitTorusPointsIsoLeviFunctor
  rfl

/-! ## The dynamic unipotent subgroup -/

/-- The positive root-subgroup point map, with codomain restricted to the dynamic unipotent
subgroup. -/
noncomputable def additiveToUnipotent (A : CommAlgCat.{w} R) :
    HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A →*
      Cocharacter.unipotent A (dynamicCocharacter (R := R)) :=
  (rootSubgroupPoints (R := R) (N := 2) (A := A)
    (by decide : (0 : Fin 2) ≠ 1)).codRestrict _ fun f ↦
      (mem_dynamicUnipotent_iff_exists_rootSubgroupPoint
        (R := R) (A := A) (rootSubgroupPoints (by decide) f)).mpr ⟨f, rfl⟩

/-- The pointwise equivalence from the additive group to the dynamic unipotent subgroup. -/
noncomputable def additiveUnipotentMulEquiv (A : CommAlgCat.{w} R) :
    HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A ≃*
      Cocharacter.unipotent A (dynamicCocharacter (R := R)) :=
  MulEquiv.ofBijective (additiveToUnipotent A) ⟨
    fun _ _ h ↦ rootSubgroupPoints_injective (by decide) (congrArg Subtype.val h),
    fun g ↦ by
      obtain ⟨f, hf⟩ :=
        (mem_dynamicUnipotent_iff_exists_rootSubgroupPoint (R := R) (A := A) g).mp g.2
      exact ⟨f, Subtype.ext hf⟩⟩

@[simp]
theorem coe_additiveUnipotentMulEquiv_apply (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A) :
    ((additiveUnipotentMulEquiv A f :
        Cocharacter.unipotent A (dynamicCocharacter (R := R))) :
      WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) =
      rootSubgroupPoints (by decide : (0 : Fin 2) ≠ 1) f := by
  unfold additiveUnipotentMulEquiv additiveToUnipotent
  rfl

/-- The additive-group coordinate Hopf algebra represents the dynamic unipotent functor for
`t ↦ diag(t, 1)`. -/
noncomputable def additivePointsIsoUnipotentFunctor :
    HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ≅
      Cocharacter.unipotentFunctor (dynamicCocharacter (R := R)) :=
  NatIso.ofComponents
    (fun A ↦ (additiveUnipotentMulEquiv A).toGrpIso)
    (by
      intro A B φ
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro (f : HopfAlgebra.points
        (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A)
      apply Subtype.ext
      -- Both component maps are restrictions of the corresponding ambient point maps.
      unfold HopfAlgebra.pointsFunctor Cocharacter.unipotentFunctor
      change ((additiveUnipotentMulEquiv B
          (HopfAlgebra.mapPoints (H := AdditiveGroup.coordinateHopfAlgebra R) φ f) :
            Cocharacter.unipotent B (dynamicCocharacter (R := R))) :
          WithConv (coordinateHopfAlgebra R 2 →ₐ[R] B)) =
        ((Cocharacter.mapUnipotent (dynamicCocharacter (R := R)) φ
            (additiveUnipotentMulEquiv A f) :
              Cocharacter.unipotent B (dynamicCocharacter (R := R))) :
            WithConv (coordinateHopfAlgebra R 2 →ₐ[R] B))
      rw [coe_additiveUnipotentMulEquiv_apply, Cocharacter.coe_mapUnipotent_apply,
        coe_additiveUnipotentMulEquiv_apply]
      exact (mapValue_rootSubgroupPoints φ.hom (by decide) f).symm)

/-- The forward component of `additivePointsIsoUnipotentFunctor` is the pointwise additive
equivalence. -/
@[simp]
theorem additivePointsIsoUnipotentFunctor_hom_app_apply (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A) :
    (additivePointsIsoUnipotentFunctor (R := R)).hom.app A f =
      additiveUnipotentMulEquiv A f := by
  unfold additivePointsIsoUnipotentFunctor
  rfl

/-- The inverse component of `additivePointsIsoUnipotentFunctor` is the inverse pointwise
additive equivalence. -/
@[simp]
theorem additivePointsIsoUnipotentFunctor_inv_app_apply (A : CommAlgCat.{w} R)
    (g : Cocharacter.unipotent A (dynamicCocharacter (R := R))) :
    (additivePointsIsoUnipotentFunctor (R := R)).inv.app A g =
      (additiveUnipotentMulEquiv A).symm g := by
  unfold additivePointsIsoUnipotentFunctor
  rfl

end TauCeti.GeneralLinear.Dynamic.GL2
