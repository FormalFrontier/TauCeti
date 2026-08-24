/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Functor
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Borel
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.GL2.Subgroups

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

/-- The pointwise equivalence from the dynamic parabolic to the upper-triangular Borel. -/
noncomputable def parabolicBorelMulEquiv (A : CommAlgCat.{w} R) :
    Cocharacter.parabolic A (dynamicCocharacter (R := R)) ≃* GL2Borel A where
  toFun g := ⟨pointsMulEquiv (R := R) (A := A) 2 g,
    (mem_dynamicParabolic_iff (R := R) (A := A) g).mp g.2⟩
  invFun g := ⟨(pointsMulEquiv (R := R) (A := A) 2).symm g,
    (mem_dynamicParabolic_iff (R := R) (A := A) _).mpr (by
      rw [(pointsMulEquiv (R := R) (A := A) 2).apply_symm_apply]
      exact g.2)⟩
  left_inv g := Subtype.ext
    ((pointsMulEquiv (R := R) (A := A) 2).symm_apply_apply
      (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)))
  right_inv g := Subtype.ext
    ((pointsMulEquiv (R := R) (A := A) 2).apply_symm_apply (g : GL (Fin 2) A))
  map_mul' g h := Subtype.ext
    (map_mul (pointsMulEquiv (R := R) (A := A) 2)
      (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) h)

@[simp]
theorem coe_parabolicBorelMulEquiv_apply (A : CommAlgCat.{w} R)
    (g : Cocharacter.parabolic A (dynamicCocharacter (R := R))) :
    ((parabolicBorelMulEquiv A g : GL2Borel A) : GL (Fin 2) A) =
      pointsMulEquiv 2 (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) := by
  unfold parabolicBorelMulEquiv
  -- The equivalence stores this map under the `GL2Borel` subtype coercion.
  change pointsMulEquiv 2 (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) = _
  rfl

@[simp]
theorem pointToGeneralLinear_parabolicBorelMulEquiv_symm_apply (A : CommAlgCat.{w} R)
    (g : GL2Borel A) :
    pointToGeneralLinear 2
        (((parabolicBorelMulEquiv A).symm g :
          Cocharacter.parabolic A (dynamicCocharacter (R := R))) :
            WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) =
      (g : GL (Fin 2) A) := by
  unfold parabolicBorelMulEquiv
  -- The inverse field is the ambient inverse point equivalence, restricted to the subgroup.
  rw [← pointsMulEquiv_apply]
  change pointsMulEquiv 2 ((pointsMulEquiv 2).symm (g : GL (Fin 2) A)) = _
  exact (pointsMulEquiv 2).apply_symm_apply (g : GL (Fin 2) A)

/-- The Borel coordinate Hopf algebra represents the dynamic parabolic functor for
`t ↦ diag(t, 1)`. -/
noncomputable def borelPointsIsoParabolicFunctor :
    HopfAlgebra.pointsFunctor (R := R) (H := Borel.coordinateHopfAlgebra R) ≅
      Cocharacter.parabolicFunctor (dynamicCocharacter (R := R)) :=
  NatIso.ofComponents
    (fun A ↦ ((Borel.pointsMulEquiv (R := R) (A := A)).trans
      (parabolicBorelMulEquiv A).symm).toGrpIso)
    (by
      intro A B φ
      ext f
      apply Subtype.ext
      apply (pointsMulEquiv (R := R) (A := B) 2).injective
      -- `NatIso.ofComponents` expands the categorical compositions but leaves the subgroup
      -- coercions opaque; the next `change` states their pointwise content.
      change pointsMulEquiv 2
          (((parabolicBorelMulEquiv B).symm
            (Borel.pointsMulEquiv (R := R) (A := B)
              (HopfAlgebra.mapPoints (H := Borel.coordinateHopfAlgebra R) φ f)) :
                Cocharacter.parabolic B (dynamicCocharacter (R := R))) :
            WithConv (coordinateHopfAlgebra R 2 →ₐ[R] B)) =
        pointsMulEquiv 2
          ((Cocharacter.mapParabolic (dynamicCocharacter (R := R)) φ
            ((parabolicBorelMulEquiv A).symm
              (Borel.pointsMulEquiv (R := R) (A := A) f)) :
                Cocharacter.parabolic B (dynamicCocharacter (R := R))) :
            WithConv (coordinateHopfAlgebra R 2 →ₐ[R] B))
      rw [pointsMulEquiv_apply,
        pointToGeneralLinear_parabolicBorelMulEquiv_symm_apply,
        Cocharacter.coe_mapParabolic_apply, pointsMulEquiv_apply,
        pointToGeneralLinear_mapValue,
        pointToGeneralLinear_parabolicBorelMulEquiv_symm_apply]
      simpa only [Borel.coe_mapBorel, CommAlgCat.hom_ofHom, CommAlgCat.ofHom_hom] using
        congrArg Subtype.val
          (Borel.pointsMulEquiv_mapValue (R := R) (A := A) (B := B) φ.hom f))

/-- The forward component of `borelPointsIsoParabolicFunctor` is the composite of the
Borel point equivalence with the inverse pointwise parabolic equivalence. -/
@[simp]
theorem borelPointsIsoParabolicFunctor_hom_app_apply (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := Borel.coordinateHopfAlgebra R) A) :
    (borelPointsIsoParabolicFunctor (R := R)).hom.app A f =
      (parabolicBorelMulEquiv A).symm (Borel.pointsMulEquiv (R := R) (A := A) f) := by
  unfold borelPointsIsoParabolicFunctor
  rfl

/-- The inverse component of `borelPointsIsoParabolicFunctor` is the composite of the
pointwise parabolic equivalence with the inverse Borel point equivalence. -/
@[simp]
theorem borelPointsIsoParabolicFunctor_inv_app_apply (A : CommAlgCat.{w} R)
    (g : Cocharacter.parabolic A (dynamicCocharacter (R := R))) :
    (borelPointsIsoParabolicFunctor (R := R)).inv.app A g =
      (Borel.pointsMulEquiv (R := R) (A := A)).symm (parabolicBorelMulEquiv A g) := by
  unfold borelPointsIsoParabolicFunctor
  rfl

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
