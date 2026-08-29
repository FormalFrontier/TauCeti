/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Levi.Decomposition
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Kernel

/-!
# The kernel of the represented weight-parabolic limit

Let `w : Fin N → ℤ`. The dynamic limit from the weight parabolic `P(w)` to its Levi
subgroup `L(w)` is already represented by a morphism of affine group schemes. This file
identifies its scheme-theoretic kernel with the represented weight-unipotent subgroup `U(w)`.
Thus the pointwise identity

```text
U(w)(A) = ker (P(w)(A) → L(w)(A))
```

holds at the level of defining Hopf ideals, not only after choosing a value algebra `A`.

## Main declarations

* `TauCeti.GeneralLinear.Dynamic.mem_weightUnipotentInParabolicPointsSubgroup_iff_limit_eq_one`:
  a represented parabolic point belongs to the relative unipotent subgroup exactly when its
  represented dynamic limit is the identity.
* `TauCeti.GeneralLinear.Dynamic.kernelHopfIdeal_weightParabolicLimitCoordinateMap`: the kernel
  Hopf ideal of the represented limit is the relative weight-unipotent Hopf ideal.
* `TauCeti.GeneralLinear.Dynamic.weightParabolicLimitKernelIso`: the resulting canonical
  isomorphism from the scheme-theoretic kernel to the weight-unipotent group scheme.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.

This advances the dynamic Levi-decomposition milestone in Layer 7, "Structure theory", of the
ReductiveGroups roadmap. The kernel identification is the normal-factor input for identifying
the represented weight parabolic with the semidirect product of its weight-unipotent and
weight-Levi subgroups.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear.Dynamic

universe u v

noncomputable section

variable (R : Type u) [CommRing R] {N : ℕ}

/-- A represented weight-parabolic point lies in the relative weight-unipotent subgroup exactly
when its represented dynamic limit is the identity of the weight-Levi point group. -/
@[simp]
theorem mem_weightUnipotentInParabolicPointsSubgroup_iff_limit_eq_one
    (w : Fin N → ℤ) (A : CommAlgCat.{v} R)
    (g : HopfAlgebra.points (R := R) (H := weightParabolicCoordinateHopfAlgebra R w) A) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup
        (weightParabolicCoordinateHopfAlgebra R w)
        (weightUnipotentInParabolicHopfIdeal R w) A ↔
      (CommHopfAlgCat.mapPointsFunctor
        (weightParabolicLimitCoordinateMap R w)).app A g = 1 := by
  rcases A with ⟨A⟩
  let p : Cocharacter.parabolic A (weightCocharacter (R := R) w) :=
    (weightParabolicPointsIso R w).hom.app (CommAlgCat.of R A) g
  rw [mapPointsFunctor_weightParabolicLimitCoordinateMap_app]
  constructor
  · intro hg
    have hg' := (mem_weightUnipotentInParabolicPointsSubgroup_iff R w g).mp hg
    have hu := (mem_weightUnipotentDefiningPointsSubgroup_iff R w _).mp hg'
    have hcoe : (p : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N)
        (CommAlgCat.of R A)) =
        CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
          (weightParabolicDefiningHopfIdeal R w) (CommAlgCat.of R A) g := by
      let p' : Cocharacter.parabolic A (weightCocharacter (R := R) w) :=
        eqToHom (Cocharacter.parabolicFunctor_obj
          (weightCocharacter (R := R) w) (CommAlgCat.of R A))
          ((weightParabolicPointsIso R w).hom.app (CommAlgCat.of R A) g)
      have hp : p = p' := by
        apply Subtype.ext
        rfl
      rw [hp]
      exact coe_weightParabolicPointsIso_hom_app_apply R w g
    have hpUnipotent : (p : HopfAlgebra.points
        (R := R) (H := coordinateHopfAlgebra R N) (CommAlgCat.of R A)) ∈
        Cocharacter.unipotent A (weightCocharacter (R := R) w) := by
      rw [hcoe]
      exact hu
    have hlimit : Cocharacter.limit A (weightCocharacter (R := R) w) p = 1 :=
      (Cocharacter.mem_unipotent_iff.mp hpUnipotent).2
    apply CommHopfAlgCat.quotientPointsHom_injective
      (coordinateHopfAlgebra R N) (weightLeviDefiningHopfIdeal R w)
      (CommAlgCat.of R A)
    rw [quotientPointsHom_weightLeviPointsIso_inv_app_apply]
    have hone := map_one (CommHopfAlgCat.quotientPointsHom
      (coordinateHopfAlgebra R N) (weightLeviDefiningHopfIdeal R w)
      (CommAlgCat.of R A)).hom
    -- The representing isomorphism hides the Levi subtype; expose its ambient point so the
    -- quotient-point injectivity calculation can use the dynamic limit equation.
    change (Cocharacter.limitToLevi A (weightCocharacter (R := R) w) p :
      HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N)
        (CommAlgCat.of R A)) = _
    calc
      _ = Cocharacter.limit A
          (weightCocharacter (R := R) w) p :=
        Cocharacter.coe_limitToLevi_apply A (weightCocharacter (R := R) w) p
      _ = 1 := hlimit
      _ = _ := hone.symm
  · intro hlimit
    have hlimit' : Cocharacter.limitToLevi A
        (weightCocharacter (R := R) w) p = 1 := by
      have hlimitFunctor := congrArg
        (fun z ↦ CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
          (weightLeviDefiningHopfIdeal R w) (CommAlgCat.of R A) z) hlimit
      rw [quotientPointsHom_weightLeviPointsIso_inv_app_apply] at hlimitFunctor
      have hone := map_one (CommHopfAlgCat.quotientPointsHom
        (coordinateHopfAlgebra R N) (weightLeviDefiningHopfIdeal R w)
        (CommAlgCat.of R A)).hom
      apply Subtype.ext
      calc
        _ = (Cocharacter.limitToLevi A
            (weightCocharacter (R := R) w) p : HopfAlgebra.points
              (R := R) (H := coordinateHopfAlgebra R N) (CommAlgCat.of R A)) := rfl
        _ = (CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
            (weightLeviDefiningHopfIdeal R w) (CommAlgCat.of R A)).hom 1 := hlimitFunctor
        _ = 1 := hone
    have hpUnipotent : (p : HopfAlgebra.points
        (R := R) (H := coordinateHopfAlgebra R N) (CommAlgCat.of R A)) ∈
        Cocharacter.unipotent A (weightCocharacter (R := R) w) := by
      apply Cocharacter.mem_unipotent_iff.mpr
      refine ⟨p.2, ?_⟩
      have := congrArg Subtype.val hlimit'
      have hp : (⟨(p : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N)
          (CommAlgCat.of R A)), p.2⟩ :
            Cocharacter.parabolic A (weightCocharacter (R := R) w)) = p :=
        Subtype.ext rfl
      rw [hp]
      simpa only [Cocharacter.coe_limitToLevi_apply, Subgroup.coe_one] using this
    apply (mem_weightUnipotentInParabolicPointsSubgroup_iff R w g).mpr
    apply (mem_weightUnipotentDefiningPointsSubgroup_iff R w _).mpr
    rw [← coe_weightParabolicPointsIso_hom_app_apply R w g]
    exact hpUnipotent

private theorem hopfIdeal_le_of_quotientGenericPoint_mem
    (H : _root_.CommHopfAlgCat.{u} R) (I J : HopfIdeal R H)
    (h : CommHopfAlgCat.quotientPointsHom H J
        (CommAlgCat.of R (CommHopfAlgCat.quotient H J))
        (toConv (AlgHom.id R (CommHopfAlgCat.quotient H J))) ∈
      CommHopfAlgCat.quotientPointsSubgroup H I
        (CommAlgCat.of R (CommHopfAlgCat.quotient H J))) :
    I ≤ J := by
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at h
  intro x hx
  have hx0 := h x hx
  rw [CommHopfAlgCat.quotientPointsHom_apply_apply, ofConv_toConv,
    AlgHom.id_apply] at hx0
  exact HopfIdeal.mem_toIdeal.mpr (Ideal.Quotient.eq_zero_iff_mem.mp hx0)

/-- The scheme-theoretic kernel of the represented weight-parabolic limit is the represented
weight-unipotent subgroup, as an equality of Hopf ideals in the parabolic coordinate algebra. -/
theorem kernelHopfIdeal_weightParabolicLimitCoordinateMap (w : Fin N → ℤ) :
    CommHopfAlgCat.kernelHopfIdeal (weightParabolicLimitCoordinateMap R w) =
      weightUnipotentInParabolicHopfIdeal R w := by
  apply le_antisymm
  · apply hopfIdeal_le_of_quotientGenericPoint_mem R
      (weightParabolicCoordinateHopfAlgebra R w)
      (CommHopfAlgCat.kernelHopfIdeal (weightParabolicLimitCoordinateMap R w))
      (weightUnipotentInParabolicHopfIdeal R w)
    apply (CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff
      (weightParabolicLimitCoordinateMap R w) _ _).mp
    rw [← CommHopfAlgCat.mapPointsFunctor_app_apply]
    apply (mem_weightUnipotentInParabolicPointsSubgroup_iff_limit_eq_one R w _ _).mp
    exact CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup _ _ _ _
  · apply hopfIdeal_le_of_quotientGenericPoint_mem R
      (weightParabolicCoordinateHopfAlgebra R w)
      (weightUnipotentInParabolicHopfIdeal R w)
      (CommHopfAlgCat.kernelHopfIdeal (weightParabolicLimitCoordinateMap R w))
    apply (mem_weightUnipotentInParabolicPointsSubgroup_iff_limit_eq_one R w _ _).mpr
    rw [CommHopfAlgCat.mapPointsFunctor_app_apply]
    apply (CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff
      (weightParabolicLimitCoordinateMap R w) _ _).mpr
    exact CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup _ _ _ _

private theorem eqToIso_quotientSpec_hom_comp_quotientSpecι
    (H : _root_.CommHopfAlgCat.{u} R) {I J : HopfIdeal R H} (hIJ : I = J) :
    (eqToIso (congrArg (CommHopfAlgCat.quotientSpec H) hIJ)).hom ≫
        CommHopfAlgCat.quotientSpecι H J =
      CommHopfAlgCat.quotientSpecι H I := by
  subst J
  simp

/-- The scheme-theoretic kernel of the weight-parabolic limit is canonically the represented
weight-unipotent group scheme. -/
noncomputable def weightParabolicLimitKernelIso (w : Fin N → ℤ) :
    CommHopfAlgCat.kernelSpec (weightParabolicLimitCoordinateMap R w) ≅
      weightUnipotentGroupScheme R w :=
  eqToIso (congrArg
      (CommHopfAlgCat.quotientSpec (weightParabolicCoordinateHopfAlgebra R w))
      (kernelHopfIdeal_weightParabolicLimitCoordinateMap R w)) ≪≫
    weightUnipotentInParabolicGroupSchemeIso R w

/-- Under the kernel identification, the canonical kernel inclusion is the represented
weight-unipotent inclusion into the weight parabolic. -/
@[simp]
theorem weightParabolicLimitKernelIso_hom_comp_weightUnipotentToParabolic
    (w : Fin N → ℤ) :
    (weightParabolicLimitKernelIso R w).hom ≫ weightUnipotentToParabolic R w =
      CommHopfAlgCat.kernelSpecι (weightParabolicLimitCoordinateMap R w) := by
  rw [weightParabolicLimitKernelIso, Iso.trans_hom, Category.assoc,
    weightUnipotentInParabolicGroupSchemeIso_hom_comp_weightUnipotentToParabolic,
    CommHopfAlgCat.kernelSpecι_def]
  exact eqToIso_quotientSpec_hom_comp_quotientSpecι R _
    (kernelHopfIdeal_weightParabolicLimitCoordinateMap R w)

end

end TauCeti.GeneralLinear.Dynamic
