/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Parabolic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Unipotent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Map

/-!
# Normality of weight-unipotent subgroups in weight parabolics

For an integer weight `w` on the standard representation, the weight-unipotent subgroup is a
closed normal subgroup of the corresponding weight parabolic. On coordinate rings, the
parabolic defining Hopf ideal is contained in the unipotent defining Hopf ideal. Mapping the
latter into the parabolic coordinate Hopf algebra therefore cuts out the same unipotent group
scheme, now regarded as a closed subgroup of the parabolic.

Normality is proved honestly at the scheme level. The functor-of-points criterion for a normal
Hopf ideal reduces it to conjugation over every commutative value algebra, where it is precisely
the existing dynamic statement that the weight parabolic normalizes its unipotent part.

## Main declarations

* `TauCeti.GeneralLinear.Dynamic.weightParabolicDefiningHopfIdeal_le_weightUnipotent`: the
  inclusion between the ambient defining Hopf ideals.
* `TauCeti.GeneralLinear.Dynamic.weightUnipotentInParabolicHopfIdeal`: the Hopf ideal in the
  parabolic coordinate algebra cutting out the unipotent subgroup.
* `TauCeti.GeneralLinear.Dynamic.weightUnipotentInParabolicHopfIdeal_isNormal`: scheme-level
  normality of the weight-unipotent subgroup in the weight parabolic.
* `TauCeti.GeneralLinear.Dynamic.weightUnipotentToParabolic`: the resulting closed immersion of
  group schemes.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.

This advances the dynamic Levi-decomposition milestone in Layer 7, "Structure theory", of the
ReductiveGroups roadmap by supplying the scheme-level normality of the represented unipotent
subgroup in its represented parabolic.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv

namespace TauCeti.GeneralLinear.Dynamic

universe u v

variable (R : Type u) [CommRing R] {N : ℕ}

/-- The defining Hopf ideal of the weight parabolic is contained in that of the weight-unipotent
subgroup. Contravariantly, the weight-unipotent group scheme is a closed subgroup of the weight
parabolic group scheme. -/
theorem weightParabolicDefiningHopfIdeal_le_weightUnipotent (w : Fin N → ℤ) :
    weightParabolicDefiningHopfIdeal R w ≤ weightUnipotentDefiningHopfIdeal R w := by
  rw [← HopfIdeal.toIdeal_le_toIdeal,
    weightParabolicDefiningHopfIdeal_toIdeal,
    weightUnipotentDefiningHopfIdeal_toIdeal]
  apply Ideal.span_mono
  intro x hx
  rw [mem_weightParabolicRelationSet_iff] at hx
  obtain ⟨i, j, hij, rfl⟩ := hx
  rw [← genericMatrix_apply]
  have hne : i ≠ j := fun hEq ↦ hij.ne (congrArg w hEq)
  simpa [Matrix.one_apply, hne] using
    sub_one_apply_mem_weightUnipotentRelationSet R w hij.le

/-- The Hopf ideal in the weight-parabolic coordinate algebra which cuts out the
weight-unipotent subgroup. -/
noncomputable def weightUnipotentInParabolicHopfIdeal (w : Fin N → ℤ) :
    HopfIdeal R (weightParabolicCoordinateHopfAlgebra R w) :=
  (weightUnipotentDefiningHopfIdeal R w).map (weightParabolicCoordinateMap R w).hom

/-- Pulling the relative weight-unipotent Hopf ideal back to the ambient general linear
coordinate algebra recovers the original weight-unipotent defining ideal. -/
@[simp]
theorem weightUnipotentInParabolicHopfIdeal_comap (w : Fin N → ℤ) :
    (weightUnipotentInParabolicHopfIdeal R w).comap
        (weightParabolicCoordinateMap R w).hom
        (weightParabolicCoordinateMap_surjective R w) =
      weightUnipotentDefiningHopfIdeal R w := by
  have hker :
      HopfIdeal.kerOfSurjective (weightParabolicCoordinateMap R w).hom
          (weightParabolicCoordinateMap_surjective R w) =
        weightParabolicDefiningHopfIdeal R w := by
    ext x
    rw [HopfIdeal.mem_kerOfSurjective, weightParabolicCoordinateMap_apply,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, HopfIdeal.mem_toIdeal]
  rw [weightUnipotentInParabolicHopfIdeal,
    HopfIdeal.comap_map_of_surjective, hker, sup_eq_left]
  exact weightParabolicDefiningHopfIdeal_le_weightUnipotent R w

section Points

variable {A : Type v} [CommRing A] [Algebra R A]

/-- A parabolic point belongs to the subgroup cut out by the relative unipotent Hopf ideal
exactly when its ambient general linear point belongs to the weight-unipotent subgroup. -/
theorem mem_weightUnipotentInParabolicPointsSubgroup_iff (w : Fin N → ℤ)
    (f : HopfAlgebra.points (R := R) (H := weightParabolicCoordinateHopfAlgebra R w)
      (CommAlgCat.of R A)) :
    f ∈ CommHopfAlgCat.quotientPointsSubgroup
        (weightParabolicCoordinateHopfAlgebra R w)
        (weightUnipotentInParabolicHopfIdeal R w) (CommAlgCat.of R A) ↔
      CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
          (weightParabolicDefiningHopfIdeal R w) (CommAlgCat.of R A) f ∈
        CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R N)
          (weightUnipotentDefiningHopfIdeal R w) (CommAlgCat.of R A) := by
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff,
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  constructor
  · intro hf x hx
    have hqx := hf ((weightParabolicCoordinateMap R w).hom x)
      (HopfIdeal.mem_map_of_mem (weightParabolicCoordinateMap R w).hom hx)
    rw [weightParabolicCoordinateMap_apply] at hqx
    rw [CommHopfAlgCat.quotientPointsHom_apply_apply]
    exact hqx
  · intro hf y hy
    rw [weightUnipotentInParabolicHopfIdeal] at hy
    obtain ⟨x, hx, hxy⟩ :=
      (HopfIdeal.mem_map_iff_of_surjective
        (weightParabolicCoordinateMap_surjective R w)).mp hy
    subst y
    have hx0 := hf x hx
    rw [CommHopfAlgCat.quotientPointsHom_apply_apply] at hx0
    rw [weightParabolicCoordinateMap_apply]
    exact hx0

end Points

/-- The relative weight-unipotent Hopf ideal is normal in the weight-parabolic coordinate Hopf
algebra. Equivalently, the represented weight-unipotent subgroup is normal in the represented
weight parabolic over every commutative value algebra. -/
theorem weightUnipotentInParabolicHopfIdeal_isNormal (w : Fin N → ℤ) :
    (weightUnipotentInParabolicHopfIdeal R w).IsNormal := by
  rw [CommHopfAlgCat.isNormal_iff_quotientPointsSubgroup_normal]
  intro A
  refine ⟨fun n hn p ↦ ?_⟩
  rw [mem_weightUnipotentInParabolicPointsSubgroup_iff] at hn ⊢
  have hnDynamic :=
    (mem_weightUnipotentDefiningPointsSubgroup_iff R w _).mp hn
  have hpAmbient :
      CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
          (weightParabolicDefiningHopfIdeal R w) A p ∈
        CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R N)
          (weightParabolicDefiningHopfIdeal R w) A :=
    CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup
      (coordinateHopfAlgebra R N) (weightParabolicDefiningHopfIdeal R w) A p
  have hpDynamic :=
    (mem_weightParabolicDefiningPointsSubgroup_iff R w _).mp hpAmbient
  have hconj := Cocharacter.conj_mem_unipotent hpDynamic hnDynamic
  apply (mem_weightUnipotentDefiningPointsSubgroup_iff R w _).mpr
  simpa only [map_mul, map_inv] using hconj

/-- The closed immersion of the weight-unipotent group scheme into the weight-parabolic group
scheme induced by inclusion of their defining Hopf ideals. -/
noncomputable def weightUnipotentToParabolic (w : Fin N → ℤ) :
    weightUnipotentGroupScheme R w ⟶ weightParabolicGroupScheme R w :=
  CommHopfAlgCat.quotientSpecMapOfLe (coordinateHopfAlgebra R N)
    (weightParabolicDefiningHopfIdeal_le_weightUnipotent R w)

/-- The weight-unipotent-to-parabolic morphism is a closed immersion. -/
instance isClosedImmersion_weightUnipotentToParabolic (w : Fin N → ℤ) :
    IsClosedImmersion (weightUnipotentToParabolic R w).hom.hom.left := by
  rw [weightUnipotentToParabolic]
  infer_instance

/-- Including the weight-unipotent group scheme through the weight parabolic agrees with its
direct inclusion into the general linear group scheme. -/
@[simp]
theorem weightUnipotentToParabolic_comp_inclusion (w : Fin N → ℤ) :
    weightUnipotentToParabolic R w ≫ weightParabolicInclusion R w =
      weightUnipotentInclusion R w := by
  rw [weightUnipotentToParabolic, weightParabolicInclusion_def,
    weightUnipotentInclusion_def, ← Category.assoc,
    CommHopfAlgCat.quotientSpecMapOfLe_comp_quotientSpecι]

end TauCeti.GeneralLinear.Dynamic
