/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Levi
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Parabolic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Unipotent.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Map

/-!
# Weight Levi and unipotent subgroups inside weight parabolics

For an integer weight `w` on the standard representation, the weight-unipotent subgroup is a
closed normal subgroup of the corresponding weight parabolic. On coordinate rings, the
parabolic defining Hopf ideal is contained in the unipotent defining Hopf ideal. Mapping the
latter into the parabolic coordinate Hopf algebra therefore cuts out the same unipotent group
scheme, now regarded as a closed subgroup of the parabolic.

The weight Levi is likewise a closed subgroup of the weight parabolic. Its relative defining
Hopf ideal is the image of the ambient weight-Levi ideal in the parabolic coordinate algebra.
The resulting quotient spectrum is canonically the already-defined weight-Levi group scheme,
and its inclusion through the parabolic agrees with the direct inclusion into `GL_N`.

Normality is proved honestly at the scheme level. The functor-of-points criterion for a normal
Hopf ideal reduces it to conjugation over every commutative value algebra, where it is precisely
the existing dynamic statement that the weight parabolic normalizes its unipotent part.

## Main declarations

* `TauCeti.GeneralLinear.Dynamic.weightParabolicDefiningHopfIdeal_le_weightUnipotent`: the
  inclusion between the ambient defining Hopf ideals.
* `TauCeti.GeneralLinear.Dynamic.weightUnipotentInParabolicHopfIdeal`: the Hopf ideal in the
  parabolic coordinate algebra cutting out the unipotent subgroup.
* `TauCeti.GeneralLinear.Dynamic.isNormal_weightUnipotentInParabolicHopfIdeal`: scheme-level
  normality of the weight-unipotent subgroup in the weight parabolic.
* `TauCeti.GeneralLinear.Dynamic.weightUnipotentInParabolicGroupSchemeIso`: the canonical
  identification of the relative quotient spectrum with the weight-unipotent group scheme.
* `TauCeti.GeneralLinear.Dynamic.weightUnipotentToParabolic`: the resulting closed immersion of
  group schemes.
* `TauCeti.GeneralLinear.Dynamic.weightLeviInParabolicHopfIdeal`: the relative Hopf ideal cutting
  out the weight Levi inside the weight parabolic.
* `TauCeti.GeneralLinear.Dynamic.weightLeviInParabolicGroupSchemeIso`: its quotient spectrum is
  canonically the weight-Levi group scheme.
* `TauCeti.GeneralLinear.Dynamic.weightLeviToParabolic`: the compatible closed immersion of the
  weight Levi into the weight parabolic.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.

This advances the dynamic Levi-decomposition milestone in Layer 7, "Structure theory", of the
ReductiveGroups roadmap by supplying both represented factors inside the weight parabolic. The
relative Levi is the acting factor required by the scheme-level semidirect-product decomposition.
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

/-- The defining Hopf ideal of the weight parabolic is contained in that of the weight Levi.
Contravariantly, the weight-Levi group scheme is a closed subgroup of the weight-parabolic group
scheme. -/
theorem weightParabolicDefiningHopfIdeal_le_weightLevi (w : Fin N → ℤ) :
    weightParabolicDefiningHopfIdeal R w ≤ weightLeviDefiningHopfIdeal R w := by
  rw [weightLeviDefiningHopfIdeal_def]
  exact le_sup_left

/-- The Hopf ideal in the weight-parabolic coordinate algebra which cuts out the weight Levi. -/
noncomputable def weightLeviInParabolicHopfIdeal (w : Fin N → ℤ) :
    HopfIdeal R (weightParabolicCoordinateHopfAlgebra R w) :=
  (weightLeviDefiningHopfIdeal R w).map (weightParabolicCoordinateMap R w).hom

/-- Pulling the relative weight-Levi Hopf ideal back to the ambient general linear coordinate
algebra recovers the original weight-Levi defining ideal. -/
@[simp]
theorem weightLeviInParabolicHopfIdeal_comapOfSurjective (w : Fin N → ℤ) :
    (weightLeviInParabolicHopfIdeal R w).comapOfSurjective
        (weightParabolicCoordinateMap R w).hom
        (weightParabolicCoordinateMap_surjective R w) =
      weightLeviDefiningHopfIdeal R w := by
  have hker :
      HopfIdeal.kerOfSurjective (weightParabolicCoordinateMap R w).hom
          (weightParabolicCoordinateMap_surjective R w) =
        weightParabolicDefiningHopfIdeal R w := by
    ext x
    rw [HopfIdeal.mem_kerOfSurjective, weightParabolicCoordinateMap_apply,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, HopfIdeal.mem_toIdeal]
  rw [weightLeviInParabolicHopfIdeal,
    HopfIdeal.comapOfSurjective_map, hker, sup_eq_left]
  exact weightParabolicDefiningHopfIdeal_le_weightLevi R w

/-- The Hopf ideal in the weight-parabolic coordinate algebra which cuts out the
weight-unipotent subgroup. -/
noncomputable def weightUnipotentInParabolicHopfIdeal (w : Fin N → ℤ) :
    HopfIdeal R (weightParabolicCoordinateHopfAlgebra R w) :=
  (weightUnipotentDefiningHopfIdeal R w).map (weightParabolicCoordinateMap R w).hom

/-- Pulling the relative weight-unipotent Hopf ideal back to the ambient general linear
coordinate algebra recovers the original weight-unipotent defining ideal. -/
@[simp]
theorem weightUnipotentInParabolicHopfIdeal_comapOfSurjective (w : Fin N → ℤ) :
    (weightUnipotentInParabolicHopfIdeal R w).comapOfSurjective
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
    HopfIdeal.comapOfSurjective_map, hker, sup_eq_left]
  exact weightParabolicDefiningHopfIdeal_le_weightUnipotent R w

section Points

variable {A : Type v} [CommRing A] [Algebra R A]

/-- A parabolic point belongs to the subgroup cut out by the relative Levi Hopf ideal exactly
when its ambient general linear point belongs to the weight-Levi subgroup. -/
@[simp]
theorem mem_weightLeviInParabolicPointsSubgroup_iff (w : Fin N → ℤ)
    (f : HopfAlgebra.points (R := R) (H := weightParabolicCoordinateHopfAlgebra R w)
      (CommAlgCat.of R A)) :
    f ∈ CommHopfAlgCat.quotientPointsSubgroup
        (weightParabolicCoordinateHopfAlgebra R w)
        (weightLeviInParabolicHopfIdeal R w) (CommAlgCat.of R A) ↔
      CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
          (weightParabolicDefiningHopfIdeal R w) (CommAlgCat.of R A) f ∈
        CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R N)
          (weightLeviDefiningHopfIdeal R w) (CommAlgCat.of R A) := by
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
    rw [weightLeviInParabolicHopfIdeal] at hy
    obtain ⟨x, hx, hxy⟩ :=
      (HopfIdeal.mem_map_iff_of_surjective
        (weightParabolicCoordinateMap_surjective R w)).mp hy
    subst y
    have hx0 := hf x hx
    rw [CommHopfAlgCat.quotientPointsHom_apply_apply] at hx0
    rw [weightParabolicCoordinateMap_apply]
    exact hx0

/-- A parabolic point belongs to the subgroup cut out by the relative unipotent Hopf ideal
exactly when its ambient general linear point belongs to the weight-unipotent subgroup. -/
@[simp]
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
theorem isNormal_weightUnipotentInParabolicHopfIdeal (w : Fin N → ℤ) :
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

private theorem mkQuotient_comp_eqToIso {H : _root_.CommHopfAlgCat.{u} R}
    {I J : HopfIdeal R H} (hIJ : I = J) :
    CommHopfAlgCat.mkQuotient H I ≫
        (eqToIso (congrArg (CommHopfAlgCat.quotient H) hIJ)).hom =
      CommHopfAlgCat.mkQuotient H J := by
  subst J
  simp

/-- The quotient-coordinate isomorphism underlying the identification of the relative
weight-Levi quotient spectrum. -/
private noncomputable def weightLeviInParabolicCoordinateIso (w : Fin N → ℤ) :
    weightLeviCoordinateHopfAlgebra R w ≅
      CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
        (weightLeviInParabolicHopfIdeal R w) :=
  eqToIso (congrArg (CommHopfAlgCat.quotient (coordinateHopfAlgebra R N))
      (weightLeviInParabolicHopfIdeal_comapOfSurjective R w).symm) ≪≫
    CommHopfAlgCat.quotientIsoOfSurjective
      (weightParabolicCoordinateMap R w)
      (weightParabolicCoordinateMap_surjective R w)
      (weightLeviInParabolicHopfIdeal R w)

/-- The relative quotient spectrum cut out inside the weight parabolic is canonically
isomorphic to the weight-Levi group scheme. -/
noncomputable def weightLeviInParabolicGroupSchemeIso (w : Fin N → ℤ) :
    CommHopfAlgCat.quotientSpec (weightParabolicCoordinateHopfAlgebra R w)
        (weightLeviInParabolicHopfIdeal R w) ≅
      weightLeviGroupScheme R w :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).mapIso
    (weightLeviInParabolicCoordinateIso R w).op

/-- The closed immersion of the weight-Levi group scheme into the weight-parabolic group scheme
induced by inclusion of their defining Hopf ideals. -/
noncomputable def weightLeviToParabolic (w : Fin N → ℤ) :
    weightLeviGroupScheme R w ⟶ weightParabolicGroupScheme R w :=
  CommHopfAlgCat.quotientSpecMapOfLe (coordinateHopfAlgebra R N)
    (weightParabolicDefiningHopfIdeal_le_weightLevi R w)

/-- The weight-Levi-to-parabolic morphism is a closed immersion. -/
instance isClosedImmersion_weightLeviToParabolic (w : Fin N → ℤ) :
    IsClosedImmersion (weightLeviToParabolic R w).hom.hom.left := by
  rw [weightLeviToParabolic]
  infer_instance

/-- Including the weight-Levi group scheme through the weight parabolic agrees with its direct
inclusion into the general linear group scheme. -/
@[simp]
theorem weightLeviToParabolic_comp_inclusion (w : Fin N → ℤ) :
    weightLeviToParabolic R w ≫ weightParabolicInclusion R w =
      weightLeviInclusion R w := by
  rw [weightLeviToParabolic, weightParabolicInclusion_def,
    weightLeviInclusion_def, ← Category.assoc,
    CommHopfAlgCat.quotientSpecMapOfLe_comp_quotientSpecι]

/-- Under the canonical identification with the weight-Levi group scheme, the relative
quotient-spectrum inclusion is `weightLeviToParabolic`. -/
@[simp]
theorem weightLeviInParabolicGroupSchemeIso_hom_comp_weightLeviToParabolic
    (w : Fin N → ℤ) :
    (weightLeviInParabolicGroupSchemeIso R w).hom ≫ weightLeviToParabolic R w =
      CommHopfAlgCat.quotientSpecι (weightParabolicCoordinateHopfAlgebra R w)
        (weightLeviInParabolicHopfIdeal R w) := by
  rw [weightLeviInParabolicGroupSchemeIso, weightLeviToParabolic,
    CommHopfAlgCat.quotientSpecMapOfLe_def, CommHopfAlgCat.quotientSpecι_def,
    Functor.mapIso_hom, Iso.op_hom,
    ← (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map_comp, ← op_comp]
  congr 2
  let q := weightParabolicCoordinateMap R w
  let hq := weightParabolicCoordinateMap_surjective R w
  let _ : Epi q := ConcreteCategory.epi_of_surjective q hq
  rw [← cancel_epi q]
  have hq_def : weightParabolicCoordinateMap R w =
      CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra R N)
        (weightParabolicDefiningHopfIdeal R w) := by
    ext x
    rw [weightParabolicCoordinateMap_apply, CommHopfAlgCat.mkQuotient_apply]
  dsimp only [q]
  rw [hq_def, ← Category.assoc,
    CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe]
  rw [weightLeviInParabolicCoordinateIso, Iso.trans_hom, ← Category.assoc,
    mkQuotient_comp_eqToIso (R := R)
      (weightLeviInParabolicHopfIdeal_comapOfSurjective R w).symm,
    CommHopfAlgCat.mkQuotient_comp_quotientIsoOfSurjective_hom, hq_def]

/-- The quotient-coordinate isomorphism underlying the identification of the relative
weight-unipotent quotient spectrum. -/
private noncomputable def weightUnipotentInParabolicCoordinateIso (w : Fin N → ℤ) :
    weightUnipotentCoordinateHopfAlgebra R w ≅
      CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
        (weightUnipotentInParabolicHopfIdeal R w) :=
  eqToIso (congrArg (CommHopfAlgCat.quotient (coordinateHopfAlgebra R N))
      (weightUnipotentInParabolicHopfIdeal_comapOfSurjective R w).symm) ≪≫
    CommHopfAlgCat.quotientIsoOfSurjective
      (weightParabolicCoordinateMap R w)
      (weightParabolicCoordinateMap_surjective R w)
      (weightUnipotentInParabolicHopfIdeal R w)

/-- The relative quotient spectrum cut out inside the weight parabolic is canonically
isomorphic to the weight-unipotent group scheme. -/
noncomputable def weightUnipotentInParabolicGroupSchemeIso (w : Fin N → ℤ) :
    CommHopfAlgCat.quotientSpec (weightParabolicCoordinateHopfAlgebra R w)
        (weightUnipotentInParabolicHopfIdeal R w) ≅
      weightUnipotentGroupScheme R w :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).mapIso
    (weightUnipotentInParabolicCoordinateIso R w).op

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

/-- Under the canonical identification with the weight-unipotent group scheme, the relative
quotient-spectrum inclusion is `weightUnipotentToParabolic`. -/
@[simp]
theorem weightUnipotentInParabolicGroupSchemeIso_hom_comp_weightUnipotentToParabolic
    (w : Fin N → ℤ) :
    (weightUnipotentInParabolicGroupSchemeIso R w).hom ≫
        weightUnipotentToParabolic R w =
      CommHopfAlgCat.quotientSpecι (weightParabolicCoordinateHopfAlgebra R w)
        (weightUnipotentInParabolicHopfIdeal R w) := by
  rw [weightUnipotentInParabolicGroupSchemeIso, weightUnipotentToParabolic,
    CommHopfAlgCat.quotientSpecMapOfLe_def, CommHopfAlgCat.quotientSpecι_def,
    Functor.mapIso_hom, Iso.op_hom,
    ← (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map_comp, ← op_comp]
  congr 2
  let q := weightParabolicCoordinateMap R w
  let hq := weightParabolicCoordinateMap_surjective R w
  let _ : Epi q := ConcreteCategory.epi_of_surjective q hq
  rw [← cancel_epi q]
  have hq_def : weightParabolicCoordinateMap R w =
      CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra R N)
        (weightParabolicDefiningHopfIdeal R w) := by
    ext x
    rw [weightParabolicCoordinateMap_apply, CommHopfAlgCat.mkQuotient_apply]
  dsimp only [q]
  rw [hq_def, ← Category.assoc,
    CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe]
  rw [weightUnipotentInParabolicCoordinateIso, Iso.trans_hom, ← Category.assoc,
    mkQuotient_comp_eqToIso (R := R)
      (weightUnipotentInParabolicHopfIdeal_comapOfSurjective R w).symm,
    CommHopfAlgCat.mkQuotient_comp_quotientIsoOfSurjective_hom, hq_def]

end TauCeti.GeneralLinear.Dynamic
