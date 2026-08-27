/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.LeviDecomposition.Naturality
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Normal
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Order

/-!
# The limit morphism from a weight parabolic to its Levi subgroup

Let `w : Fin N → ℤ` and let `P(w)` and `L(w)` be the represented weight parabolic and Levi
subgroups of `GL_N`. The dynamic limit

```text
g ↦ lim_{t → 0} diag(t ^ w) g diag(t ^ (-w))
```

is natural in the commutative value algebra. Yoneda therefore represents it by a morphism of
coordinate Hopf algebras `O(L(w)) → O(P(w))`, and hence by a group-scheme morphism
`P(w) → L(w)`. Its effect on points is exactly the dynamic limit, not merely an abstract
existence statement.

This is the retraction needed to extract the Levi coordinate in the represented semidirect-product
decomposition of `P(w)`.

## Main declarations

* `TauCeti.GeneralLinear.Dynamic.weightParabolicLimitPointsMap`: the natural limit map on
  represented points.
* `TauCeti.GeneralLinear.Dynamic.weightLeviToParabolicPointsMap`: the natural represented Levi
  inclusion, which is a section of the limit map.
* `TauCeti.GeneralLinear.Dynamic.weightLeviToParabolicCoordinateMap`: the quotient coordinate
  map representing that inclusion.
* `TauCeti.GeneralLinear.Dynamic.weightParabolicLimitCoordinateMap`: its representing coordinate
  Hopf-algebra morphism.
* `TauCeti.GeneralLinear.Dynamic.weightParabolicLimit`: the corresponding group-scheme morphism
  from the weight parabolic to the weight Levi.
* `TauCeti.GeneralLinear.Dynamic.weightLeviToParabolic_comp_weightParabolicLimit`: the
  group-scheme retraction identity.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.

This advances the dynamic route to parabolic subgroups and Levi decomposition in Layer 7,
"Structure theory", of the ReductiveGroups roadmap. The remaining step is to combine this
represented retraction with the represented unipotent and Levi inclusions to identify `P(w)` with
their semidirect product.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite

namespace TauCeti.GeneralLinear.Dynamic

universe u

noncomputable section

variable (R : Type u) [CommRing R] {N : ℕ}

/-- The natural transformation on represented points obtained by transporting the dynamic limit
from the weight parabolic to the weight Levi. -/
@[expose] noncomputable def weightParabolicLimitPointsMap (w : Fin N → ℤ) :
    HopfAlgebra.pointsFunctor (R := R) (H := weightParabolicCoordinateHopfAlgebra R w) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := weightLeviCoordinateHopfAlgebra R w) :=
  (weightParabolicPointsIso R w).hom ≫
    Cocharacter.limitToLeviNatTrans (weightCocharacter (R := R) w) ≫
    (weightLeviPointsIso R w).inv

/-- The natural inclusion of represented weight-Levi points into represented weight-parabolic
points, transported from the dynamic subgroup inclusion. -/
@[expose] noncomputable def weightLeviToParabolicPointsMap (w : Fin N → ℤ) :
    HopfAlgebra.pointsFunctor (R := R) (H := weightLeviCoordinateHopfAlgebra R w) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := weightParabolicCoordinateHopfAlgebra R w) :=
  (weightLeviPointsIso R w).hom ≫
    Cocharacter.leviToParabolicNatTrans (weightCocharacter (R := R) w) ≫
    (weightParabolicPointsIso R w).inv

/-- At every value algebra, the represented Levi inclusion is the dynamic subgroup inclusion
transported through the representing isomorphisms. -/
@[simp]
theorem weightLeviToParabolicPointsMap_app_apply (w : Fin N → ℤ)
    (A : CommAlgCat.{u} R)
    (z : HopfAlgebra.points (R := R) (H := weightLeviCoordinateHopfAlgebra R w) A) :
    (weightLeviToParabolicPointsMap R w).app A z =
      (weightParabolicPointsIso R w).inv.app A
        (Cocharacter.leviToParabolic A (weightCocharacter (R := R) w)
          ((weightLeviPointsIso R w).hom.app A z)) := by
  rfl

/-- The natural represented Levi inclusion is a section of the represented dynamic limit. -/
@[simp]
theorem weightLeviToParabolicPointsMap_comp_weightParabolicLimitPointsMap
    (w : Fin N → ℤ) :
    weightLeviToParabolicPointsMap R w ≫ weightParabolicLimitPointsMap R w =
      𝟙 (HopfAlgebra.pointsFunctor
        (R := R) (H := weightLeviCoordinateHopfAlgebra R w)) := by
  simp only [weightLeviToParabolicPointsMap, weightParabolicLimitPointsMap,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc
    (Cocharacter.leviToParabolicNatTrans (weightCocharacter (R := R) w))
    (Cocharacter.limitToLeviNatTrans (weightCocharacter (R := R) w))
    (weightLeviPointsIso R w).inv]
  rw [Cocharacter.leviToParabolicNatTrans_comp_limitToLeviNatTrans,
    Category.id_comp, Iso.hom_inv_id]

/-- Pointwise, the represented weight-Levi inclusion is a right inverse to the represented
dynamic limit. -/
theorem weightParabolicLimitPointsMap_rightInverse (w : Fin N → ℤ)
    (A : CommAlgCat.{u} R) :
    Function.RightInverse ((weightLeviToParabolicPointsMap R w).app A)
      ((weightParabolicLimitPointsMap R w).app A) := by
  intro z
  have h := NatTrans.congr_app
    (weightLeviToParabolicPointsMap_comp_weightParabolicLimitPointsMap R w) A
  simpa only [NatTrans.vcomp_app', NatTrans.id_app, GrpCat.comp_apply,
    GrpCat.id_apply] using
    ConcreteCategory.congr_hom h z

/-- The coordinate morphism representing the inclusion `L(w) → P(w)`. It is the canonical
map between the two quotient coordinate Hopf algebras induced by containment of their defining
Hopf ideals. -/
@[expose] noncomputable def weightLeviToParabolicCoordinateMap (w : Fin N → ℤ) :
    weightParabolicCoordinateHopfAlgebra R w ⟶ weightLeviCoordinateHopfAlgebra R w :=
  CommHopfAlgCat.quotientMapOfLe (coordinateHopfAlgebra R N)
    (weightParabolicDefiningHopfIdeal_le_weightLevi R w)

/-- On points over a same-universe commutative algebra, the canonical quotient coordinate map is
the represented dynamic Levi inclusion. -/
@[simp]
theorem mapPointsFunctor_weightLeviToParabolicCoordinateMap_app (w : Fin N → ℤ)
    {A : Type u} [CommRing A] [Algebra R A]
    (z : HopfAlgebra.points (R := R) (H := weightLeviCoordinateHopfAlgebra R w)
      (CommAlgCat.of R A)) :
    (CommHopfAlgCat.mapPointsFunctor (weightLeviToParabolicCoordinateMap R w)).app
        (CommAlgCat.of R A) z =
      (weightLeviToParabolicPointsMap R w).app (CommAlgCat.of R A) z := by
  apply CommHopfAlgCat.quotientPointsHom_injective
    (coordinateHopfAlgebra R N) (weightParabolicDefiningHopfIdeal R w)
    (CommAlgCat.of R A)
  rw [weightLeviToParabolicCoordinateMap,
    CommHopfAlgCat.quotientPointsHom_mapPointsFunctor_quotientMapOfLe_app,
    weightLeviToParabolicPointsMap_app_apply,
    quotientPointsHom_weightParabolicPointsIso_inv_app_apply]
  let zDynamic : Cocharacter.levi (CommAlgCat.of R A)
      (weightCocharacter (R := R) w) :=
    eqToHom (Cocharacter.leviFunctor_obj
      (weightCocharacter (R := R) w) (CommAlgCat.of R A))
      ((weightLeviPointsIso R w).hom.app (CommAlgCat.of R A) z)
  calc
    CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
        (weightLeviDefiningHopfIdeal R w) (CommAlgCat.of R A) z =
        (zDynamic : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N)
          (CommAlgCat.of R A)) :=
      (coe_weightLeviPointsIso_hom_app_apply R w z).symm
    _ = (Cocharacter.leviToParabolic (CommAlgCat.of R A)
          (weightCocharacter (R := R) w) zDynamic :
          HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N)
            (CommAlgCat.of R A)) :=
      (Cocharacter.coe_leviToParabolic_apply (CommAlgCat.of R A)
        (weightCocharacter (R := R) w) zDynamic).symm

/-- The canonical quotient coordinate map induces the represented dynamic Levi inclusion on
points. -/
theorem mapPointsFunctor_weightLeviToParabolicCoordinateMap (w : Fin N → ℤ) :
    (CommHopfAlgCat.mapPointsFunctor.{u, u, u}
      (weightLeviToParabolicCoordinateMap R w) :
      HopfAlgebra.pointsFunctor (R := R) (H := weightLeviCoordinateHopfAlgebra R w) ⟶
        HopfAlgebra.pointsFunctor (R := R) (H := weightParabolicCoordinateHopfAlgebra R w)) =
      weightLeviToParabolicPointsMap R w := by
  ext A z
  rcases A with ⟨A⟩
  exact mapPointsFunctor_weightLeviToParabolicCoordinateMap_app R w z

/-- At every value algebra, the represented limit map is the dynamic limit transported through
the representing isomorphisms for the weight parabolic and weight Levi. -/
@[simp]
theorem weightParabolicLimitPointsMap_app_apply (w : Fin N → ℤ)
    (A : CommAlgCat.{u} R)
    (g : HopfAlgebra.points (R := R) (H := weightParabolicCoordinateHopfAlgebra R w) A) :
    (weightParabolicLimitPointsMap R w).app A g =
      (weightLeviPointsIso R w).inv.app A
        (Cocharacter.limitToLevi A (weightCocharacter (R := R) w)
          ((weightParabolicPointsIso R w).hom.app A g)) := by
  rfl

/-- The coordinate morphism representing the limit `P(w) → L(w)`. Its direction is
`O(L(w)) → O(P(w))`, opposite to the group-scheme morphism. -/
noncomputable def weightParabolicLimitCoordinateMap (w : Fin N → ℤ) :
    weightLeviCoordinateHopfAlgebra R w ⟶ weightParabolicCoordinateHopfAlgebra R w :=
  ((CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}).preimage
    (weightParabolicLimitPointsMap R w)).unop

/-- Precomposition by the limit coordinate morphism is the natural dynamic limit map on
represented points. -/
theorem mapPointsFunctor_weightParabolicLimitCoordinateMap (w : Fin N → ℤ) :
    (CommHopfAlgCat.mapPointsFunctor.{u, u, u}
      (weightParabolicLimitCoordinateMap R w) :
      HopfAlgebra.pointsFunctor (R := R) (H := weightParabolicCoordinateHopfAlgebra R w) ⟶
        HopfAlgebra.pointsFunctor (R := R) (H := weightLeviCoordinateHopfAlgebra R w)) =
      weightParabolicLimitPointsMap R w := by
  unfold weightParabolicLimitCoordinateMap
  rw [← CommHopfAlgCat.pointsFunctor_map]
  exact Functor.map_preimage
    (CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}) _

/-- The limit coordinate morphism is a section of the coordinate morphism representing the
Levi inclusion. This is the coordinate-ring form of the retraction `P(w) → L(w)`. -/
@[simp]
theorem weightParabolicLimitCoordinateMap_comp_weightLeviToParabolicCoordinateMap
    (w : Fin N → ℤ) :
    weightParabolicLimitCoordinateMap R w ≫ weightLeviToParabolicCoordinateMap R w =
      𝟙 (weightLeviCoordinateHopfAlgebra R w) := by
  apply Quiver.Hom.op_inj
  apply (CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R) :
    (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}).map_injective
  change CommHopfAlgCat.mapPointsFunctor (weightLeviToParabolicCoordinateMap R w) ≫
      CommHopfAlgCat.mapPointsFunctor (weightParabolicLimitCoordinateMap R w) = 𝟙 _
  rw [mapPointsFunctor_weightLeviToParabolicCoordinateMap,
    mapPointsFunctor_weightParabolicLimitCoordinateMap,
    weightLeviToParabolicPointsMap_comp_weightParabolicLimitPointsMap]

/-- On every same-universe value algebra, the morphism induced by the limit coordinate map is
the dynamic limit transported to the represented weight-Levi points. -/
@[simp]
theorem mapPointsFunctor_weightParabolicLimitCoordinateMap_app (w : Fin N → ℤ)
    (A : CommAlgCat.{u} R)
    (g : HopfAlgebra.points (R := R) (H := weightParabolicCoordinateHopfAlgebra R w) A) :
    (CommHopfAlgCat.mapPointsFunctor (weightParabolicLimitCoordinateMap R w)).app A g =
      (weightLeviPointsIso R w).inv.app A
        (Cocharacter.limitToLevi A (weightCocharacter (R := R) w)
          ((weightParabolicPointsIso R w).hom.app A g)) := by
  rw [mapPointsFunctor_weightParabolicLimitCoordinateMap]
  exact weightParabolicLimitPointsMap_app_apply R w A g

/-- The group-scheme morphism `P(w) → L(w)` represented by the dynamic limit. -/
@[expose] noncomputable def weightParabolicLimit (w : Fin N → ℤ) :
    weightParabolicGroupScheme R w ⟶ weightLeviGroupScheme R w :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
    (weightParabolicLimitCoordinateMap R w).op

/-- The weight-parabolic limit is relative spectrum applied contravariantly to its coordinate
Hopf-algebra morphism. -/
theorem weightParabolicLimit_def (w : Fin N → ℤ) :
    weightParabolicLimit R w =
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
        (weightParabolicLimitCoordinateMap R w).op :=
  rfl

/-- The represented dynamic limit retracts the existing closed immersion of the weight Levi into
the weight parabolic. -/
@[simp]
theorem weightLeviToParabolic_comp_weightParabolicLimit (w : Fin N → ℤ) :
    weightLeviToParabolic R w ≫ weightParabolicLimit R w =
      𝟙 (weightLeviGroupScheme R w) := by
  unfold weightLeviToParabolic
  rw [CommHopfAlgCat.quotientSpecMapOfLe_def, weightParabolicLimit_def,
    ← (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map_comp,
    ← op_comp]
  change (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
      (weightParabolicLimitCoordinateMap R w ≫
        weightLeviToParabolicCoordinateMap R w).op = _
  rw [weightParabolicLimitCoordinateMap_comp_weightLeviToParabolicCoordinateMap]
  exact (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map_id _

end

end TauCeti.GeneralLinear.Dynamic
