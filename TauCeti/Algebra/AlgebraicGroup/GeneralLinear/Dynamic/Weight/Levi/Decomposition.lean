/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.LeviDecomposition.Naturality
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Normal

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
* `TauCeti.GeneralLinear.Dynamic.weightParabolicLimitCoordinateMap`: its representing coordinate
  Hopf-algebra morphism.
* `TauCeti.GeneralLinear.Dynamic.weightParabolicLimit`: the corresponding group-scheme morphism
  from the weight parabolic to the weight Levi.
* `TauCeti.GeneralLinear.Dynamic.schemePointsAlgΓMulEquiv_weightParabolicLimit`: its dynamic
  formula on points valued in an arbitrary scheme over the base.
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

open AlgebraicGeometry CategoryTheory Opposite WithConv

namespace TauCeti.GeneralLinear.Dynamic

universe u v

noncomputable section

variable (R : Type u) [CommRing R] {N : ℕ}

private theorem comp_comp_app_apply {C : Type*} [Category C]
    {F G H K : C ⥤ GrpCat} (α : F ⟶ G) (β : G ⟶ H) (γ : H ⟶ K)
    (A : C) (x : F.obj A) :
    (α ≫ β ≫ γ).app A x = γ.app A (β.app A (α.app A x)) := by
  rw [NatTrans.vcomp_app', NatTrans.vcomp_app', GrpCat.comp_apply, GrpCat.comp_apply]

/-- The natural transformation on represented points obtained by transporting the dynamic limit
from the weight parabolic to the weight Levi. -/
noncomputable def weightParabolicLimitPointsMap (w : Fin N → ℤ) :
    HopfAlgebra.pointsFunctor.{u, u, v}
        (R := R) (H := weightParabolicCoordinateHopfAlgebra R w) ⟶
      HopfAlgebra.pointsFunctor.{u, u, v}
        (R := R) (H := weightLeviCoordinateHopfAlgebra R w) :=
  (weightParabolicPointsIso R w).hom ≫
    Cocharacter.limitToLeviNatTrans (weightCocharacter (R := R) w) ≫
    (weightLeviPointsIso R w).inv

/-- The represented limit map is the dynamic limit transported through the representing
isomorphisms for the weight parabolic and weight Levi. -/
theorem weightParabolicLimitPointsMap_def (w : Fin N → ℤ) :
    weightParabolicLimitPointsMap R w =
      (weightParabolicPointsIso R w).hom ≫
        Cocharacter.limitToLeviNatTrans (weightCocharacter (R := R) w) ≫
        (weightLeviPointsIso R w).inv := (rfl)

/-- At every value algebra, the represented limit map is the dynamic limit transported through
the representing isomorphisms for the weight parabolic and weight Levi. -/
@[simp]
theorem weightParabolicLimitPointsMap_app_apply (w : Fin N → ℤ)
    (A : CommAlgCat.{v} R)
    (g : HopfAlgebra.points (R := R) (H := weightParabolicCoordinateHopfAlgebra R w) A) :
    (weightParabolicLimitPointsMap R w).app A g =
      (weightLeviPointsIso R w).inv.app A
        (Cocharacter.limitToLevi A (weightCocharacter (R := R) w)
          ((weightParabolicPointsIso R w).hom.app A g)) := by
  calc
    (weightParabolicLimitPointsMap R w).app A g =
        (((weightParabolicPointsIso R w).hom ≫
          Cocharacter.limitToLeviNatTrans (weightCocharacter (R := R) w) ≫
          (weightLeviPointsIso R w).inv).app A) g :=
      ConcreteCategory.congr_hom
        (NatTrans.congr_app (weightParabolicLimitPointsMap_def R w) A) g
    _ = (weightLeviPointsIso R w).inv.app A
          (Cocharacter.limitToLevi A (weightCocharacter (R := R) w)
            ((weightParabolicPointsIso R w).hom.app A g)) := by
      calc
        _ = (weightLeviPointsIso R w).inv.app A
              ((Cocharacter.limitToLeviNatTrans
                (weightCocharacter (R := R) w)).app A
                ((weightParabolicPointsIso R w).hom.app A
                  (show (HopfAlgebra.pointsFunctor
                    (R := R) (H := weightParabolicCoordinateHopfAlgebra R w)).obj A from g))) :=
          comp_comp_app_apply _ _ _ A _
        _ = _ := congrArg
          (fun z ↦ (weightLeviPointsIso R w).inv.app A z)
          (ConcreteCategory.congr_hom
            (Cocharacter.limitToLeviNatTrans_app
              (weightCocharacter (R := R) w) A)
            ((weightParabolicPointsIso R w).hom.app A g))

private theorem mapPointsFunctor_weightLeviToParabolicCoordinateMap_eq_transported
    (w : Fin N → ℤ) :
    (CommHopfAlgCat.mapPointsFunctor.{u, u, v}
      (weightLeviToParabolicCoordinateMap R w) :
      HopfAlgebra.pointsFunctor (R := R) (H := weightLeviCoordinateHopfAlgebra R w) ⟶
        HopfAlgebra.pointsFunctor (R := R) (H := weightParabolicCoordinateHopfAlgebra R w)) =
      (weightLeviPointsIso R w).hom ≫
        Cocharacter.leviToParabolicNatTrans (weightCocharacter (R := R) w) ≫
        (weightParabolicPointsIso R w).inv := by
  ext A z
  rcases A with ⟨A⟩
  -- `pointsFunctor.obj` is the bundled group on `HopfAlgebra.points`; expose that carrier once
  -- so the public pointwise formula applies to the component supplied by extensionality.
  change HopfAlgebra.points
    (R := R) (H := weightLeviCoordinateHopfAlgebra R w) (CommAlgCat.of R A) at z
  calc
    _ = (weightParabolicPointsIso R w).inv.app (CommAlgCat.of R A)
          (Cocharacter.leviToParabolic (CommAlgCat.of R A)
            (weightCocharacter (R := R) w)
            ((weightLeviPointsIso R w).hom.app (CommAlgCat.of R A)
              z)) :=
      mapPointsFunctor_weightLeviToParabolicCoordinateMap_app R w _ _
    _ = _ := by
      symm
      calc
        _ = (weightParabolicPointsIso R w).inv.app (CommAlgCat.of R A)
              ((Cocharacter.leviToParabolicNatTrans
                (weightCocharacter (R := R) w)).app (CommAlgCat.of R A)
                ((weightLeviPointsIso R w).hom.app (CommAlgCat.of R A) z)) :=
          comp_comp_app_apply _ _ _ (CommAlgCat.of R A) _
        _ = _ := congrArg
          (fun g ↦ (weightParabolicPointsIso R w).inv.app (CommAlgCat.of R A) g)
          (ConcreteCategory.congr_hom
            (Cocharacter.leviToParabolicNatTrans_app
              (weightCocharacter (R := R) w) (CommAlgCat.of R A))
            ((weightLeviPointsIso R w).hom.app (CommAlgCat.of R A) z))

/-- The canonical represented Levi inclusion is a section of the represented dynamic limit. -/
@[simp]
theorem mapPointsFunctor_weightLeviToParabolicCoordinateMap_comp_weightParabolicLimitPointsMap
    (w : Fin N → ℤ) :
    CommHopfAlgCat.mapPointsFunctor.{u, u, v}
        (weightLeviToParabolicCoordinateMap R w) ≫
      weightParabolicLimitPointsMap R w =
      𝟙 (HopfAlgebra.pointsFunctor.{u, u, v}
        (R := R) (H := weightLeviCoordinateHopfAlgebra R w)) := by
  simp only [mapPointsFunctor_weightLeviToParabolicCoordinateMap_eq_transported,
    weightParabolicLimitPointsMap_def, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc
    (Cocharacter.leviToParabolicNatTrans (weightCocharacter (R := R) w))
    (Cocharacter.limitToLeviNatTrans (weightCocharacter (R := R) w))
    (weightLeviPointsIso R w).inv]
  rw [Cocharacter.leviToParabolicNatTrans_comp_limitToLeviNatTrans,
    Category.id_comp, Iso.hom_inv_id]

/-- Pointwise, the canonical represented weight-Levi inclusion is a right inverse to the
represented dynamic limit. -/
theorem weightParabolicLimitPointsMap_rightInverse (w : Fin N → ℤ)
    (A : CommAlgCat.{v} R) :
    Function.RightInverse
      ((CommHopfAlgCat.mapPointsFunctor
        (weightLeviToParabolicCoordinateMap R w)).app A)
      ((weightParabolicLimitPointsMap R w).app A) := by
  intro z
  have h := NatTrans.congr_app
    (mapPointsFunctor_weightLeviToParabolicCoordinateMap_comp_weightParabolicLimitPointsMap
      R w) A
  simpa only [NatTrans.vcomp_app', NatTrans.id_app, GrpCat.comp_apply,
    GrpCat.id_apply] using
    ConcreteCategory.congr_hom h z

/-- The coordinate morphism representing the limit `P(w) → L(w)`. Its direction is
`O(L(w)) → O(P(w))`, opposite to the group-scheme morphism. -/
noncomputable def weightParabolicLimitCoordinateMap (w : Fin N → ℤ) :
    weightLeviCoordinateHopfAlgebra R w ⟶ weightParabolicCoordinateHopfAlgebra R w :=
  ((CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}).preimage
    (weightParabolicLimitPointsMap R w)).unop

/-- Precomposition by the limit coordinate morphism is the natural dynamic limit map on
represented points. -/
private theorem mapPointsFunctor_weightParabolicLimitCoordinateMap_sameUniverse
    (w : Fin N → ℤ) :
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
  -- The points functor is contravariant, so the coordinate composite appears in reverse order.
  -- Writing it as `mapPointsFunctor` lets the two representing-map theorems rewrite it.
  change CommHopfAlgCat.mapPointsFunctor (weightLeviToParabolicCoordinateMap R w) ≫
      CommHopfAlgCat.mapPointsFunctor (weightParabolicLimitCoordinateMap R w) = 𝟙 _
  rw [mapPointsFunctor_weightParabolicLimitCoordinateMap_sameUniverse,
    mapPointsFunctor_weightLeviToParabolicCoordinateMap_comp_weightParabolicLimitPointsMap]

/-- On every commutative value algebra, the morphism induced by the limit coordinate map is the
dynamic limit transported to the represented weight-Levi points. -/
@[simp]
theorem mapPointsFunctor_weightParabolicLimitCoordinateMap_app (w : Fin N → ℤ)
    (A : CommAlgCat.{v} R)
    (g : HopfAlgebra.points (R := R) (H := weightParabolicCoordinateHopfAlgebra R w) A) :
    (CommHopfAlgCat.mapPointsFunctor (weightParabolicLimitCoordinateMap R w)).app A g =
      (weightLeviPointsIso R w).inv.app A
        (Cocharacter.limitToLevi A (weightCocharacter (R := R) w)
          ((weightParabolicPointsIso R w).hom.app A g)) := by
  rcases A with ⟨A⟩
  let P := weightParabolicCoordinateHopfAlgebra R w
  let PAlg : CommAlgCat.{u} R := CommAlgCat.of R P
  let q : HopfAlgebra.points (R := R) (H := P) PAlg :=
    toConv (AlgHom.id R P)
  let gP : Cocharacter.parabolic PAlg (weightCocharacter (R := R) w) :=
    eqToHom (Cocharacter.parabolicFunctor_obj
      (weightCocharacter (R := R) w) PAlg)
      ((weightParabolicPointsIso R w).hom.app PAlg q)
  let gA : Cocharacter.parabolic (CommAlgCat.of R A)
      (weightCocharacter (R := R) w) :=
    eqToHom (Cocharacter.parabolicFunctor_obj
      (weightCocharacter (R := R) w) (CommAlgCat.of R A))
      ((weightParabolicPointsIso R w).hom.app (CommAlgCat.of R A) g)
  have hsame :
      (CommHopfAlgCat.mapPointsFunctor
        (weightParabolicLimitCoordinateMap R w)).app PAlg q =
        (weightLeviPointsIso R w).inv.app PAlg
          (Cocharacter.limitToLevi PAlg (weightCocharacter (R := R) w) gP) := by
    rw [mapPointsFunctor_weightParabolicLimitCoordinateMap_sameUniverse]
    exact weightParabolicLimitPointsMap_app_apply R w PAlg q
  have hambient := congrArg
    (CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
      (weightLeviDefiningHopfIdeal R w) PAlg) hsame
  rw [quotientPointsHom_weightLeviPointsIso_inv_app_apply,
    Cocharacter.coe_limitToLevi_apply] at hambient
  have hgP :
      (⟨AlgHom.mapValue g.ofConv
          (gP : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N) PAlg),
        Cocharacter.parabolic_le_comap g.ofConv gP.2⟩ :
          Cocharacter.parabolic (CommAlgCat.of R A)
            (weightCocharacter (R := R) w)) = gA := by
    apply Subtype.ext
    dsimp only [gP, gA]
    rw [coe_weightParabolicPointsIso_hom_app_apply,
      coe_weightParabolicPointsIso_hom_app_apply]
    apply WithConv.ofConv_injective
    ext h
    simp only [AlgHom.mapValue_apply, WithConv.ofConv_toConv, AlgHom.comp_apply]
    rw [CommHopfAlgCat.quotientPointsHom_apply_apply,
      CommHopfAlgCat.quotientPointsHom_apply_apply]
    dsimp only [q]
    rw [WithConv.ofConv_toConv, AlgHom.id_apply]
  -- Name the dynamic-parabolic component already present in the theorem statement so the
  -- quotient-point comparison below can use its characteristic lemma directly.
  change (CommHopfAlgCat.mapPointsFunctor
      (weightParabolicLimitCoordinateMap R w)).app (CommAlgCat.of R A) g =
    (weightLeviPointsIso R w).inv.app (CommAlgCat.of R A)
      (Cocharacter.limitToLevi (CommAlgCat.of R A)
        (weightCocharacter (R := R) w) gA)
  apply CommHopfAlgCat.quotientPointsHom_injective
    (coordinateHopfAlgebra R N) (weightLeviDefiningHopfIdeal R w)
    (CommAlgCat.of R A)
  rw [quotientPointsHom_weightLeviPointsIso_inv_app_apply,
    Cocharacter.coe_limitToLevi_apply]
  calc
    CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
        (weightLeviDefiningHopfIdeal R w) (CommAlgCat.of R A)
        ((CommHopfAlgCat.mapPointsFunctor
          (weightParabolicLimitCoordinateMap R w)).app (CommAlgCat.of R A) g) =
        AlgHom.mapValue g.ofConv
          (CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
            (weightLeviDefiningHopfIdeal R w) PAlg
            ((CommHopfAlgCat.mapPointsFunctor
              (weightParabolicLimitCoordinateMap R w)).app PAlg q)) := by
      apply WithConv.ofConv_injective
      ext h
      simp only [AlgHom.mapValue_apply, WithConv.ofConv_toConv, AlgHom.comp_apply]
      erw [CommHopfAlgCat.quotientPointsHom_apply_apply]
    _ = AlgHom.mapValue g.ofConv
          (Cocharacter.limit PAlg (weightCocharacter (R := R) w) gP) :=
      congrArg (AlgHom.mapValue g.ofConv) hambient
    _ = Cocharacter.limit (CommAlgCat.of R A) (weightCocharacter (R := R) w)
          ⟨AlgHom.mapValue g.ofConv gP,
            Cocharacter.parabolic_le_comap g.ofConv gP.2⟩ :=
      Cocharacter.mapValue_limit g.ofConv gP
    _ = Cocharacter.limit (CommAlgCat.of R A) (weightCocharacter (R := R) w) gA :=
      congrArg (Cocharacter.limit (CommAlgCat.of R A)
        (weightCocharacter (R := R) w)) hgP

/-- The group-scheme morphism `P(w) → L(w)` represented by the dynamic limit. -/
noncomputable def weightParabolicLimit (w : Fin N → ℤ) :
    weightParabolicGroupScheme R w ⟶ weightLeviGroupScheme R w :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
    (weightParabolicLimitCoordinateMap R w).op

/-- The weight-parabolic limit is relative spectrum applied contravariantly to its coordinate
Hopf-algebra morphism. -/
theorem weightParabolicLimit_def (w : Fin N → ℤ) :
    weightParabolicLimit R w =
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
        (weightParabolicLimitCoordinateMap R w).op := (rfl)

/-- On points valued in an arbitrary scheme over `Spec R`, the group-scheme limit is the
dynamic limit over the relative global sections of that scheme. -/
@[simp]
theorem schemePointsAlgΓMulEquiv_weightParabolicLimit (w : Fin N → ℤ)
    (T : Over (Spec (CommRingCat.of R)))
    (g : T ⟶ (weightParabolicGroupScheme R w).X) :
    WithConv.toConv ((((algΓ (CommRingCat.of R)).map g ≫
        (algΓ (CommRingCat.of R)).map (weightParabolicLimit R w).hom.hom) ≫
      (algΓAlgSpecAdjunction (CommRingCat.of R)).counit.app
        (Opposite.op (CommAlgCat.of R
          (weightLeviCoordinateHopfAlgebra R w)))).unop.hom) =
      (weightLeviPointsIso R w).inv.app
        ((algΓ (CommRingCat.of R)).obj T).unop
        (Cocharacter.limitToLevi ((algΓ (CommRingCat.of R)).obj T).unop
          (weightCocharacter (R := R) w)
          ((weightParabolicPointsIso R w).hom.app
            ((algΓ (CommRingCat.of R)).obj T).unop
            (CommHopfAlgCat.schemePointsAlgΓMulEquiv
              (weightParabolicCoordinateHopfAlgebra R w) T g))) := by
  rw [← Functor.map_comp]
  erw [← CommHopfAlgCat.schemePointsAlgΓMulEquiv_apply]
  rw [weightParabolicLimit_def]
  erw [CommHopfAlgCat.schemePointsAlgΓMulEquiv_mapDomain]
  change (CommHopfAlgCat.mapPointsFunctor
      (weightParabolicLimitCoordinateMap R w)).app
      ((algΓ (CommRingCat.of R)).obj T).unop
      (CommHopfAlgCat.schemePointsAlgΓMulEquiv
        (weightParabolicCoordinateHopfAlgebra R w) T g) = _
  exact mapPointsFunctor_weightParabolicLimitCoordinateMap_app R w _ _

/-- The represented dynamic limit retracts the existing closed immersion of the weight Levi into
the weight parabolic. -/
@[simp]
theorem weightLeviToParabolic_comp_weightParabolicLimit (w : Fin N → ℤ) :
    weightLeviToParabolic R w ≫ weightParabolicLimit R w =
      𝟙 (weightLeviGroupScheme R w) := by
  rw [weightLeviToParabolic_def, CommHopfAlgCat.quotientSpecMapOfLe_def,
    weightParabolicLimit_def,
    ← (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map_comp,
    ← op_comp]
  rw [← weightLeviToParabolicCoordinateMap_def]
  rw [weightParabolicLimitCoordinateMap_comp_weightLeviToParabolicCoordinateMap]
  exact (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map_id _

end

end TauCeti.GeneralLinear.Dynamic
