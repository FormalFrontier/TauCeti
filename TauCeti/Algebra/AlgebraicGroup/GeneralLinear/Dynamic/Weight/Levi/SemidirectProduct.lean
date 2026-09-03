/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Levi.Action
public import TauCeti.Algebra.AlgebraicGroup.Connected.Product
public import TauCeti.Algebra.AlgebraicGroup.Smooth.Product

/-!
# The represented weight-parabolic Levi decomposition

Let `w : Fin N → ℤ`. The weight-unipotent subgroup `U(w)` is normal in the weight parabolic
`P(w)`, and the weight Levi subgroup `L(w)` acts on it by conjugation. The resulting represented
semidirect product maps to `P(w)` by multiplication. This file proves that multiplication is an
isomorphism:

```text
U(w) ⋊ L(w) ≅ P(w).
```

On points over every commutative algebra this is the dynamic Levi decomposition. The proof
transports the categorical semidirect-product points to the dynamic subgroups, uses the existing
comparison of the two conjugation actions, and then applies the pointwise decomposition.

## Main declarations

* `TauCeti.GeneralLinear.Dynamic.weightParabolicSemidirectProductCoordinateHopfAlgebra`: the
  coordinate Hopf algebra of the represented unipotent-by-Levi semidirect product.
* `TauCeti.GeneralLinear.Dynamic.weightParabolicSemidirectProductCoordinateMap`: the coordinate
  morphism dual to multiplication into the parabolic.
* `TauCeti.GeneralLinear.Dynamic.weightParabolicSemidirectProductPointsMulEquiv`: the represented
  semidirect-product points are equivalent to the represented parabolic points.
* `TauCeti.GeneralLinear.Dynamic.weightParabolicSemidirectProductCoordinateIso`: multiplication
  identifies the coordinate Hopf algebra of `U(w) ⋊ L(w)` with that of `P(w)`.
* `TauCeti.GeneralLinear.Dynamic.
  smoothCommHopfAlgProperty_weightParabolicSemidirectProductCoordinateHopfAlgebra`:
  smoothness transfers from `U(w)` and `L(w)` to their represented semidirect product.
* `TauCeti.GeneralLinear.Dynamic.
  geometricallyConnectedCommHopfAlgProperty_weightParabolicSemidirectProductCoordinateHopfAlgebra`:
  geometric connectedness transfers from `U(w)` and `L(w)` to their represented semidirect
  product.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.

This completes the represented dynamic Levi decomposition for general-linear weight parabolics,
in the dynamic route to parabolics and Levi decomposition in Layer 7, "Structure theory", of the
ReductiveGroups roadmap.
-/

public section

open AlgebraicGeometry CategoryTheory Limits Opposite MonoidalCategory
  CartesianMonoidalCategory WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.GeneralLinear.Dynamic

universe u

noncomputable section

variable (R : Type u) [CommRing R] {N : ℕ}

/-- The coordinate Hopf algebra of the represented semidirect product `U(w) ⋊ L(w)`. -/
noncomputable def weightParabolicSemidirectProductCoordinateHopfAlgebra
    (w : Fin N → ℤ) :
    _root_.CommHopfAlgCat.{u} R :=
  (CommHopfAlgCat.quotientNormalConjugation
    (weightParabolicCoordinateHopfAlgebra R w)
    (weightUnipotentInParabolicHopfIdeal R w)
    (weightLeviInParabolicHopfIdeal R w)
    (isNormal_weightUnipotentInParabolicHopfIdeal R w)).coordinateHopfAlgebra

/-- The coordinate Hopf-algebra morphism dual to multiplication
`U(w) ⋊ L(w) → P(w)`. -/
noncomputable def weightParabolicSemidirectProductCoordinateMap (w : Fin N → ℤ) :
    weightParabolicCoordinateHopfAlgebra R w ⟶
      weightParabolicSemidirectProductCoordinateHopfAlgebra R w :=
  CommHopfAlgCat.productMapOfNormal
    (weightParabolicCoordinateHopfAlgebra R w)
    (weightUnipotentInParabolicHopfIdeal R w)
    (weightLeviInParabolicHopfIdeal R w)
    (isNormal_weightUnipotentInParabolicHopfIdeal R w) ≫
      (CommHopfAlgCat.normalSemidirectProductIso
        (weightParabolicCoordinateHopfAlgebra R w)
        (weightUnipotentInParabolicHopfIdeal R w)
        (weightLeviInParabolicHopfIdeal R w)
        (isNormal_weightUnipotentInParabolicHopfIdeal R w)).hom ≫
      eqToHom (by rw [weightParabolicSemidirectProductCoordinateHopfAlgebra])

/-- Categorical points of the represented semidirect product, split into quotient points. -/
private noncomputable def weightParabolicCategoricalSemidirectPointsMulEquiv
    (w : Fin N → ℤ) (A : CommAlgCat.{u} R) :
    HopfAlgebra.points (R := R)
      (H := weightParabolicSemidirectProductCoordinateHopfAlgebra R w) A ≃*
      ((op A ⟶ CommHopfAlgCat.grpObj
          (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
            (weightUnipotentInParabolicHopfIdeal R w))) ⋊[(CommHopfAlgCat.quotientNormalConjugation
          (weightParabolicCoordinateHopfAlgebra R w)
          (weightUnipotentInParabolicHopfIdeal R w)
          (weightLeviInParabolicHopfIdeal R w)
          (isNormal_weightUnipotentInParabolicHopfIdeal R w)).toMulAutHom (op A)]
        (op A ⟶ CommHopfAlgCat.grpObj
          (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
            (weightLeviInParabolicHopfIdeal R w)))) :=
  (CommHopfAlgCat.grpObjPointsMulEquiv
      (CommHopfAlgCat.quotientNormalConjugation
        (weightParabolicCoordinateHopfAlgebra R w)
        (weightUnipotentInParabolicHopfIdeal R w)
        (weightLeviInParabolicHopfIdeal R w)
        (isNormal_weightUnipotentInParabolicHopfIdeal R w)).coordinateHopfAlgebra
      (op A)).symm.trans
    ((CommHopfAlgCat.quotientNormalConjugation
      (weightParabolicCoordinateHopfAlgebra R w)
      (weightUnipotentInParabolicHopfIdeal R w)
      (weightLeviInParabolicHopfIdeal R w)
      (isNormal_weightUnipotentInParabolicHopfIdeal R w)).pointMulEquiv (op A))

/-- Categorical quotient points transported to dynamic weight-unipotent points. -/
private noncomputable def weightUnipotentCategoricalPointsMulEquiv
    (w : Fin N → ℤ) (A : CommAlgCat.{u} R) :
    (op A ⟶ CommHopfAlgCat.grpObj
        (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
          (weightUnipotentInParabolicHopfIdeal R w))) ≃*
      Cocharacter.unipotent A (weightCocharacter (R := R) w) :=
  (CommHopfAlgCat.grpObjPointsMulEquiv
      (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
        (weightUnipotentInParabolicHopfIdeal R w)) (op A)).trans
    (weightUnipotentInParabolicPointsMulEquiv R w A)

/-- Categorical quotient points transported to dynamic weight-Levi points. -/
private noncomputable def weightLeviCategoricalPointsMulEquiv
    (w : Fin N → ℤ) (A : CommAlgCat.{u} R) :
    (op A ⟶ CommHopfAlgCat.grpObj
        (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
          (weightLeviInParabolicHopfIdeal R w))) ≃*
      Cocharacter.levi A (weightCocharacter (R := R) w) :=
  (CommHopfAlgCat.grpObjPointsMulEquiv
      (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
        (weightLeviInParabolicHopfIdeal R w)) (op A)).trans
    (weightLeviInParabolicPointsMulEquiv R w A)

private theorem weightCategoricalPoints_action
    (w : Fin N → ℤ) (A : CommAlgCat.{u} R)
    (z : op A ⟶ CommHopfAlgCat.grpObj
      (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
        (weightLeviInParabolicHopfIdeal R w)))
    (g : op A ⟶ CommHopfAlgCat.grpObj
      (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
        (weightUnipotentInParabolicHopfIdeal R w))) :
    weightUnipotentCategoricalPointsMulEquiv R w A
        ((CommHopfAlgCat.quotientNormalConjugation
          (weightParabolicCoordinateHopfAlgebra R w)
          (weightUnipotentInParabolicHopfIdeal R w)
          (weightLeviInParabolicHopfIdeal R w)
          (isNormal_weightUnipotentInParabolicHopfIdeal R w)).toMulAutHom (op A) z g) =
      Cocharacter.leviConjugation A (weightCocharacter (R := R) w)
        (weightLeviCategoricalPointsMulEquiv R w A z)
        (weightUnipotentCategoricalPointsMulEquiv R w A g) := by
  simp only [weightUnipotentCategoricalPointsMulEquiv,
    weightLeviCategoricalPointsMulEquiv, MulEquiv.trans_apply]
  rw [← representedWeightLeviConjugation_apply R w A z g]
  rw [representedWeightLeviConjugation_eq_dynamic]

/-- The equivalence between categorical and dynamic weight semidirect-product points. -/
private noncomputable def weightCategoricalSemidirectPointsMulEquiv
    (w : Fin N → ℤ) (A : CommAlgCat.{u} R) :
    ((op A ⟶ CommHopfAlgCat.grpObj
          (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
            (weightUnipotentInParabolicHopfIdeal R w))) ⋊[(CommHopfAlgCat.quotientNormalConjugation
          (weightParabolicCoordinateHopfAlgebra R w)
          (weightUnipotentInParabolicHopfIdeal R w)
          (weightLeviInParabolicHopfIdeal R w)
          (isNormal_weightUnipotentInParabolicHopfIdeal R w)).toMulAutHom (op A)]
        (op A ⟶ CommHopfAlgCat.grpObj
          (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
            (weightLeviInParabolicHopfIdeal R w)))) ≃*
      (Cocharacter.unipotent A (weightCocharacter (R := R) w) ⋊[
        Cocharacter.leviConjugation A (weightCocharacter (R := R) w)]
        Cocharacter.levi A (weightCocharacter (R := R) w)) :=
  SemidirectProduct.congr
    (weightUnipotentCategoricalPointsMulEquiv R w A)
    (weightLeviCategoricalPointsMulEquiv R w A) fun z ↦ by
      apply MulEquiv.ext
      intro g
      exact weightCategoricalPoints_action R w A z g

@[simp]
private theorem weightCategoricalSemidirectPointsMulEquiv_left
    (w : Fin N → ℤ) (A : CommAlgCat.{u} R)
    (x : ((op A ⟶ CommHopfAlgCat.grpObj
          (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
            (weightUnipotentInParabolicHopfIdeal R w))) ⋊[(CommHopfAlgCat.quotientNormalConjugation
          (weightParabolicCoordinateHopfAlgebra R w)
          (weightUnipotentInParabolicHopfIdeal R w)
          (weightLeviInParabolicHopfIdeal R w)
          (isNormal_weightUnipotentInParabolicHopfIdeal R w)).toMulAutHom (op A)]
        (op A ⟶ CommHopfAlgCat.grpObj
          (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
            (weightLeviInParabolicHopfIdeal R w))))) :
    (weightCategoricalSemidirectPointsMulEquiv R w A x).left =
      weightUnipotentCategoricalPointsMulEquiv R w A x.left :=
  rfl

@[simp]
private theorem weightCategoricalSemidirectPointsMulEquiv_right
    (w : Fin N → ℤ) (A : CommAlgCat.{u} R)
    (x : ((op A ⟶ CommHopfAlgCat.grpObj
          (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
            (weightUnipotentInParabolicHopfIdeal R w))) ⋊[(CommHopfAlgCat.quotientNormalConjugation
          (weightParabolicCoordinateHopfAlgebra R w)
          (weightUnipotentInParabolicHopfIdeal R w)
          (weightLeviInParabolicHopfIdeal R w)
          (isNormal_weightUnipotentInParabolicHopfIdeal R w)).toMulAutHom (op A)]
        (op A ⟶ CommHopfAlgCat.grpObj
          (CommHopfAlgCat.quotient (weightParabolicCoordinateHopfAlgebra R w)
            (weightLeviInParabolicHopfIdeal R w))))) :
    (weightCategoricalSemidirectPointsMulEquiv R w A x).right =
      weightLeviCategoricalPointsMulEquiv R w A x.right :=
  rfl

/-- Represented weight-parabolic points transported to their dynamic model. -/
private noncomputable def weightParabolicDynamicPointsMulEquiv
    (w : Fin N → ℤ) (A : CommAlgCat.{u} R) :
    HopfAlgebra.points (R := R) (H := weightParabolicCoordinateHopfAlgebra R w) A ≃*
      Cocharacter.parabolic A (weightCocharacter (R := R) w) :=
  ((weightParabolicPointsIso R w).app A).groupIsoToMulEquiv.trans
    ((eqToIso (Cocharacter.parabolicFunctor_obj
      (weightCocharacter (R := R) w) A)).groupIsoToMulEquiv)

@[simp]
private theorem coe_weightParabolicDynamicPointsMulEquiv_apply
    (w : Fin N → ℤ) (A : CommAlgCat.{u} R)
    (g : HopfAlgebra.points (R := R) (H := weightParabolicCoordinateHopfAlgebra R w) A) :
    ((weightParabolicDynamicPointsMulEquiv R w A g :
        Cocharacter.parabolic A (weightCocharacter (R := R) w)) :
      HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R N) A) =
      CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R N)
        (weightParabolicDefiningHopfIdeal R w) A g := by
  exact coe_weightParabolicPointsIso_hom_app_apply R w g

/-- Points of the represented weight-unipotent-by-Levi semidirect product are canonically
equivalent to represented weight-parabolic points. Under this equivalence, a pair `(u, z)` maps
to the product `u * z` of its two subgroup inclusions. -/
noncomputable def weightParabolicSemidirectProductPointsMulEquiv
    (w : Fin N → ℤ) (A : CommAlgCat.{u} R) :
    HopfAlgebra.points (R := R)
      (H := weightParabolicSemidirectProductCoordinateHopfAlgebra R w) A ≃*
      HopfAlgebra.points (R := R) (H := weightParabolicCoordinateHopfAlgebra R w) A :=
  (weightParabolicCategoricalSemidirectPointsMulEquiv R w A).trans
    ((weightCategoricalSemidirectPointsMulEquiv R w A).trans
      ((Cocharacter.leviDecompositionMulEquiv A
        (weightCocharacter (R := R) w)).trans
        (weightParabolicDynamicPointsMulEquiv R w A).symm))

private theorem weightParabolicDynamicPointsMulEquiv_weightParabolicSemidirectProductPointsMulEquiv
    (w : Fin N → ℤ) (A : CommAlgCat.{u} R)
    (g : HopfAlgebra.points (R := R)
      (H := weightParabolicSemidirectProductCoordinateHopfAlgebra R w) A) :
    weightParabolicDynamicPointsMulEquiv R w A
        (weightParabolicSemidirectProductPointsMulEquiv R w A g) =
      Cocharacter.leviDecompositionMulEquiv A (weightCocharacter (R := R) w)
        (weightCategoricalSemidirectPointsMulEquiv R w A
          (weightParabolicCategoricalSemidirectPointsMulEquiv R w A g)) := by
  unfold weightParabolicSemidirectProductPointsMulEquiv
  simp only [MulEquiv.trans_apply]
  rw [MulEquiv.apply_symm_apply]

private theorem mapPointsFunctor_weightParabolicSemidirectProductCoordinateMap_apply
    (w : Fin N → ℤ) (A : CommAlgCat.{u} R)
    (g : HopfAlgebra.points (R := R)
      (H := weightParabolicSemidirectProductCoordinateHopfAlgebra R w) A) :
    let x := weightParabolicCategoricalSemidirectPointsMulEquiv R w A g
    (CommHopfAlgCat.mapPointsFunctor
      (weightParabolicSemidirectProductCoordinateMap R w)).app A g =
        CommHopfAlgCat.quotientPointsHom (weightParabolicCoordinateHopfAlgebra R w)
            (weightUnipotentInParabolicHopfIdeal R w) A
            (CommHopfAlgCat.grpObjPointsMulEquiv _ (op A) x.left) *
          CommHopfAlgCat.quotientPointsHom (weightParabolicCoordinateHopfAlgebra R w)
            (weightLeviInParabolicHopfIdeal R w) A
            (CommHopfAlgCat.grpObjPointsMulEquiv _ (op A) x.right) := by
  dsimp only
  let H := weightParabolicCoordinateHopfAlgebra R w
  let I := weightUnipotentInParabolicHopfIdeal R w
  let J := weightLeviInParabolicHopfIdeal R w
  let hI := isNormal_weightUnipotentInParabolicHopfIdeal R w
  let _ : IsMonHom.Normal (CommHopfAlgCat.quotientGrpObjInclusion H I) :=
    (CommHopfAlgCat.quotientGrpObjInclusion_normal_iff H I).2 hI
  let action := CommHopfAlgCat.quotientNormalConjugation H I J hI
  -- Work first with the categorical semidirect-product point corresponding to `g`.
  let q : op A ⟶ action.semidirectProduct.toMon.X :=
    (CommHopfAlgCat.grpObjPointsMulEquiv
      (weightParabolicSemidirectProductCoordinateHopfAlgebra R w) (op A)).symm g
  have hmap : CommHopfAlgCat.grpObjMap
      (weightParabolicSemidirectProductCoordinateMap R w) =
      (GrpObj.Action.normalSemidirectMul
        (CommHopfAlgCat.quotientGrpObjInclusion H I)
        (CommHopfAlgCat.quotientGrpObjInclusion H J)).hom.hom := by
    simp only [weightParabolicSemidirectProductCoordinateMap,
      weightParabolicSemidirectProductCoordinateHopfAlgebra]
    rw [CommHopfAlgCat.grpObjMap_comp]
    exact CommHopfAlgCat.grpObjMap_productMapOfNormal H I J hI
  have hq : CommHopfAlgCat.grpObjPointsMulEquiv
      (weightParabolicSemidirectProductCoordinateHopfAlgebra R w) (op A) q = g :=
    MulEquiv.apply_symm_apply _ g
  -- The two coordinates of `q` are exactly the components used by the point equivalence.
  have hxleft :
      (weightParabolicCategoricalSemidirectPointsMulEquiv R w A g).left =
        q ≫ fst
          (CommHopfAlgCat.grpObj (CommHopfAlgCat.quotient H I))
          (CommHopfAlgCat.grpObj (CommHopfAlgCat.quotient H J)) := by
    simp only [weightParabolicCategoricalSemidirectPointsMulEquiv, q]
    exact (action.pointMulEquiv_left _).trans rfl
  have hxright :
      (weightParabolicCategoricalSemidirectPointsMulEquiv R w A g).right =
        q ≫ snd
          (CommHopfAlgCat.grpObj (CommHopfAlgCat.quotient H I))
          (CommHopfAlgCat.grpObj (CommHopfAlgCat.quotient H J)) := by
    simp only [weightParabolicCategoricalSemidirectPointsMulEquiv, q]
    exact (action.pointMulEquiv_right _).trans rfl
  rw [hxleft, hxright]
  -- Multiplication on represented points is composition with the categorical multiplication;
  -- its normal-semidirect formula then separates into the two quotient inclusions.
  calc
    _ = CommHopfAlgCat.grpObjPointsMulEquiv H (op A)
        (q ≫ CommHopfAlgCat.grpObjMap
          (weightParabolicSemidirectProductCoordinateMap R w)) := by
      have hcomp := CommHopfAlgCat.grpObjPointsMulEquiv_comp_grpObjMap
        (weightParabolicSemidirectProductCoordinateMap R w) (op A) q
      rw [CommHopfAlgCat.mapPointsFunctor_app_apply, hq] at hcomp
      rw [CommHopfAlgCat.mapPointsFunctor_app_apply]
      exact hcomp.symm
    _ = CommHopfAlgCat.grpObjPointsMulEquiv H (op A)
        (q ≫ (GrpObj.Action.normalSemidirectMul
          (CommHopfAlgCat.quotientGrpObjInclusion H I)
          (CommHopfAlgCat.quotientGrpObjInclusion H J)).hom.hom) := by
      rw [hmap]
    _ = CommHopfAlgCat.grpObjPointsMulEquiv H (op A)
        ((q ≫ fst _ _ ≫
            CommHopfAlgCat.quotientGrpObjInclusion H I) *
          (q ≫ snd _ _ ≫
            CommHopfAlgCat.quotientGrpObjInclusion H J)) := by
      rw [GrpObj.Action.comp_normalSemidirectMul]
    _ = _ := by
      rw [map_mul]
      have hleft := CommHopfAlgCat.grpObjPointsMulEquiv_comp_quotientGrpObjInclusion
        H I (op A) (q ≫ fst (CommHopfAlgCat.grpObj (CommHopfAlgCat.quotient H I))
          (CommHopfAlgCat.grpObj (CommHopfAlgCat.quotient H J)))
      have hright := CommHopfAlgCat.grpObjPointsMulEquiv_comp_quotientGrpObjInclusion
        H J (op A) (q ≫ snd (CommHopfAlgCat.grpObj (CommHopfAlgCat.quotient H I))
          (CommHopfAlgCat.grpObj (CommHopfAlgCat.quotient H J)))
      simpa only [H, I, J, Category.assoc] using congrArg₂ (· * ·) hleft hright

/-- The represented weight-parabolic semidirect-product equivalence is induced by the
coordinate morphism dual to multiplication. -/
@[simp]
theorem weightParabolicSemidirectProductPointsMulEquiv_apply
    (w : Fin N → ℤ) (A : CommAlgCat.{u} R)
    (g : HopfAlgebra.points (R := R)
      (H := weightParabolicSemidirectProductCoordinateHopfAlgebra R w) A) :
    weightParabolicSemidirectProductPointsMulEquiv R w A g =
      (CommHopfAlgCat.mapPointsFunctor
        (weightParabolicSemidirectProductCoordinateMap R w)).app A g := by
  apply (weightParabolicDynamicPointsMulEquiv R w A).injective
  rw [mapPointsFunctor_weightParabolicSemidirectProductCoordinateMap_apply]
  rw [weightParabolicDynamicPointsMulEquiv_weightParabolicSemidirectProductPointsMulEquiv]
  apply Subtype.ext
  rw [Cocharacter.leviDecompositionMulEquiv_apply]
  simp only [Subgroup.coe_mul, Cocharacter.coe_unipotentToParabolic_apply,
    Cocharacter.coe_leviToParabolic_apply,
    weightCategoricalSemidirectPointsMulEquiv_left,
    weightCategoricalSemidirectPointsMulEquiv_right,
    weightUnipotentCategoricalPointsMulEquiv, weightLeviCategoricalPointsMulEquiv,
    MulEquiv.trans_apply]
  rw [coe_weightParabolicDynamicPointsMulEquiv_apply, map_mul,
    coe_weightUnipotentInParabolicPointsMulEquiv_apply,
    coe_weightLeviInParabolicPointsMulEquiv_apply]

private noncomputable instance isIso_mapPointsFunctor_weightParabolicSemidirectProductCoordinateMap
    (w : Fin N → ℤ) :
    IsIso (CommHopfAlgCat.mapPointsFunctor.{u, u, u}
      (weightParabolicSemidirectProductCoordinateMap R w)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro A
  rcases A with ⟨A⟩
  apply (ConcreteCategory.isIso_iff_bijective _).2
  constructor
  · intro x y hxy
    -- Unpack the value-algebra object so the exposed carrier of `pointsFunctor.obj` reduces to
    -- the `HopfAlgebra.points` type used by the pointwise equivalence.
    change HopfAlgebra.points
      (R := R) (H := weightParabolicSemidirectProductCoordinateHopfAlgebra R w)
        (CommAlgCat.of R A) at x y
    apply (weightParabolicSemidirectProductPointsMulEquiv R w (CommAlgCat.of R A)).injective
    rw [weightParabolicSemidirectProductPointsMulEquiv_apply,
      weightParabolicSemidirectProductPointsMulEquiv_apply]
    exact hxy
  · intro y
    -- Normalize the target carrier for the same reason before using surjectivity of the
    -- pointwise equivalence.
    change HopfAlgebra.points
      (R := R) (H := weightParabolicCoordinateHopfAlgebra R w)
        (CommAlgCat.of R A) at y
    obtain ⟨x, rfl⟩ :=
      (weightParabolicSemidirectProductPointsMulEquiv R w (CommAlgCat.of R A)).surjective y
    exact ⟨x, (weightParabolicSemidirectProductPointsMulEquiv_apply
      R w (CommAlgCat.of R A) x).symm⟩

/-- Multiplication from the represented weight-unipotent-by-Levi semidirect product to the
weight parabolic is an isomorphism. -/
noncomputable instance isIso_weightParabolicSemidirectProductCoordinateMap
    (w : Fin N → ℤ) :
    IsIso (weightParabolicSemidirectProductCoordinateMap R w) := by
  let f := weightParabolicSemidirectProductCoordinateMap R w
  let _ : IsIso (CommHopfAlgCat.mapPointsFunctor.{u, u, u} f) := by
    dsimp only [f]
    exact isIso_mapPointsFunctor_weightParabolicSemidirectProductCoordinateMap R w
  exact CommHopfAlgCat.isIso_of_isIso_mapPointsFunctor f

/-- Multiplication identifies the coordinate Hopf algebra of the weight parabolic with the
coordinate Hopf algebra of its represented unipotent-by-Levi semidirect product. -/
noncomputable def weightParabolicSemidirectProductCoordinateIso (w : Fin N → ℤ) :
    weightParabolicCoordinateHopfAlgebra R w ≅
      weightParabolicSemidirectProductCoordinateHopfAlgebra R w :=
  asIso (weightParabolicSemidirectProductCoordinateMap R w)

/-- The forward morphism of the weight-parabolic coordinate isomorphism is dual to
multiplication. -/
@[simp]
theorem weightParabolicSemidirectProductCoordinateIso_hom (w : Fin N → ℤ) :
    (weightParabolicSemidirectProductCoordinateIso R w).hom =
      weightParabolicSemidirectProductCoordinateMap R w :=
  by
    rw [weightParabolicSemidirectProductCoordinateIso, asIso_hom]

/-- Smoothness of the weight-unipotent and weight-Levi factors implies smoothness of their
represented semidirect product. -/
theorem smoothCommHopfAlgProperty_weightParabolicSemidirectProductCoordinateHopfAlgebra
    (R : Type u) [CommRing R] (w : Fin N → ℤ)
    (hU : smoothCommHopfAlgProperty R (weightUnipotentCoordinateHopfAlgebra R w))
    (hL : smoothCommHopfAlgProperty R (weightLeviCoordinateHopfAlgebra R w)) :
    smoothCommHopfAlgProperty R
      (weightParabolicSemidirectProductCoordinateHopfAlgebra R w) := by
  let A := CommHopfAlgCat.quotientNormalConjugation
    (weightParabolicCoordinateHopfAlgebra R w)
    (weightUnipotentInParabolicHopfIdeal R w)
    (weightLeviInParabolicHopfIdeal R w)
    (isNormal_weightUnipotentInParabolicHopfIdeal R w)
  unfold weightParabolicSemidirectProductCoordinateHopfAlgebra
  apply smoothCommHopfAlgProperty.semidirectProduct _ _ A
  · exact (smoothCommHopfAlgProperty R).prop_of_iso
      (weightUnipotentInParabolicCoordinateIso R w) hU
  · exact (smoothCommHopfAlgProperty R).prop_of_iso
      (weightLeviInParabolicCoordinateIso R w) hL

/-- Geometric connectedness of the weight-unipotent and weight-Levi factors implies geometric
connectedness of their represented semidirect product. -/
theorem
    geometricallyConnectedCommHopfAlgProperty_weightParabolicSemidirectProductCoordinateHopfAlgebra
    (k : Type u) [Field k] (w : Fin N → ℤ)
    (hU : geometricallyConnectedCommHopfAlgProperty k
      (weightUnipotentCoordinateHopfAlgebra k w))
    (hL : geometricallyConnectedCommHopfAlgProperty k
      (weightLeviCoordinateHopfAlgebra k w)) :
    geometricallyConnectedCommHopfAlgProperty k
      (weightParabolicSemidirectProductCoordinateHopfAlgebra k w) := by
  let A := CommHopfAlgCat.quotientNormalConjugation
    (weightParabolicCoordinateHopfAlgebra k w)
    (weightUnipotentInParabolicHopfIdeal k w)
    (weightLeviInParabolicHopfIdeal k w)
    (isNormal_weightUnipotentInParabolicHopfIdeal k w)
  unfold weightParabolicSemidirectProductCoordinateHopfAlgebra
  apply geometricallyConnectedCommHopfAlgProperty.semidirectProduct _ _ A
  · exact (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
      (weightUnipotentInParabolicCoordinateIso k w) hU
  · exact (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
      (weightLeviInParabolicCoordinateIso k w) hL

end

end TauCeti.GeneralLinear.Dynamic
