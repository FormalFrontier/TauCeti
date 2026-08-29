/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SemidirectProduct
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Categorical
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Basic
public import TauCeti.CategoryTheory.Monoidal.SemidirectProduct.Normal

/-!
# Products with a normal closed affine subgroup

Let `I` and `J` be Hopf ideals in a commutative Hopf algebra `H`, with `I` normal. Conjugation
of the subgroup defined by `J` on the normal subgroup defined by `I` equips their product scheme
with a semidirect-product group structure, for which multiplication into `Spec H` is a group
homomorphism. This file packages the corresponding coordinate Hopf-algebra morphism and defines
the product subgroup as its scheme-theoretic image.

This is the multiplication-image object required by the maximal-dimension construction of the
unipotent radical. Containment of both factors and normality are proved in
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Product.Properties`; connectedness, smoothness,
and unipotence of the image remain subsequent steps.

## Main declarations

* `TauCeti.CommHopfAlgCat.quotientNormalConjugation`: conjugation of one quotient subgroup on
  a normal quotient subgroup.
* `TauCeti.CommHopfAlgCat.normalSemidirectProduct`: the coordinate Hopf algebra of the
  resulting semidirect product.
* `TauCeti.CommHopfAlgCat.productMapOfNormal`: the coordinate morphism dual to multiplication.
* `TauCeti.CommHopfAlgCat.productOfNormal`: the coordinate Hopf algebra of the product image.
* `TauCeti.CommHopfAlgCat.productOfNormalGrpObjInclusion`: its categorical closed-subgroup
  inclusion.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and Sections 5.a, 6.a.
* A. Borel, *Linear Algebraic Groups*, Proposition 14.4.

This advances Layer 5, "The unipotent radical", of the ReductiveGroups roadmap by constructing
the multiplication image needed for binary-product closure of connected normal smooth unipotent
subgroup candidates.
-/

public section

open CategoryTheory Opposite
open scoped CategoryTheory.MonObj

namespace TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R]

/-- Conjugation of a quotient closed subgroup on a normal quotient closed subgroup, viewed as
an action of affine group objects. -/
@[expose] noncomputable def quotientNormalConjugation
    (H : _root_.CommHopfAlgCat.{u} R) (I J : HopfIdeal R H)
    (hI : I.IsNormal) :
    GrpObj.Action (grpObj (quotient H J)) (grpObj (quotient H I)) := by
  let i := quotientGrpObjInclusion H I
  let j := quotientGrpObjInclusion H J
  letI : IsMonHom.Normal i := (quotientGrpObjInclusion_normal_iff H I).2 hI
  exact GrpObj.Action.normalConjugation i j

/-- Evaluating quotient normal conjugation on points and including into the ambient group
gives conjugation by the included acting point. -/
theorem quotientPointsHom_quotientNormalConjugation_apply
    (H : _root_.CommHopfAlgCat.{u} R) (I J : HopfIdeal R H) (hI : I.IsNormal)
    (A : CommAlgCat.{u} R)
    (z : HopfAlgebra.points (R := R) (H := quotient H J) A)
    (g : HopfAlgebra.points (R := R) (H := quotient H I) A) :
    quotientPointsHom H I A
        (grpObjPointsMulEquiv (quotient H I) (op A)
          ((quotientNormalConjugation H I J hI).act
            ((grpObjPointsMulEquiv (quotient H J) (op A)).symm z)
            ((grpObjPointsMulEquiv (quotient H I) (op A)).symm g))) =
      quotientPointsHom H J A z * quotientPointsHom H I A g *
        (quotientPointsHom H J A z)⁻¹ := by
  let i := quotientGrpObjInclusion H I
  let j := quotientGrpObjInclusion H J
  let z' := (grpObjPointsMulEquiv (quotient H J) (op A)).symm z
  let g' := (grpObjPointsMulEquiv (quotient H I) (op A)).symm g
  let _ : IsMonHom.Normal i := (quotientGrpObjInclusion_normal_iff H I).2 hI
  have hact :
      (quotientNormalConjugation H I J hI).act z' g' ≫ i =
        (z' ≫ j) * (g' ≫ i) * (z' ≫ j)⁻¹ := by
    -- Unfold the exposed quotient action to categorical normal conjugation so its
    -- pointwise action lemma applies to the chosen quotient inclusions.
    change (GrpObj.Action.normalConjugation i j).act z' g' ≫ i = _
    rw [GrpObj.Action.normalConjugation_act, Category.assoc]
    exact TauCeti.lift_normalConjugation_comp i (z' ≫ j) g'
  have hpoints := congrArg (grpObjPointsMulEquiv H (op A)) hact
  simp only [i, j, z', g', map_mul, map_inv] at hpoints
  rw [grpObjPointsMulEquiv_comp_quotientGrpObjInclusion,
    grpObjPointsMulEquiv_comp_quotientGrpObjInclusion,
    grpObjPointsMulEquiv_comp_quotientGrpObjInclusion] at hpoints
  simpa only [MulEquiv.apply_symm_apply] using hpoints

/-- The coordinate Hopf algebra of the semidirect product of a normal closed affine subgroup
and another closed affine subgroup. Its underlying commutative algebra is
`(H / I) ⊗[ R ] (H / J)`, and its Hopf structure records conjugation of the second subgroup
on the first. -/
noncomputable def normalSemidirectProduct
    (H : _root_.CommHopfAlgCat.{u} R) (I J : HopfIdeal R H)
    (hI : I.IsNormal) : _root_.CommHopfAlgCat.{u} R :=
  (quotientNormalConjugation H I J hI).coordinateHopfAlgebra

/-- The canonical comparison between the named normal semidirect product and the coordinate
Hopf algebra supplied by the categorical semidirect-product construction. -/
noncomputable def normalSemidirectProductIso
    (H : _root_.CommHopfAlgCat.{u} R) (I J : HopfIdeal R H)
    (hI : I.IsNormal) :
    normalSemidirectProduct H I J hI ≅
      (quotientNormalConjugation H I J hI).coordinateHopfAlgebra := by
  rw [normalSemidirectProduct]

/-- The coordinate algebra of the named normal semidirect product is finite type when the
coordinate algebras of both factors are finite type. -/
noncomputable instance normalSemidirectProduct_finiteType
    (H : _root_.CommHopfAlgCat.{u} R) (I J : HopfIdeal R H)
    (hI : I.IsNormal) [Algebra.FiniteType R (quotient H I)]
    [Algebra.FiniteType R (quotient H J)] :
    Algebra.FiniteType R (normalSemidirectProduct H I J hI) :=
  Algebra.FiniteType.equiv
    (GrpObj.Action.coordinateHopfAlgebra_finiteType (quotientNormalConjugation H I J hI))
    (CommHopfAlgCat.ofIso (normalSemidirectProductIso H I J hI)).toAlgEquiv.symm

/-- The coordinate morphism representing inclusion of the normal factor in the named normal
semidirect product. -/
noncomputable def normalSemidirectProductCoordinateInl
    (H : _root_.CommHopfAlgCat.{u} R) (I J : HopfIdeal R H)
    (hI : I.IsNormal) : normalSemidirectProduct H I J hI ⟶ quotient H I :=
  (normalSemidirectProductIso H I J hI).hom ≫
    (quotientNormalConjugation H I J hI).coordinateInl

/-- The coordinate morphism representing inclusion of the acting factor in the named normal
semidirect product. -/
noncomputable def normalSemidirectProductCoordinateInr
    (H : _root_.CommHopfAlgCat.{u} R) (I J : HopfIdeal R H)
    (hI : I.IsNormal) : normalSemidirectProduct H I J hI ⟶ quotient H J :=
  (normalSemidirectProductIso H I J hI).hom ≫
    (quotientNormalConjugation H I J hI).coordinateInr

/-- The normal-factor coordinate morphism is transported by the canonical comparison. -/
theorem normalSemidirectProductCoordinateInl_def
    (H : _root_.CommHopfAlgCat.{u} R) (I J : HopfIdeal R H)
    (hI : I.IsNormal) :
    normalSemidirectProductCoordinateInl H I J hI =
      (normalSemidirectProductIso H I J hI).hom ≫
        (quotientNormalConjugation H I J hI).coordinateInl := by
  rw [normalSemidirectProductCoordinateInl]

/-- The acting-factor coordinate morphism is transported by the canonical comparison. -/
theorem normalSemidirectProductCoordinateInr_def
    (H : _root_.CommHopfAlgCat.{u} R) (I J : HopfIdeal R H)
    (hI : I.IsNormal) :
    normalSemidirectProductCoordinateInr H I J hI =
      (normalSemidirectProductIso H I J hI).hom ≫
        (quotientNormalConjugation H I J hI).coordinateInr := by
  rw [normalSemidirectProductCoordinateInr]

/-- The coordinate map obtained directly from categorical normal semidirect multiplication. -/
private noncomputable def normalSemidirectMultiplicationCoordinateMap
    (H : _root_.CommHopfAlgCat.{u} R) (I J : HopfIdeal R H)
    (hI : I.IsNormal) :
    H ⟶ (quotientNormalConjugation H I J hI).coordinateHopfAlgebra := by
  let i := quotientGrpObjInclusion H I
  let j := quotientGrpObjInclusion H J
  letI : IsMonHom.Normal i := (quotientGrpObjInclusion_normal_iff H I).2 hI
  exact (commHopfAlgCatEquivCogrpCommAlgCat R).unitIso.hom.app H ≫
    (commHopfAlgCatEquivCogrpCommAlgCat R).inverse.map
      (op (GrpObj.Action.normalSemidirectMul i j))

/-- The coordinate Hopf-algebra morphism dual to multiplication from the semidirect product of
a normal closed subgroup and another closed subgroup into the ambient affine group. -/
noncomputable def productMapOfNormal
    (H : _root_.CommHopfAlgCat.{u} R) (I J : HopfIdeal R H)
    (hI : I.IsNormal) : H ⟶ normalSemidirectProduct H I J hI :=
  normalSemidirectMultiplicationCoordinateMap H I J hI ≫
    (normalSemidirectProductIso H I J hI).inv

/-- After the canonical comparison, the product coordinate morphism is the transport of
categorical normal semidirect multiplication. -/
private theorem productMapOfNormal_comp_normalSemidirectProductIso_hom
    (H : _root_.CommHopfAlgCat.{u} R) (I J : HopfIdeal R H)
    (hI : I.IsNormal) :
    productMapOfNormal H I J hI ≫ (normalSemidirectProductIso H I J hI).hom =
      normalSemidirectMultiplicationCoordinateMap H I J hI := by
  rw [productMapOfNormal, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The underlying algebra map of the direct categorical coordinate map is obtained by
unopping normal semidirect multiplication. -/
private theorem normalSemidirectMultiplicationCoordinateMap_hom_toAlgHom
    (H : _root_.CommHopfAlgCat.{u} R) (I J : HopfIdeal R H)
    (hI : I.IsNormal) :
    let i := quotientGrpObjInclusion H I
    let j := quotientGrpObjInclusion H J
    let _ : IsMonHom.Normal i := (quotientGrpObjInclusion_normal_iff H I).2 hI
    (normalSemidirectMultiplicationCoordinateMap H I J hI).hom.toAlgHom =
      (GrpObj.Action.normalSemidirectMul i j).hom.hom.unop.hom := by
  rw [normalSemidirectMultiplicationCoordinateMap]
  -- The unit of Mathlib's Hopf/cogroup equivalence is definitionally the identity on the
  -- underlying algebra map, leaving exactly the unop of semidirect multiplication.
  rfl

/-- The represented group-object map of the direct categorical coordinate map is normal
semidirect multiplication. -/
private theorem grpObjMap_normalSemidirectMultiplicationCoordinateMap
    (H : _root_.CommHopfAlgCat.{u} R) (I J : HopfIdeal R H)
    (hI : I.IsNormal) :
    let i := quotientGrpObjInclusion H I
    let j := quotientGrpObjInclusion H J
    let _ : IsMonHom.Normal i := (quotientGrpObjInclusion_normal_iff H I).2 hI
    grpObjMap (normalSemidirectMultiplicationCoordinateMap H I J hI) =
      (GrpObj.Action.normalSemidirectMul i j).hom.hom := by
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  rw [grpObjMap_unop_hom]
  exact normalSemidirectMultiplicationCoordinateMap_hom_toAlgHom H I J hI

/-- After the canonical comparison, the represented group-object map of `productMapOfNormal`
is normal semidirect multiplication. -/
theorem grpObjMap_productMapOfNormal
    (H : _root_.CommHopfAlgCat.{u} R) (I J : HopfIdeal R H)
    (hI : I.IsNormal) :
    let i := quotientGrpObjInclusion H I
    let j := quotientGrpObjInclusion H J
    let _ : IsMonHom.Normal i := (quotientGrpObjInclusion_normal_iff H I).2 hI
    grpObjMap (normalSemidirectProductIso H I J hI).hom ≫
      grpObjMap (productMapOfNormal H I J hI) =
      (GrpObj.Action.normalSemidirectMul i j).hom.hom := by
  rw [← grpObjMap_comp]
  rw [productMapOfNormal_comp_normalSemidirectProductIso_hom]
  exact grpObjMap_normalSemidirectMultiplicationCoordinateMap H I J hI

variable {k : Type u} [Field k]

/-- The coordinate Hopf algebra of the scheme-theoretic multiplication image. -/
noncomputable abbrev productOfNormal
    (H : _root_.CommHopfAlgCat.{u} k) (I J : HopfIdeal k H)
    (hI : I.IsNormal) : _root_.CommHopfAlgCat.{u} k :=
  image (productMapOfNormal H I J hI)

/-- The categorical closed-subgroup inclusion of the multiplication image into the ambient
affine group. -/
noncomputable abbrev productOfNormalGrpObjInclusion
    (H : _root_.CommHopfAlgCat.{u} k) (I J : HopfIdeal k H)
    (hI : I.IsNormal) :
    grpObj (productOfNormal H I J hI) ⟶ grpObj H :=
  quotientGrpObjInclusion H (HopfIdeal.ker (productMapOfNormal H I J hI).hom)

end TauCeti.CommHopfAlgCat
