/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
unipotent radical. Establishing its containment of both factors and closure of normality,
connectedness, smoothness, and unipotence are subsequent steps.

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

/-- The coordinate Hopf algebra of the semidirect product of a normal closed affine subgroup
and another closed affine subgroup. Its underlying commutative algebra is
`(H / I) ⊗[ R ] (H / J)`, and its Hopf structure records conjugation of the second subgroup
on the first. -/
@[expose] noncomputable def normalSemidirectProduct
    (H : _root_.CommHopfAlgCat.{u} R) (I J : HopfIdeal R H)
    (hI : I.IsNormal) : _root_.CommHopfAlgCat.{u} R :=
  (commHopfAlgCatEquivCogrpCommAlgCat R).inverse.obj
    (op (quotientNormalConjugation H I J hI).semidirectProduct)

/-- The coordinate Hopf-algebra morphism dual to multiplication from the semidirect product of
a normal closed subgroup and another closed subgroup into the ambient affine group. -/
noncomputable def productMapOfNormal
    (H : _root_.CommHopfAlgCat.{u} R) (I J : HopfIdeal R H)
    (hI : I.IsNormal) : H ⟶ normalSemidirectProduct H I J hI := by
  let i := quotientGrpObjInclusion H I
  let j := quotientGrpObjInclusion H J
  letI : IsMonHom.Normal i := (quotientGrpObjInclusion_normal_iff H I).2 hI
  exact (commHopfAlgCatEquivCogrpCommAlgCat R).unitIso.hom.app H ≫
    (commHopfAlgCatEquivCogrpCommAlgCat R).inverse.map
      (op (GrpObj.Action.normalSemidirectMul i j))

/-- The product coordinate morphism is the transport of categorical normal semidirect
multiplication. -/
theorem productMapOfNormal_def
    (H : _root_.CommHopfAlgCat.{u} R) (I J : HopfIdeal R H)
    (hI : I.IsNormal) :
    let i := quotientGrpObjInclusion H I
    let j := quotientGrpObjInclusion H J
    letI : IsMonHom.Normal i := (quotientGrpObjInclusion_normal_iff H I).2 hI
    productMapOfNormal H I J hI =
      (commHopfAlgCatEquivCogrpCommAlgCat R).unitIso.hom.app H ≫
        (commHopfAlgCatEquivCogrpCommAlgCat R).inverse.map
          (op (GrpObj.Action.normalSemidirectMul i j)) :=
  (rfl)

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
