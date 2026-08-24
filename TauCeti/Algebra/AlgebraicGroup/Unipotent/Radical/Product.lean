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
# Products of normal closed affine subgroups

Let `I` and `J` be normal Hopf ideals in a commutative Hopf algebra `H`. Their quotient spectra
are normal closed subgroup schemes of `Spec H`. Conjugation of the second subgroup on the first
equips their product scheme with a semidirect-product group structure, for which multiplication
into `Spec H` is a group homomorphism. This file packages the corresponding coordinate Hopf
algebra morphism and defines the product subgroup as its scheme-theoretic image.

This is the multiplication-image object required by the maximal-dimension construction of the
unipotent radical. Establishing its containment of both factors and closure of normality,
connectedness, smoothness, and unipotence are subsequent steps.

## Main declarations

* `TauCeti.CommHopfAlgCat.normalProductSource`: the coordinate Hopf algebra of the semidirect
  product of two normal closed subgroups.
* `TauCeti.CommHopfAlgCat.normalProductMap`: the coordinate morphism dual to multiplication.
* `TauCeti.CommHopfAlgCat.normalProductHopfIdeal`: the Hopf ideal cutting out its image.
* `TauCeti.CommHopfAlgCat.normalProduct`: the coordinate Hopf algebra of the product image.
* `TauCeti.CommHopfAlgCat.normalProductInclusion`: its categorical closed-subgroup inclusion.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and Sections 5.a, 6.a.
* A. Borel, *Linear Algebraic Groups*, Proposition 14.4.

This advances Layer 5, "The unipotent radical", of the ReductiveGroups roadmap by constructing
the multiplication image needed for binary-product closure of connected normal smooth unipotent
subgroup candidates.
-/

public section

open CategoryTheory Opposite
open scoped CategoryTheory.MonObj TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u

variable {k : Type u} [Field k]

/-- Conjugation of the second normal closed subgroup on the first, viewed as an action of
affine group objects. -/
noncomputable abbrev normalProductAction
    (H : _root_.CommHopfAlgCat.{u} k) (I J : HopfIdeal k H)
    (hI : I.IsNormal) (_hJ : J.IsNormal) :
    GrpObj.Action (grpObj (quotient H J)) (grpObj (quotient H I)) := by
  let i := quotientGrpObjInclusion H I
  let j := quotientGrpObjInclusion H J
  letI : IsMonHom.Normal i := (quotientGrpObjInclusion_normal_iff H I).2 hI
  letI : IsMonHom.Normal j := (quotientGrpObjInclusion_normal_iff H J).2 _hJ
  exact GrpObj.Action.normalConjugation i j

/-- The coordinate Hopf algebra of the semidirect product of two normal closed affine
subgroups. Its underlying commutative algebra is `(H / I) ⊗[ k ] (H / J)`; its Hopf structure
records conjugation of the second subgroup on the first. -/
noncomputable abbrev normalProductSource
    (H : _root_.CommHopfAlgCat.{u} k) (I J : HopfIdeal k H)
    (hI : I.IsNormal) (hJ : J.IsNormal) : _root_.CommHopfAlgCat.{u} k := by
  let A := normalProductAction H I J hI hJ
  let _ := A.semidirectProductGrpObj
  exact (commHopfAlgCatEquivCogrpCommAlgCat k).inverse.obj
    (op (Grp.mk (MonoidalCategoryStruct.tensorObj
      (grpObj (quotient H I)) (grpObj (quotient H J)))))

/-- The coordinate Hopf-algebra morphism dual to multiplication from the semidirect product of
two normal closed subgroups into the ambient affine group. -/
noncomputable def normalProductMap
    (H : _root_.CommHopfAlgCat.{u} k) (I J : HopfIdeal k H)
    (hI : I.IsNormal) (hJ : J.IsNormal) : H ⟶ normalProductSource H I J hI hJ := by
  let i := quotientGrpObjInclusion H I
  let j := quotientGrpObjInclusion H J
  let _ : IsMonHom.Normal i := (quotientGrpObjInclusion_normal_iff H I).2 hI
  let _ : IsMonHom.Normal j := (quotientGrpObjInclusion_normal_iff H J).2 hJ
  let A := GrpObj.Action.normalConjugation i j
  let _ := A.semidirectProductGrpObj
  let m := GrpObj.Action.normalSemidirectMul i j
  exact (commHopfAlgCatEquivCogrpCommAlgCat k).unitIso.hom.app H ≫
    (commHopfAlgCatEquivCogrpCommAlgCat k).inverse.map (op m)

/-- The Hopf ideal cutting out the scheme-theoretic product of two normal closed affine
subgroups. It is the kernel of the coordinate morphism dual to semidirect multiplication. -/
noncomputable def normalProductHopfIdeal
    (H : _root_.CommHopfAlgCat.{u} k) (I J : HopfIdeal k H)
    (hI : I.IsNormal) (hJ : J.IsNormal) : HopfIdeal k H :=
  HopfIdeal.ker (normalProductMap H I J hI hJ).hom

/-- Membership in the product Hopf ideal means vanishing under the coordinate multiplication
morphism. -/
@[simp]
theorem mem_normalProductHopfIdeal_iff
    (H : _root_.CommHopfAlgCat.{u} k) (I J : HopfIdeal k H)
    (hI : I.IsNormal) (hJ : J.IsNormal) (x : H) :
    x ∈ normalProductHopfIdeal H I J hI hJ ↔
      (normalProductMap H I J hI hJ).hom x = 0 :=
  HopfIdeal.mem_ker _

/-- The coordinate Hopf algebra of the scheme-theoretic multiplication image. -/
noncomputable abbrev normalProduct
    (H : _root_.CommHopfAlgCat.{u} k) (I J : HopfIdeal k H)
    (hI : I.IsNormal) (hJ : J.IsNormal) : _root_.CommHopfAlgCat.{u} k :=
  image (normalProductMap H I J hI hJ)

/-- The categorical closed-subgroup inclusion of the multiplication image into the ambient
affine group. -/
noncomputable abbrev normalProductInclusion
    (H : _root_.CommHopfAlgCat.{u} k) (I J : HopfIdeal k H)
    (hI : I.IsNormal) (hJ : J.IsNormal) :
    grpObj (normalProduct H I J hI hJ) ⟶ grpObj H :=
  grpObjMap (mkImage (normalProductMap H I J hI hJ))

end TauCeti.CommHopfAlgCat
