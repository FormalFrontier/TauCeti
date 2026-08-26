/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SemidirectProduct
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Image
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Product.Basic
public import TauCeti.CategoryTheory.Monoidal.SemidirectProduct.Equivariance

/-!
# Containment and normality of normal-subgroup products

Let `I` and `J` be Hopf ideals of a commutative Hopf algebra `H`. If `I` is normal, multiplication
from the conjugation semidirect product has a scheme-theoretic image in `Spec H`. This file proves
that the image contains the closed subgroups cut out by both `I` and `J`. If `J` is normal as well,
then the product image is normal.

Containment is contravariant: the kernel Hopf ideal of the product coordinate map lies below each
of `I` and `J`. Normality follows by translating simultaneous-conjugation equivariance of
semidirect multiplication to coordinate algebras, then applying the general theorem that the
kernel of an equivariant coordinate morphism is normal.

These are two of the structural inputs needed to prove binary-product closure of connected normal
smooth unipotent closed subgroups. Connectedness and smooth unipotence of the product image are
separate steps.

## Main declarations

* `TauCeti.CommHopfAlgCat.productMapOfNormal_comp_coordinateInl` and
  `TauCeti.CommHopfAlgCat.productMapOfNormal_comp_coordinateInr`: multiplication restricts to the
  two original closed-subgroup inclusions.
* `TauCeti.CommHopfAlgCat.ker_productMapOfNormal_le_left` and
  `TauCeti.CommHopfAlgCat.ker_productMapOfNormal_le_right`: the product image contains both
  factors.
* `TauCeti.CommHopfAlgCat.isNormal_ker_productMapOfNormal`: the product of two normal
  closed affine subgroups is normal.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and Sections 5.a, 6.a.
* A. Borel, *Linear Algebraic Groups*, Proposition 14.4.

This advances Layer 5, "The unipotent radical", of the ReductiveGroups roadmap by proving the
containment and normality parts of binary-product closure for unipotent-radical candidates.
-/

public section

open CategoryTheory Opposite
open scoped CategoryTheory.MonObj TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u

noncomputable section

section

variable {k : Type u} [CommRing k]

/-- Multiplication from the conjugation semidirect product restricts on its normal factor to the
closed-subgroup quotient morphism. -/
@[reassoc (attr := simp)]
theorem productMapOfNormal_comp_coordinateInl
    (H : _root_.CommHopfAlgCat.{u} k) (I J : HopfIdeal k H) (hI : I.IsNormal) :
    productMapOfNormal H I J hI ≫ normalSemidirectProductCoordinateInl H I J hI =
      mkQuotient H I := by
  have _ : IsMonHom.Normal (quotientGrpObjInclusion H I) :=
    (quotientGrpObjInclusion_normal_iff H I).2 hI
  rw [normalSemidirectProductCoordinateInl_def, ← Category.assoc]
  apply grpObjMap_injective
  rw [grpObjMap_comp, grpObjMap_comp, GrpObj.Action.grpObjMap_coordinateInl,
    grpObjMap_productMapOfNormal]
  rw [← quotientGrpObjInclusion_def]
  have hrestriction :
      let A := GrpObj.Action.normalConjugation
        (quotientGrpObjInclusion H I) (quotientGrpObjInclusion H J)
      A.inl.hom.hom ≫
          (GrpObj.Action.normalSemidirectMul
            (quotientGrpObjInclusion H I) (quotientGrpObjInclusion H J)).hom.hom =
        quotientGrpObjInclusion H I := by
    simpa only [Grp.comp_hom_hom, Grp.ofHom_hom_hom] using
      congrArg (fun f ↦ f.hom.hom) (GrpObj.Action.inl_comp_normalSemidirectMul
        (quotientGrpObjInclusion H I) (quotientGrpObjInclusion H J))
  exact hrestriction

/-- Multiplication from the conjugation semidirect product restricts on its acting factor to the
closed-subgroup quotient morphism. -/
@[reassoc (attr := simp)]
theorem productMapOfNormal_comp_coordinateInr
    (H : _root_.CommHopfAlgCat.{u} k) (I J : HopfIdeal k H) (hI : I.IsNormal) :
    productMapOfNormal H I J hI ≫ normalSemidirectProductCoordinateInr H I J hI =
      mkQuotient H J := by
  have _ : IsMonHom.Normal (quotientGrpObjInclusion H I) :=
    (quotientGrpObjInclusion_normal_iff H I).2 hI
  rw [normalSemidirectProductCoordinateInr_def, ← Category.assoc]
  apply grpObjMap_injective
  rw [grpObjMap_comp, grpObjMap_comp, GrpObj.Action.grpObjMap_coordinateInr,
    grpObjMap_productMapOfNormal]
  rw [← quotientGrpObjInclusion_def]
  have hrestriction :
      let A := GrpObj.Action.normalConjugation
        (quotientGrpObjInclusion H I) (quotientGrpObjInclusion H J)
      A.inr.hom.hom ≫
          (GrpObj.Action.normalSemidirectMul
            (quotientGrpObjInclusion H I) (quotientGrpObjInclusion H J)).hom.hom =
        quotientGrpObjInclusion H J := by
    simpa only [Grp.comp_hom_hom, Grp.ofHom_hom_hom] using
      congrArg (fun f ↦ f.hom.hom) (GrpObj.Action.inr_comp_normalSemidirectMul
        (quotientGrpObjInclusion H I) (quotientGrpObjInclusion H J))
  exact hrestriction

end

variable {k : Type u} [Field k]

/-- The defining Hopf ideal of the multiplication image lies below the ideal of the normal
factor. Equivalently, the product image contains that factor as a closed subgroup scheme. -/
theorem ker_productMapOfNormal_le_left
    (H : _root_.CommHopfAlgCat.{u} k) (I J : HopfIdeal k H) (hI : I.IsNormal) :
    HopfIdeal.ker (productMapOfNormal H I J hI).hom ≤ I := by
  calc
    HopfIdeal.ker (productMapOfNormal H I J hI).hom ≤
        HopfIdeal.ker ((normalSemidirectProductCoordinateInl H I J hI).hom.comp
          (productMapOfNormal H I J hI).hom) :=
      HopfIdeal.ker_le_ker_comp _ _
    _ = HopfIdeal.ker (mkQuotient H I).hom := by
      rw [← _root_.CommHopfAlgCat.hom_comp,
        productMapOfNormal_comp_coordinateInl]
    _ = I := HopfIdeal.ker_mkBialgHom I

/-- The defining Hopf ideal of the multiplication image lies below the ideal of the acting
factor. Equivalently, the product image contains that factor as a closed subgroup scheme. -/
theorem ker_productMapOfNormal_le_right
    (H : _root_.CommHopfAlgCat.{u} k) (I J : HopfIdeal k H) (hI : I.IsNormal) :
    HopfIdeal.ker (productMapOfNormal H I J hI).hom ≤ J := by
  calc
    HopfIdeal.ker (productMapOfNormal H I J hI).hom ≤
        HopfIdeal.ker ((normalSemidirectProductCoordinateInr H I J hI).hom.comp
          (productMapOfNormal H I J hI).hom) :=
      HopfIdeal.ker_le_ker_comp _ _
    _ = HopfIdeal.ker (mkQuotient H J).hom := by
      rw [← _root_.CommHopfAlgCat.hom_comp,
        productMapOfNormal_comp_coordinateInr]
    _ = J := HopfIdeal.ker_mkBialgHom J

/-- The coordinate algebra map of simultaneous ambient conjugation on the normal semidirect
product. -/
private noncomputable def normalSemidirectConjugationAlgHom
    (H : _root_.CommHopfAlgCat.{u} k) (I J : HopfIdeal k H)
    (hI : I.IsNormal) (hJ : J.IsNormal) :
    (quotientNormalConjugation H I J hI).coordinateHopfAlgebra →ₐ[k]
      (H ⊗[k] (quotientNormalConjugation H I J hI).coordinateHopfAlgebra) :=
  let i := quotientGrpObjInclusion H I
  let j := quotientGrpObjInclusion H J
  let _ : IsMonHom.Normal i := (quotientGrpObjInclusion_normal_iff H I).2 hI
  let _ : IsMonHom.Normal j := (quotientGrpObjInclusion_normal_iff H J).2 hJ
  let A := GrpObj.Action.normalConjugation i j
  let _ := A.semidirectProductGrpObj
  (GrpObj.Action.normalSemidirectConjugation i j).hom.unop.hom

private theorem productMapOfNormal_conjugation_equivariant
    (H : _root_.CommHopfAlgCat.{u} k) (I J : HopfIdeal k H)
    (hI : I.IsNormal) (hJ : J.IsNormal) :
    (Algebra.TensorProduct.map (AlgHom.id k H)
        ((productMapOfNormal H I J hI ≫
          (normalSemidirectProductIso H I J hI).hom).hom.toAlgHom)).comp
        (HopfAlgebra.conjugationAlgHom (R := k) (H := H)) =
      (normalSemidirectConjugationAlgHom H I J hI hJ).comp
        ((productMapOfNormal H I J hI ≫
          (normalSemidirectProductIso H I J hI).hom).hom.toAlgHom) := by
  let i := quotientGrpObjInclusion H I
  let j := quotientGrpObjInclusion H J
  let _ : IsMonHom.Normal i := (quotientGrpObjInclusion_normal_iff H I).2 hI
  let _ : IsMonHom.Normal j := (quotientGrpObjInclusion_normal_iff H J).2 hJ
  let A := GrpObj.Action.normalConjugation i j
  let _ := A.semidirectProductGrpObj
  have hequiv := GrpObj.Action.normalSemidirectMul_equivariant i j
  have hproduct : grpObjMap (productMapOfNormal H I J hI ≫
      (normalSemidirectProductIso H I J hI).hom) =
      (GrpObj.Action.normalSemidirectMul i j).hom.hom :=
    by
      rw [grpObjMap_comp]
      exact grpObjMap_productMapOfNormal H I J hI
  rw [← hproduct] at hequiv
  have hunop := congrArg (fun q ↦ q.unop.hom) hequiv.symm
  have hleft :
      (MonoidalCategoryStruct.whiskerLeft (grpObj H)
          (grpObjMap (productMapOfNormal H I J hI ≫
            (normalSemidirectProductIso H I J hI).hom)) ≫
        GrpObj.conj (grpObj H)).unop.hom =
        (Algebra.TensorProduct.map (AlgHom.id k H)
          ((productMapOfNormal H I J hI ≫
            (normalSemidirectProductIso H I J hI).hom).hom.toAlgHom)).comp
            (HopfAlgebra.conjugationAlgHom (R := k) (H := H)) := by
    rw [unop_comp, CommAlgCat.hom_comp, whiskerLeft_grpObjMap_unop_hom,
      grpObj_conj_unop_hom]
  have hright :
      ((GrpObj.Action.normalSemidirectConjugation i j).hom ≫
          grpObjMap (productMapOfNormal H I J hI ≫
            (normalSemidirectProductIso H I J hI).hom)).unop.hom =
        (normalSemidirectConjugationAlgHom H I J hI hJ).comp
          ((productMapOfNormal H I J hI ≫
            (normalSemidirectProductIso H I J hI).hom).hom.toAlgHom) := by
    have hproductHom := congrArg (fun q ↦ q.unop.hom) hproduct
    rw [grpObjMap_unop_hom] at hproductHom
    rw [hproduct, hproductHom]
    -- Expanding the local action instances identifies the named coordinate map with the unop of
    -- categorical semidirect conjugation, and composition in the opposite category reverses.
    rfl
  exact hleft.symm.trans (hunop.trans hright)

/-- If both factors are normal, the Hopf ideal defining their scheme-theoretic multiplication
image is normal. Thus the product image is a normal closed affine subgroup of the ambient group. -/
theorem isNormal_ker_productMapOfNormal
    (H : _root_.CommHopfAlgCat.{u} k) (I J : HopfIdeal k H)
    (hI : I.IsNormal) (hJ : J.IsNormal) :
    (HopfIdeal.ker (productMapOfNormal H I J hI).hom).IsNormal := by
  let e := normalSemidirectProductIso H I J hI
  let f := productMapOfNormal H I J hI
  have hnormal : (HopfIdeal.ker (f ≫ e.hom).hom).IsNormal :=
    HopfIdeal.isNormal_ker_of_conjugation_equivariant
      (f ≫ e.hom).hom
      (normalSemidirectConjugationAlgHom H I J hI hJ)
      (productMapOfNormal_conjugation_equivariant H I J hI hJ)
  have hker : HopfIdeal.ker f.hom = HopfIdeal.ker (f ≫ e.hom).hom := by
    apply HopfIdeal.ext
    intro x
    rw [HopfIdeal.mem_ker, HopfIdeal.mem_ker]
    constructor
    · intro hx
      simp [hx]
    · intro hx
      have hinv := congrArg (fun y ↦ e.inv.hom y) hx
      simpa using hinv
  rw [hker]
  exact hnormal

end

end TauCeti.CommHopfAlgCat
