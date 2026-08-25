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
* `TauCeti.CommHopfAlgCat.productOfNormal_definingIdeal_le_left` and
  `TauCeti.CommHopfAlgCat.productOfNormal_definingIdeal_le_right`: the product image contains both
  factors.
* `TauCeti.CommHopfAlgCat.isNormal_productOfNormal_definingIdeal`: the product of two normal
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

variable {k : Type u} [Field k]

/-- Multiplication from the conjugation semidirect product restricts on its normal factor to the
closed-subgroup quotient morphism. -/
@[reassoc]
theorem productMapOfNormal_comp_coordinateInl
    (H : _root_.CommHopfAlgCat.{u} k) (I J : HopfIdeal k H) (hI : I.IsNormal) :
    productMapOfNormal H I J hI ≫ (quotientNormalConjugation H I J hI).coordinateInl =
      mkQuotient H I := by
  have _ : IsMonHom.Normal (quotientGrpObjInclusion H I) :=
    (quotientGrpObjInclusion_normal_iff H I).2 hI
  apply grpObjMap_injective
  rw [grpObjMap_comp, GrpObj.Action.grpObjMap_coordinateInl]
  rw [grpObjMap_productMapOfNormal]
  rw [← quotientGrpObjInclusion_def]
  exact GrpObj.Action.inl_hom_comp_normalSemidirectMul_hom
    (quotientGrpObjInclusion H I) (quotientGrpObjInclusion H J)

/-- Multiplication from the conjugation semidirect product restricts on its acting factor to the
closed-subgroup quotient morphism. -/
@[reassoc]
theorem productMapOfNormal_comp_coordinateInr
    (H : _root_.CommHopfAlgCat.{u} k) (I J : HopfIdeal k H) (hI : I.IsNormal) :
    productMapOfNormal H I J hI ≫ (quotientNormalConjugation H I J hI).coordinateInr =
      mkQuotient H J := by
  have _ : IsMonHom.Normal (quotientGrpObjInclusion H I) :=
    (quotientGrpObjInclusion_normal_iff H I).2 hI
  apply grpObjMap_injective
  rw [grpObjMap_comp, GrpObj.Action.grpObjMap_coordinateInr]
  rw [grpObjMap_productMapOfNormal]
  rw [← quotientGrpObjInclusion_def]
  exact GrpObj.Action.inr_hom_comp_normalSemidirectMul_hom
    (quotientGrpObjInclusion H I) (quotientGrpObjInclusion H J)

/-- The defining Hopf ideal of the multiplication image lies below the ideal of the normal
factor. Equivalently, the product image contains that factor as a closed subgroup scheme. -/
theorem productOfNormal_definingIdeal_le_left
    (H : _root_.CommHopfAlgCat.{u} k) (I J : HopfIdeal k H) (hI : I.IsNormal) :
    HopfIdeal.ker (productMapOfNormal H I J hI).hom ≤ I := by
  rw [← HopfIdeal.toIdeal_le_toIdeal]
  intro x hx
  rw [← mkQuotient_eq_zero_iff H I x]
  have hx0 : (productMapOfNormal H I J hI).hom x = 0 :=
    (HopfIdeal.mem_ker _).mp hx
  have hcomp := congrArg (fun f : H ⟶ quotient H I ↦ f.hom x)
    (productMapOfNormal_comp_coordinateInl H I J hI)
  change ((quotientNormalConjugation H I J hI).coordinateInl).hom
      ((productMapOfNormal H I J hI).hom x) = (mkQuotient H I).hom x at hcomp
  rw [← hcomp, hx0, map_zero]

/-- The defining Hopf ideal of the multiplication image lies below the ideal of the acting
factor. Equivalently, the product image contains that factor as a closed subgroup scheme. -/
theorem productOfNormal_definingIdeal_le_right
    (H : _root_.CommHopfAlgCat.{u} k) (I J : HopfIdeal k H) (hI : I.IsNormal) :
    HopfIdeal.ker (productMapOfNormal H I J hI).hom ≤ J := by
  rw [← HopfIdeal.toIdeal_le_toIdeal]
  intro x hx
  rw [← mkQuotient_eq_zero_iff H J x]
  have hx0 : (productMapOfNormal H I J hI).hom x = 0 :=
    (HopfIdeal.mem_ker _).mp hx
  have hcomp := congrArg (fun f : H ⟶ quotient H J ↦ f.hom x)
    (productMapOfNormal_comp_coordinateInr H I J hI)
  change ((quotientNormalConjugation H I J hI).coordinateInr).hom
      ((productMapOfNormal H I J hI).hom x) = (mkQuotient H J).hom x at hcomp
  rw [← hcomp, hx0, map_zero]

private theorem whiskerLeft_grpObjMap_unop_hom
    {H K : _root_.CommHopfAlgCat.{u} k} (f : H ⟶ K) :
    (MonoidalCategoryStruct.whiskerLeft (grpObj H) (grpObjMap f)).unop.hom =
      Algebra.TensorProduct.map (AlgHom.id k H) f.hom.toAlgHom := by
  change Algebra.TensorProduct.map (AlgHom.id k H) (grpObjMap f).unop.hom = _
  rw [grpObjMap_unop_hom]

private theorem grpObj_conj_unop_hom (H : _root_.CommHopfAlgCat.{u} k) :
    (GrpObj.conj (grpObj H)).unop.hom =
      HopfAlgebra.conjugationAlgHom (R := k) (H := H) := by
  have hinv :
      ((WithConv.toConv
        (Bialgebra.TensorProduct.includeLeft (R := k) (H₁ := H) (H₂ := H)).toAlgHom)⁻¹).ofConv =
        (Bialgebra.TensorProduct.includeLeft (R := k) (H₁ := H) (H₂ := H)).toAlgHom.comp
          (HopfAlgebra.antipodeAlgHom k H) := rfl
  have hmul :
      (WithConv.toConv
          (Bialgebra.TensorProduct.includeLeft (R := k) (H₁ := H) (H₂ := H)).toAlgHom *
        WithConv.toConv
          (Bialgebra.TensorProduct.includeRight (R := k) (H₁ := H) (H₂ := H)).toAlgHom).ofConv =
        (Algebra.TensorProduct.lift
          (Bialgebra.TensorProduct.includeLeft (R := k) (H₁ := H) (H₂ := H)).toAlgHom
          (Bialgebra.TensorProduct.includeRight (R := k) (H₁ := H) (H₂ := H)).toAlgHom
          (fun _ _ ↦ .all _ _)).comp (Bialgebra.comulAlgHom k H) := by
    ext x
    exact AlgHom.convMul_apply _ _ x
  apply WithConv.toConv_injective
  rw [HopfAlgebra.toConv_conjugationAlgHom]
  rw [GrpObj.conj, CategoryTheory.Hom.mul_def, CategoryTheory.Hom.mul_def,
    CategoryTheory.Hom.inv_def]
  ext x
  simp only [unop_comp, CommAlgCat.hom_comp, CommAlgCat.lift_unop_hom,
    CommAlgCat.mul_op_of_unop_hom, CommAlgCat.inv_op_of_unop_hom,
    CommAlgCat.fst_unop_hom, CommAlgCat.snd_unop_hom,
    AlgHom.convMul_apply, hinv, hmul, AlgHom.coe_comp, Function.comp_apply]
  congr 1
  apply Algebra.TensorProduct.ext'
  intro a b
  simp

/-- The coordinate algebra map of simultaneous ambient conjugation on the normal semidirect
product. -/
private noncomputable def normalSemidirectConjugationAlgHom
    (H : _root_.CommHopfAlgCat.{u} k) (I J : HopfIdeal k H)
    (hI : I.IsNormal) (hJ : J.IsNormal) :
    normalSemidirectProduct H I J hI →ₐ[k]
      (H ⊗[k] normalSemidirectProduct H I J hI) := by
  let i := quotientGrpObjInclusion H I
  let j := quotientGrpObjInclusion H J
  let _ : IsMonHom.Normal i := (quotientGrpObjInclusion_normal_iff H I).2 hI
  let _ : IsMonHom.Normal j := (quotientGrpObjInclusion_normal_iff H J).2 hJ
  let A := GrpObj.Action.normalConjugation i j
  let _ := A.semidirectProductGrpObj
  dsimp only [normalSemidirectProduct]
  exact (GrpObj.Action.normalSemidirectConjugation i j).hom.unop.hom

private theorem productMapOfNormal_conjugation_equivariant
    (H : _root_.CommHopfAlgCat.{u} k) (I J : HopfIdeal k H)
    (hI : I.IsNormal) (hJ : J.IsNormal) :
    (Algebra.TensorProduct.map (AlgHom.id k H)
        (productMapOfNormal H I J hI).hom.toAlgHom).comp
        (HopfAlgebra.conjugationAlgHom (R := k) (H := H)) =
      (normalSemidirectConjugationAlgHom H I J hI hJ).comp
        (productMapOfNormal H I J hI).hom.toAlgHom := by
  let i := quotientGrpObjInclusion H I
  let j := quotientGrpObjInclusion H J
  let _ : IsMonHom.Normal i := (quotientGrpObjInclusion_normal_iff H I).2 hI
  let _ : IsMonHom.Normal j := (quotientGrpObjInclusion_normal_iff H J).2 hJ
  let A := GrpObj.Action.normalConjugation i j
  let _ := A.semidirectProductGrpObj
  have hequiv := GrpObj.Action.normalSemidirectMul_equivariant i j
  have hproduct : grpObjMap (productMapOfNormal H I J hI) =
      (GrpObj.Action.normalSemidirectMul i j).hom.hom :=
    grpObjMap_productMapOfNormal H I J hI
  rw [← hproduct] at hequiv
  have hunop := congrArg (fun q ↦ q.unop.hom) hequiv.symm
  have hleft :
      (MonoidalCategoryStruct.whiskerLeft (grpObj H)
          (grpObjMap (productMapOfNormal H I J hI)) ≫
        GrpObj.conj (grpObj H)).unop.hom =
        (Algebra.TensorProduct.map (AlgHom.id k H)
          (productMapOfNormal H I J hI).hom.toAlgHom).comp
            (HopfAlgebra.conjugationAlgHom (R := k) (H := H)) := by
    rw [unop_comp, CommAlgCat.hom_comp, whiskerLeft_grpObjMap_unop_hom,
      grpObj_conj_unop_hom]
  have hright :
      ((GrpObj.Action.normalSemidirectConjugation i j).hom ≫
          grpObjMap (productMapOfNormal H I J hI)).unop.hom =
        (normalSemidirectConjugationAlgHom H I J hI hJ).comp
          (productMapOfNormal H I J hI).hom.toAlgHom := by
    rw [hproduct, productMapOfNormal_hom]
    dsimp only [normalSemidirectConjugationAlgHom]
    rfl
  exact hleft.symm.trans (hunop.trans hright)

/-- If both factors are normal, the Hopf ideal defining their scheme-theoretic multiplication
image is normal. Thus the product image is a normal closed affine subgroup of the ambient group. -/
theorem isNormal_productOfNormal_definingIdeal
    (H : _root_.CommHopfAlgCat.{u} k) (I J : HopfIdeal k H)
    (hI : I.IsNormal) (hJ : J.IsNormal) :
    (HopfIdeal.ker (productMapOfNormal H I J hI).hom).IsNormal :=
  HopfIdeal.isNormal_ker_of_conjugation_equivariant
    (productMapOfNormal H I J hI).hom
    (normalSemidirectConjugationAlgHom H I J hI hJ)
    (productMapOfNormal_conjugation_equivariant H I J hI hJ)

end

end TauCeti.CommHopfAlgCat
