/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SemidirectProduct
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Product
public import TauCeti.RepresentationTheory.Unipotent.NormalJoin

/-!
# Smooth unipotence of semidirect products

An internal action of affine groups equips the product of their underlying affine schemes with
the semidirect-product group law. This file proves that if both factors are geometrically
unipotent, then so is the semidirect product, and consequently that semidirect products of smooth
unipotent affine groups are smooth unipotent.

The pointwise argument works in an arbitrary finite-dimensional representation of the semidirect
product. The images of the two factors act unipotently by restriction. The first factor is normal,
and the two factor images generate the whole semidirect product, so the normal-join theorem makes
every element act unipotently. Smoothness depends only on the underlying algebra, which is the
tensor product of the coordinate algebras.

## Main declarations

* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.semidirectProduct`: internal
  semidirect products preserve geometric-point unipotence.
* `TauCeti.smoothUnipotentCommHopfAlgProperty.semidirectProduct`: internal semidirect products of
  smooth unipotent affine groups are smooth unipotent.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, Proposition 2.4.12.

This supplies the smooth-unipotence step in Layer 5, "The unipotent radical", of the
ReductiveGroups roadmap. The binary product of two radical candidates is formed as the image of
multiplication from their conjugation semidirect product; the source must first be known to be
smooth unipotent.
-/

public section

open CategoryTheory Opposite WithConv
open scoped CategoryTheory.MonObj TensorProduct

namespace TauCeti

universe u


noncomputable section

namespace geometricallyUnipotentPointsCommHopfAlgProperty

variable (k : Type u) [Field k]

/-- An internal semidirect product of affine groups with geometrically unipotent points again has
geometrically unipotent points. -/
theorem semidirectProduct (H K : _root_.CommHopfAlgCat.{u} k)
    (A : GrpObj.Action (CommHopfAlgCat.grpObj K) (CommHopfAlgCat.grpObj H))
    (hH : geometricallyUnipotentPointsCommHopfAlgProperty k H)
    (hK : geometricallyUnipotentPointsCommHopfAlgProperty k K) :
    geometricallyUnipotentPointsCommHopfAlgProperty k A.coordinateHopfAlgebra := by
  rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff] at hH hK ⊢
  intro g
  rw [HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one]
  intro M
  let L := CommAlgCat.of k (AlgebraicClosure k)
  let X := op L
  let _ := A.semidirectProductGrpObj
  let eS := CommHopfAlgCat.grpObjPointsMulEquiv A.coordinateHopfAlgebra X
  let e := A.pointMulEquiv X
  let ePoint : HopfAlgebra.points (R := k) (H := A.coordinateHopfAlgebra) L ≃*
      ((X ⟶ CommHopfAlgCat.grpObj H) ⋊[A.toMulAutHom X]
        (X ⟶ CommHopfAlgCat.grpObj K)) := eS.symm.trans e
  let rho := Comodule.pointsRepresentation (R := k) (H := A.coordinateHopfAlgebra)
    (A := AlgebraicClosure k) M
  let U : Subgroup (HopfAlgebra.points (R := k) (H := A.coordinateHopfAlgebra) L) :=
    Subgroup.comap ePoint.toMonoidHom
      (SemidirectProduct.rightHom (N := X ⟶ CommHopfAlgCat.grpObj H)
        (G := X ⟶ CommHopfAlgCat.grpObj K)).ker
  let W : Subgroup (HopfAlgebra.points (R := k) (H := A.coordinateHopfAlgebra) L) :=
    Subgroup.comap ePoint.toMonoidHom
      (SemidirectProduct.inr (N := X ⟶ CommHopfAlgCat.grpObj H)
        (G := X ⟶ CommHopfAlgCat.grpObj K)).range
  let _ : U.Normal := Subgroup.normal_comap ePoint.toMonoidHom
  have hU (x : U) : IsNilpotent (rho x - 1) := by
    let n : X ⟶ CommHopfAlgCat.grpObj H := (ePoint x).left
    let p := CommHopfAlgCat.grpObjPointsMulEquiv H X n
    have hxright : (ePoint x).right = 1 := by
      exact x.2
    have hpoint : x = AlgHom.mapDomain A.coordinateInl.hom p := by
      apply ePoint.injective
      rw [A.pointMulEquiv_mapDomain_coordinateInl]
      rw [MulEquiv.symm_apply_apply]
      exact SemidirectProduct.ext rfl hxright
    have hu := (hH p).mapDomain A.coordinateInl.hom
    rw [← hpoint] at hu
    have huM := hu
    rw [HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one] at huM
    simpa only [rho, Comodule.pointsRepresentation_apply] using huM M
  have hW (x : W) : IsNilpotent (rho x - 1) := by
    obtain ⟨r, hr⟩ := x.2
    let p := CommHopfAlgCat.grpObjPointsMulEquiv K X r
    have hpoint : x = AlgHom.mapDomain A.coordinateInr.hom p := by
      apply ePoint.injective
      rw [A.pointMulEquiv_mapDomain_coordinateInr]
      rw [MulEquiv.symm_apply_apply]
      exact hr.symm
    have hu := (hK p).mapDomain A.coordinateInr.hom
    rw [← hpoint] at hu
    have huM := hu
    rw [HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one] at huM
    simpa only [rho, Comodule.pointsRepresentation_apply] using huM M
  have hg : g ∈ U ⊔ W := by
    let qU := ePoint.symm (SemidirectProduct.inl (ePoint g).left)
    let qW := ePoint.symm (SemidirectProduct.inr (ePoint g).right)
    have hqU : qU ∈ U := by
      simp only [U, Subgroup.mem_comap, MonoidHom.mem_ker]
      simp only [qU, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
        SemidirectProduct.rightHom_inl]
    have hqW : qW ∈ W := by
      simp only [W, Subgroup.mem_comap, MonoidHom.mem_range]
      exact ⟨(ePoint g).right, by
        simp only [qW, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]⟩
    have hfactor : g = qU * qW := by
      apply ePoint.injective
      simp only [map_mul, qU, qW, MulEquiv.apply_symm_apply,
        SemidirectProduct.inl_left_mul_inr_right]
    rw [hfactor]
    exact Subgroup.mul_mem_sup hqU hqW
  have hgnilpotent := rho.isNilpotent_sub_one_of_mem_sup_of_le_normalizer_isUnipotent
    U W Subgroup.le_normalizer_of_normal hU hW hg
  simpa only [rho, Comodule.pointsRepresentation_apply] using hgnilpotent

end geometricallyUnipotentPointsCommHopfAlgProperty

namespace smoothUnipotentCommHopfAlgProperty

variable (k : Type u) [Field k]

/-- An internal semidirect product of smooth unipotent finite-type affine groups is smooth
unipotent. -/
theorem semidirectProduct (H K : FiniteTypeCommHopfAlgCat.{u, u} k)
    (A : GrpObj.Action (CommHopfAlgCat.grpObj K.obj) (CommHopfAlgCat.grpObj H.obj))
    (hH : smoothUnipotentCommHopfAlgProperty k H)
    (hK : smoothUnipotentCommHopfAlgProperty k K) :
    smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.of k A.coordinateHopfAlgebra) := by
  have hH' := (smoothUnipotentCommHopfAlgProperty_iff k H).mp hH
  have hK' := (smoothUnipotentCommHopfAlgProperty_iff k K).mp hK
  have hHpoints : geometricallyUnipotentPointsCommHopfAlgProperty k H.obj := by
    rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff]
    exact hH'.2
  have hKpoints : geometricallyUnipotentPointsCommHopfAlgProperty k K.obj := by
    rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff]
    exact hK'.2
  have hproduct := smoothUnipotentCommHopfAlgProperty.tensorProduct k H K hH hK
  have hproduct' :=
    (smoothUnipotentCommHopfAlgProperty_iff k
      (FiniteTypeCommHopfAlgCat.tensorProduct H K)).mp hproduct
  rw [smoothUnipotentCommHopfAlgProperty_iff]
  let smoothProduct : Algebra.Smooth k (H.obj ⊗[k] K.obj) := hproduct'.1
  refine ⟨Algebra.Smooth.of_equiv A.coordinateAlgEquiv.symm, ?_⟩
  rw [← geometricallyUnipotentPointsCommHopfAlgProperty_iff]
  exact geometricallyUnipotentPointsCommHopfAlgProperty.semidirectProduct
    k H.obj K.obj A hHpoints hKpoints

end smoothUnipotentCommHopfAlgProperty

end

end TauCeti
