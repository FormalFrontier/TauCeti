/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.Product
public import TauCeti.CategoryTheory.Monoidal.SemidirectProduct.Basic

/-!
# Coordinate Hopf algebras of semidirect products

An internal action between the group objects represented by commutative Hopf algebras equips the
product of their underlying affine schemes with a semidirect-product group law. This file carries
that group object back across Mathlib's commutative-Hopf-algebra/cogroup equivalence, records the
coordinate morphisms representing the two canonical factor inclusions, and computes them on
algebra-valued points.

## Main declarations

* `TauCeti.GrpObj.Action.coordinateHopfAlgebra`: the coordinate Hopf algebra of an internal
  semidirect product.
* `TauCeti.GrpObj.Action.coordinateAlgEquiv`: its underlying tensor-product coordinate algebra.
* `TauCeti.GrpObj.Action.coordinateInl` and `coordinateInr`: the coordinate morphisms representing
  the two factor inclusions.
* `TauCeti.GrpObj.Action.pointMulEquiv_mapDomain_coordinateInl` and
  `pointMulEquiv_mapDomain_coordinateInr`: their formulas under the semidirect-product point
  equivalence.

## References

This uses Mathlib's `commHopfAlgCatEquivCogrpCommAlgCat` and Tau Ceti's group-object Yoneda
equivalence. It is the coordinate bridge used by the semidirect-product construction in Layer 5,
"The unipotent radical", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory Opposite WithConv
open scoped CategoryTheory.MonObj TensorProduct

namespace TauCeti.GrpObj.Action

universe u

noncomputable section

variable {k : Type u} [CommRing k]
variable {H K : _root_.CommHopfAlgCat.{u} k}

/-- The coordinate Hopf algebra of an internal semidirect product. -/
noncomputable abbrev coordinateHopfAlgebra
    (A : GrpObj.Action (CommHopfAlgCat.grpObj K) (CommHopfAlgCat.grpObj H)) :
    _root_.CommHopfAlgCat.{u} k :=
  (commHopfAlgCatEquivCogrpCommAlgCat k).inverse.obj (op A.semidirectProduct)

/-- The underlying coordinate algebra of a semidirect product is the tensor product of the
coordinate algebras of its factors. -/
noncomputable def coordinateAlgEquiv
    (A : GrpObj.Action (CommHopfAlgCat.grpObj K) (CommHopfAlgCat.grpObj H)) :
    A.coordinateHopfAlgebra ≃ₐ[k] H ⊗[k] K :=
  AlgEquiv.refl

/-- The coordinate algebra of a semidirect product is finite type when both factors are. -/
noncomputable instance coordinateHopfAlgebra_finiteType
    (A : GrpObj.Action (CommHopfAlgCat.grpObj K) (CommHopfAlgCat.grpObj H))
    [Algebra.FiniteType k H] [Algebra.FiniteType k K] :
    Algebra.FiniteType k A.coordinateHopfAlgebra :=
  Algebra.FiniteType.equiv
    (FiniteTypeCommHopfAlgCat.tensorProduct_finiteType (R := k) H K) A.coordinateAlgEquiv.symm

/-- The coordinate morphism representing inclusion of the normal factor in a semidirect
product. -/
noncomputable def coordinateInl
    (A : GrpObj.Action (CommHopfAlgCat.grpObj K) (CommHopfAlgCat.grpObj H)) :
    A.coordinateHopfAlgebra ⟶ H :=
  (commHopfAlgCatEquivCogrpCommAlgCat k).inverse.map (op A.inl)

/-- The coordinate morphism representing inclusion of the acting factor in a semidirect
product. -/
noncomputable def coordinateInr
    (A : GrpObj.Action (CommHopfAlgCat.grpObj K) (CommHopfAlgCat.grpObj H)) :
    A.coordinateHopfAlgebra ⟶ K :=
  (commHopfAlgCatEquivCogrpCommAlgCat k).inverse.map (op A.inr)

/-- The represented group-object morphism associated to `coordinateInl` is the canonical
inclusion of the normal factor. -/
@[simp]
theorem grpObjMap_coordinateInl
    (A : GrpObj.Action (CommHopfAlgCat.grpObj K) (CommHopfAlgCat.grpObj H)) :
    letI := A.semidirectProductGrpObj
    CommHopfAlgCat.grpObjMap A.coordinateInl = A.inl.hom.hom := by
  let _ := A.semidirectProductGrpObj
  apply Quiver.Hom.unop_inj
  rw [CommHopfAlgCat.grpObjMap_unop]
  rfl

/-- The represented group-object morphism associated to `coordinateInr` is the canonical
inclusion of the acting factor. -/
@[simp]
theorem grpObjMap_coordinateInr
    (A : GrpObj.Action (CommHopfAlgCat.grpObj K) (CommHopfAlgCat.grpObj H)) :
    letI := A.semidirectProductGrpObj
    CommHopfAlgCat.grpObjMap A.coordinateInr = A.inr.hom.hom := by
  let _ := A.semidirectProductGrpObj
  apply Quiver.Hom.unop_inj
  rw [CommHopfAlgCat.grpObjMap_unop]
  rfl

private theorem grpObjPointsMulEquiv_symm_mapDomain {B C : _root_.CommHopfAlgCat.{u} k}
    (f : B ⟶ C) (L : CommAlgCat.{u} k) (g : HopfAlgebra.points (R := k) (H := C) L) :
    (CommHopfAlgCat.grpObjPointsMulEquiv B (op L)).symm (AlgHom.mapDomain f.hom g) =
      (CommHopfAlgCat.grpObjPointsMulEquiv C (op L)).symm g ≫
        CommHopfAlgCat.grpObjMap f := by
  have hnat := CommHopfAlgCat.grpObjPointsMulEquiv_comp_grpObjMap f
    (op L) ((CommHopfAlgCat.grpObjPointsMulEquiv C (op L)).symm g)
  apply (CommHopfAlgCat.grpObjPointsMulEquiv B (op L)).injective
  simpa only [CommHopfAlgCat.mapPointsFunctor_app_apply, AlgHom.mapDomain_apply,
    MulEquiv.apply_symm_apply] using hnat.symm

/-- Under the point equivalence for a semidirect product, precomposition with `coordinateInl`
is the ordinary inclusion of the normal factor. -/
theorem pointMulEquiv_mapDomain_coordinateInl
    (A : GrpObj.Action (CommHopfAlgCat.grpObj K) (CommHopfAlgCat.grpObj H))
    (L : CommAlgCat.{u} k) (g : HopfAlgebra.points (R := k) (H := H) L) :
    letI := A.semidirectProductGrpObj
    ((CommHopfAlgCat.grpObjPointsMulEquiv A.coordinateHopfAlgebra (op L)).symm.trans
        (A.pointMulEquiv (op L))) (AlgHom.mapDomain A.coordinateInl.hom g) =
      SemidirectProduct.inl
        ((CommHopfAlgCat.grpObjPointsMulEquiv H (op L)).symm g) := by
  let _ := A.semidirectProductGrpObj
  -- Expose application of the composite equivalence; its intermediate object is definitionally
  -- the carrier of `A.semidirectProduct`, whose group-object implementation is intentionally
  -- hidden by the categorical semidirect-product API.
  change (A.pointMulEquiv (op L))
    ((CommHopfAlgCat.grpObjPointsMulEquiv A.coordinateHopfAlgebra (op L)).symm
      (AlgHom.mapDomain A.coordinateInl.hom g)) = _
  have hcat :
      (CommHopfAlgCat.grpObjPointsMulEquiv A.coordinateHopfAlgebra (op L)).symm
          (AlgHom.mapDomain A.coordinateInl.hom g) =
        (CommHopfAlgCat.grpObjPointsMulEquiv H (op L)).symm g ≫ A.inl.hom.hom := by
    rw [grpObjPointsMulEquiv_symm_mapDomain]
    rw [A.grpObjMap_coordinateInl]
    rfl
  rw [hcat, A.pointMulEquiv_comp_inl]

/-- Under the point equivalence for a semidirect product, precomposition with `coordinateInr`
is the ordinary inclusion of the acting factor. -/
theorem pointMulEquiv_mapDomain_coordinateInr
    (A : GrpObj.Action (CommHopfAlgCat.grpObj K) (CommHopfAlgCat.grpObj H))
    (L : CommAlgCat.{u} k) (g : HopfAlgebra.points (R := k) (H := K) L) :
    letI := A.semidirectProductGrpObj
    ((CommHopfAlgCat.grpObjPointsMulEquiv A.coordinateHopfAlgebra (op L)).symm.trans
        (A.pointMulEquiv (op L))) (AlgHom.mapDomain A.coordinateInr.hom g) =
      SemidirectProduct.inr
        ((CommHopfAlgCat.grpObjPointsMulEquiv K (op L)).symm g) := by
  let _ := A.semidirectProductGrpObj
  -- As above, expose application of the composite across the hidden group-object carrier.
  change (A.pointMulEquiv (op L))
    ((CommHopfAlgCat.grpObjPointsMulEquiv A.coordinateHopfAlgebra (op L)).symm
      (AlgHom.mapDomain A.coordinateInr.hom g)) = _
  have hcat :
      (CommHopfAlgCat.grpObjPointsMulEquiv A.coordinateHopfAlgebra (op L)).symm
          (AlgHom.mapDomain A.coordinateInr.hom g) =
        (CommHopfAlgCat.grpObjPointsMulEquiv K (op L)).symm g ≫ A.inr.hom.hom := by
    rw [grpObjPointsMulEquiv_symm_mapDomain]
    rw [A.grpObjMap_coordinateInr]
    rfl
  rw [hcat, A.pointMulEquiv_comp_inr]

end

end TauCeti.GrpObj.Action
