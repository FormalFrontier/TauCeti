/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Basic

/-!
# Unipotent points and algebraic characters

A group-like element of a coordinate Hopf algebra is the coordinate-ring incarnation of an
algebraic character. Its associated rank-one comodule lets a point act by evaluation at that
group-like element. Consequently a unipotent point valued in a reduced ring evaluates every
algebraic character at one: the difference between that scalar action and the identity is
nilpotent, so the scalar itself must be one.

This is the pointwise representation-theoretic input to the theorem that a connected unipotent
group has no nontrivial characters. Promoting the pointwise conclusion to equality of characters
requires the separate fact that algebraic-closure-valued points separate functions on a smooth
finite-type affine group.

## Main declaration

* `TauCeti.HopfAlgebra.IsUnipotentPoint.apply_groupLike_eq_one`: a unipotent point evaluates
  every group-like element at one.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This advances Layer 5, "Unipotent groups", of the ReductiveGroups roadmap, specifically the
consequence that connected unipotent groups have no nontrivial characters.
-/

public section

open scoped TensorProduct

open WithConv

namespace TauCeti

namespace HopfAlgebra

universe u v w

/-- A unipotent point evaluates every group-like element of the coordinate Hopf algebra at one.

Group-like elements are the coordinate-ring incarnation of algebraic characters. The associated
rank-one comodule turns evaluation at the group-like element into a scalar point action. -/
@[simp]
theorem IsUnipotentPoint.apply_groupLike_eq_one
    {F : Type u} {C : Type v} {L : Type w} [CommSemiring F] [Semiring C]
    [_root_.HopfAlgebra F C] [CommRing L] [IsReduced L] [Algebra F L]
    {g : WithConv (C →ₐ[F] L)} (hg : IsUnipotentPoint g) (x : GroupLike F C) :
    g.ofConv x = 1 := by
  by_cases hL : Subsingleton L
  · let _ : Subsingleton L := hL
    exact Subsingleton.elim _ _
  let _ : Nontrivial L := not_subsingleton_iff_nontrivial.mp hL
  let _ : Comodule F C F := Comodule.groupLike (R := F) (C := C) (M := F) x
  let M : FGComoduleCat.{u, v, u} F C := FGComoduleCat.of (R := F) (C := C) F
  let e := TensorProduct.AlgebraTensorModule.rid F L L
  let _ : Module.Free L (L ⊗[F] F) := Module.Free.of_equiv e.symm
  have hdim : Module.finrank L (L ⊗[F] F) = 1 := by
    calc
      Module.finrank L (L ⊗[F] F) = Module.finrank L L := e.finrank_eq
      _ = 1 := Module.finrank_self L
  have hone := ((isUnipotentPoint_def g).mp hg M).eq_one_of_finrank_eq_one hdim
  have haction : Comodule.endOfPoint M g.ofConv = LinearMap.id := by
    apply LinearMap.ext
    intro z
    rw [← Comodule.pointsAction_toLinearMap]
    have := congrArg (fun f : LinearMap.GeneralLinearGroup L (L ⊗[F] F) ↦ f • z) hone
    simpa only [LinearMap.GeneralLinearGroup.ofLinearEquiv_smul, one_smul,
      LinearEquiv.coe_toLinearMap, LinearMap.id_coe, id_eq] using this
  -- The comodule instance on `M` is definitionally the local group-like instance above.
  rw [Comodule.endOfPoint_groupLike] at haction
  apply (LinearEquiv.smul_id_of_finrank_eq_one hdim).injective
  simpa only [LinearEquiv.smul_id_of_finrank_eq_one_apply, one_smul] using haction

end HopfAlgebra

end TauCeti
