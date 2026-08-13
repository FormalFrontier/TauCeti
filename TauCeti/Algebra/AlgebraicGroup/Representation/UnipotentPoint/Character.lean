/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Basic

/-!
# Unipotent points and algebraic characters

A group-like element of a coordinate Hopf algebra is the coordinate-ring incarnation of an
algebraic character. Its associated one-dimensional comodule lets a point act by evaluation at
that group-like element. Consequently a unipotent point evaluates every algebraic character at
one: a unipotent automorphism of a one-dimensional vector space is necessarily the identity.

This is the pointwise representation-theoretic input to the theorem that a connected unipotent
group has no nontrivial characters. Promoting the pointwise conclusion to equality of characters
requires the separate fact that algebraic-closure-valued points separate functions on a smooth
finite-type affine group.

## Main declaration

* `TauCeti.HopfAlgebra.IsUnipotentPoint.apply_groupLike`: a unipotent point evaluates every
  group-like element at one.

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

universe u v x

/-- A unipotent point evaluates every group-like element of the coordinate Hopf algebra at one.

Group-like elements are the coordinate-ring incarnation of algebraic characters. The associated
rank-one comodule turns evaluation at `x` into a one-dimensional point action, which can be
unipotent only when that scalar is one. -/
theorem IsUnipotentPoint.apply_groupLike
    {F : Type u} {C : Type v} {L : Type x} [Field F] [Semiring C]
    [_root_.HopfAlgebra F C] [Field L] [Algebra F L]
    {g : WithConv (C →ₐ[F] L)} (hg : IsUnipotentPoint g) (x : GroupLike F C) :
    g.ofConv x = 1 := by
  let _ : Comodule F C F := Comodule.groupLike (R := F) (C := C) (M := F) x
  let M : FGComoduleCat.{u, v, u} F C := FGComoduleCat.of (R := F) (C := C) F
  have hdim : Module.finrank L (L ⊗[F] F) = 1 := by
    rw [(TensorProduct.AlgebraTensorModule.rid F L L).finrank_eq, Module.finrank_self]
  have haction := (hg M).eq_one_of_finrank_eq_one hdim
  let z : L ⊗[F] F := (1 : L) ⊗ₜ[F] (1 : F)
  have happ := congrArg
    (fun q : LinearMap.GeneralLinearGroup L (L ⊗[F] F) => q • z) haction
  simp only [LinearMap.GeneralLinearGroup.ofLinearEquiv_smul, one_smul] at happ
  have hpoint := DFunLike.congr_fun (Comodule.pointsAction_toLinearMap M g) z
  have hend : Comodule.endOfPoint M g.ofConv z = z := hpoint.symm.trans happ
  simp only [z, Comodule.endOfPoint_groupLike_tmul, one_mul] at hend
  have := congrArg (TensorProduct.AlgebraTensorModule.rid F L L) hend
  simpa using this

end HopfAlgebra

end TauCeti
