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
rank-one comodule turns evaluation at `x` into a scalar point action. Its difference from the
identity is nilpotent, so reducedness forces that scalar to be one. -/
@[simp]
theorem IsUnipotentPoint.apply_groupLike
    {F : Type u} {C : Type v} {L : Type x} [CommSemiring F] [Semiring C]
    [_root_.HopfAlgebra F C] [CommRing L] [IsReduced L] [Algebra F L]
    {g : WithConv (C →ₐ[F] L)} (hg : IsUnipotentPoint g) (x : GroupLike F C) :
    g.ofConv x = 1 := by
  let _ : Comodule F C F := Comodule.groupLike (R := F) (C := C) (M := F) x
  let M : FGComoduleCat.{u, v, u} F C := FGComoduleCat.of (R := F) (C := C) F
  have hnil :=
    (isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one g).mp hg M
  have haction : Comodule.endOfPoint M g.ofConv - 1 =
      (g.ofConv x - 1) • LinearMap.id := by
    rw [Comodule.endOfPoint_groupLike]
    apply LinearMap.ext
    intro z
    simp [sub_smul]
  let z : L ⊗[F] F := (1 : L) ⊗ₜ[F] (1 : F)
  rw [haction] at hnil
  obtain ⟨n, hn⟩ := hnil
  have hz := DFunLike.congr_fun hn z
  have hp : (g.ofConv x - 1) ^ n = 0 := by
    have := congrArg (TensorProduct.AlgebraTensorModule.rid F L L) hz
    simpa [z, smul_pow] using this
  exact sub_eq_zero.mp (IsReduced.eq_zero _ ⟨n, hp⟩)

end HopfAlgebra

end TauCeti
