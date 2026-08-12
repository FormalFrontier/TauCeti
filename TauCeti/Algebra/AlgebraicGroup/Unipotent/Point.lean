/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Basic
public import TauCeti.LinearAlgebra.JordanChevalley.Unipotent

/-!
# Unipotent points of an affine group

Let `H` be a Hopf algebra over a field `k` and let `K / k` be a field extension. A `K`-valued
point `g : H →ₐ[k] K` acts on the scalar extension of every finite-dimensional `H`-comodule.
This file calls `g` **unipotent** when every one of those linear automorphisms is unipotent,
meaning that its difference from the identity is nilpotent.

For the commutative coordinate Hopf algebra of an affine group scheme, taking `K` to be an
algebraic closure of `k` is precisely the representation-theoretic definition of a geometric
unipotent element. The quantification over all finite-dimensional comodules is essential: testing
nilpotence in the reduced coordinate ring would instead give the vacuous condition warned against
in the ReductiveGroups roadmap.

The predicate is immediately exercised by its basic group-theoretic API. The identity is
unipotent, as are inverses and natural powers of unipotent points. Products are unipotent when the
points commute, and unipotence is invariant under conjugation. These statements follow because
every comodule point action is a group homomorphism and the corresponding closure properties hold
in the general linear group.

## Main declarations

* `TauCeti.HopfAlgebra.IsUnipotent`: a point acts unipotently in every finite-dimensional
  comodule.
* `TauCeti.HopfAlgebra.isUnipotent_iff_isNilpotent_endOfPoint_sub_one`: the equivalent
  nilpotence formulation using the underlying comodule action endomorphisms.
* `TauCeti.HopfAlgebra.IsUnipotent.inv`, `.mul`, and `.pow`: closure under inversion, commuting
  products, and natural powers.
* `TauCeti.HopfAlgebra.isUnipotent_inv_iff`: a point is unipotent exactly when its inverse is.
* `TauCeti.HopfAlgebra.isUnipotent_conj_iff`: invariance under conjugation.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This is the elementwise definition required by Layer 5, "Unipotent groups", of the
ReductiveGroups roadmap. It uses the representation--comodule dictionary built in Layer 1.
-/

public section

open WithConv

namespace TauCeti

namespace HopfAlgebra

universe u v x

variable {k : Type u} {H : Type v} {K : Type x}
variable [Field k] [Semiring H] [_root_.HopfAlgebra k H] [Field K] [Algebra k K]

/-- A field-valued point of a Hopf algebra is unipotent when it acts by a unipotent linear
automorphism on the scalar extension of every finite-dimensional comodule.

When `H` is the commutative coordinate Hopf algebra of an affine group over `k` and `K` is an
algebraic closure, this is the standard representation-theoretic definition of a geometric
unipotent element. -/
def IsUnipotent (g : WithConv (H →ₐ[k] K)) : Prop :=
  ∀ M : FGComoduleCat.{u, v, u} k H,
    GeneralLinearGroup.IsUnipotent
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))

/-- Unfolding the definition of a unipotent point gives unipotence of its action on every finite
comodule. -/
theorem isUnipotent_def (g : WithConv (H →ₐ[k] K)) :
    IsUnipotent g ↔
      ∀ M : FGComoduleCat.{u, v, u} k H,
        GeneralLinearGroup.IsUnipotent
          (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) :=
  Iff.rfl

/-- A point is unipotent exactly when each underlying point-action endomorphism minus the
identity is nilpotent. -/
theorem isUnipotent_iff_isNilpotent_endOfPoint_sub_one (g : WithConv (H →ₐ[k] K)) :
    IsUnipotent g ↔
      ∀ M : FGComoduleCat.{u, v, u} k H,
        _root_.IsNilpotent (Comodule.endOfPoint M g.ofConv - 1) := by
  rw [isUnipotent_def]
  apply forall_congr'
  intro M
  rw [GeneralLinearGroup.isUnipotent_ofLinearEquiv_iff,
    Comodule.pointsAction_toLinearMap]

/-- The identity point is unipotent. -/
@[simp]
theorem isUnipotent_one :
    IsUnipotent (1 : WithConv (H →ₐ[k] K)) := by
  intro M
  rw [map_one]
  exact GeneralLinearGroup.isUnipotent_one

/-- The inverse of a unipotent point is unipotent. -/
theorem IsUnipotent.inv {g : WithConv (H →ₐ[k] K)}
    (hg : IsUnipotent g) : IsUnipotent g⁻¹ := by
  intro M
  have haction :
      LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g⁻¹) =
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))⁻¹ := by
    rw [map_inv, LinearMap.GeneralLinearGroup.ofLinearEquiv_inv]
  rw [haction]
  exact (hg M).inv

/-- A point is unipotent if and only if its inverse is unipotent. -/
@[simp]
theorem isUnipotent_inv_iff (g : WithConv (H →ₐ[k] K)) :
    IsUnipotent g⁻¹ ↔ IsUnipotent g := by
  constructor
  · intro hg
    have := hg.inv
    rwa [inv_inv] at this
  · exact IsUnipotent.inv

/-- The product of two commuting unipotent points is unipotent. -/
theorem IsUnipotent.mul {g h : WithConv (H →ₐ[k] K)}
    (hg : IsUnipotent g) (hh : IsUnipotent h)
    (hcomm : Commute g h) : IsUnipotent (g * h) := by
  intro M
  rw [map_mul, LinearMap.GeneralLinearGroup.ofLinearEquiv_mul]
  apply (hg M).mul (hh M)
  have hactionComm := hcomm.map (Comodule.pointsAction M)
  rw [commute_iff_eq] at hactionComm ⊢
  rw [← LinearMap.GeneralLinearGroup.ofLinearEquiv_mul,
    ← LinearMap.GeneralLinearGroup.ofLinearEquiv_mul, hactionComm]

/-- Every natural power of a unipotent point is unipotent. -/
theorem IsUnipotent.pow {g : WithConv (H →ₐ[k] K)}
    (hg : IsUnipotent g) (n : ℕ) : IsUnipotent (g ^ n) := by
  intro M
  rw [map_pow]
  change GeneralLinearGroup.IsUnipotent
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv K _).symm
      (Comodule.pointsAction M g ^ n))
  rw [map_pow]
  exact (hg M).pow n

/-- Unipotence of points is invariant under conjugation. -/
@[simp]
theorem isUnipotent_conj_iff (g h : WithConv (H →ₐ[k] K)) :
    IsUnipotent (MulAut.conj h g) ↔ IsUnipotent g := by
  constructor
  · intro hg M
    have hM := hg M
    simp only [MulAut.conj_apply, map_mul, map_inv, LinearMap.GeneralLinearGroup.ofLinearEquiv_mul,
      LinearMap.GeneralLinearGroup.ofLinearEquiv_inv] at hM
    exact (GeneralLinearGroup.isUnipotent_conj_iff
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M h))).mp hM
  · intro hg M
    simp only [MulAut.conj_apply, map_mul, map_inv, LinearMap.GeneralLinearGroup.ofLinearEquiv_mul,
      LinearMap.GeneralLinearGroup.ofLinearEquiv_inv]
    exact (GeneralLinearGroup.isUnipotent_conj_iff
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M h))).mpr (hg M)

end HopfAlgebra

end TauCeti
