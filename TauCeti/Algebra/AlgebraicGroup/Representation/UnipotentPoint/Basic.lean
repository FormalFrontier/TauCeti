/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction
public import TauCeti.LinearAlgebra.GeneralLinearGroup.Unipotent
import TauCeti.LinearAlgebra.GeneralLinearGroup.Intertwining

/-!
# Unipotent points of an affine group

Let `H` be a Hopf algebra over a commutative semiring `k` and let `K` be a commutative
`k`-algebra. A
`K`-valued point `g : H →ₐ[k] K` acts on the scalar extension of every finitely generated
`H`-comodule. Over a field, these are the finite-dimensional representations relevant to the
geometric definition. This file calls `g` **unipotent** when every one of those linear
automorphisms is unipotent, meaning that its difference from the identity is nilpotent.

For the commutative coordinate Hopf algebra of an affine group scheme, taking `K` to be an
algebraic closure of `k` is precisely the representation-theoretic definition of a geometric
unipotent element. The quantification over all finitely generated comodules is essential: testing
nilpotence in the reduced coordinate ring would instead give the vacuous condition warned against
in the ReductiveGroups roadmap.

The predicate is immediately exercised by its basic group-theoretic API. The identity is
unipotent, as are inverses and natural or integer powers of unipotent points. Products are
unipotent when the points commute, and unipotence is invariant under conjugation. These statements
follow because every comodule point action is a group homomorphism and the corresponding closure
properties hold in the general linear group. Unipotence is also preserved by precomposition along
bialgebra morphisms, and hence invariant under bialgebra isomorphisms.

## Main declarations

* `TauCeti.HopfAlgebra.IsUnipotentPoint`: a point acts unipotently in every finitely generated
  comodule.
* `TauCeti.HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one`: the equivalent
  nilpotence formulation using the underlying comodule action endomorphisms.
* `TauCeti.HopfAlgebra.IsUnipotentPoint.inv`, `.mul_of_commute`, `.pow`, and `.zpow`: closure under
  inversion, commuting products, and natural or integer powers.
* `TauCeti.HopfAlgebra.isUnipotentPoint_inv_iff`: a point is unipotent exactly when its inverse is.
* `TauCeti.HopfAlgebra.isUnipotentPoint_conj_iff`: invariance under conjugation.
* `TauCeti.HopfAlgebra.IsUnipotentPoint.mapDomain`: functoriality under precomposition by a
  bialgebra morphism.
* `TauCeti.HopfAlgebra.isUnipotentPoint_mapDomain_iff`: invariance under a bialgebra
  isomorphism of the coordinate algebra.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This is the elementwise definition required by Layer 5, "Unipotent groups", of the
ReductiveGroups roadmap. It uses the representation--comodule dictionary built in Layer 1.
-/

public section

open LinearMap WithConv

namespace TauCeti

namespace HopfAlgebra

universe u v w x

variable {k : Type u} {H : Type v} {K : Type x}
variable [CommSemiring k] [Semiring H] [_root_.HopfAlgebra k H] [CommRing K] [Algebra k K]

/-- A point of a Hopf algebra valued in a commutative algebra is unipotent when it acts by a
unipotent linear automorphism on the scalar extension of every finitely generated comodule.

When `k` is a field, these comodules are the finite-dimensional representations. Thus, when `H`
is the commutative coordinate Hopf algebra of an affine group over `k` and `K` is an algebraic
closure, this is the standard representation-theoretic definition of a geometric unipotent
element. -/
def IsUnipotentPoint (g : WithConv (H →ₐ[k] K)) : Prop :=
  ∀ M : FGComoduleCat.{u, v, u} k H,
    GeneralLinearGroup.IsUnipotent
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))

/-- Unfolding the definition of a unipotent point gives unipotence of its action on every finite
comodule. -/
theorem isUnipotentPoint_def (g : WithConv (H →ₐ[k] K)) :
    IsUnipotentPoint g ↔
      ∀ M : FGComoduleCat.{u, v, u} k H,
        GeneralLinearGroup.IsUnipotent
          (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) :=
  Iff.rfl

/-- A point is unipotent exactly when each underlying point-action endomorphism minus the
identity is nilpotent. -/
theorem isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one
    (g : WithConv (H →ₐ[k] K)) :
    IsUnipotentPoint g ↔
      ∀ M : FGComoduleCat.{u, v, u} k H,
        _root_.IsNilpotent (Comodule.endOfPoint M g.ofConv - 1) := by
  rw [isUnipotentPoint_def]
  apply forall_congr'
  intro M
  rw [GeneralLinearGroup.isUnipotent_ofLinearEquiv_iff,
    Comodule.pointsAction_toLinearMap]

/-- Precomposing a unipotent point with a bialgebra morphism gives a unipotent point. -/
theorem IsUnipotentPoint.mapDomain {H' : Type w} [Semiring H'] [_root_.HopfAlgebra k H']
    {g : WithConv (H' →ₐ[k] K)} (hg : IsUnipotentPoint g) (f : H →ₐc[k] H') :
    IsUnipotentPoint (AlgHom.mapDomain f g) := by
  rw [isUnipotentPoint_def] at hg ⊢
  intro M
  rw [← Comodule.pointsAction_corestrict_obj f M g]
  exact hg ((FGComoduleCat.corestrict f.toCoalgHom).obj M)

/-- Unipotence of a point is invariant under precomposition by a bialgebra isomorphism. -/
theorem isUnipotentPoint_mapDomain_iff {H' : Type w} [Semiring H']
    [_root_.HopfAlgebra k H'] (e : H ≃ₐc[k] H') (g : WithConv (H' →ₐ[k] K)) :
    IsUnipotentPoint (AlgHom.mapDomain (e : H →ₐc[k] H') g) ↔ IsUnipotentPoint g := by
  constructor
  · intro hg
    have h := hg.mapDomain (e.symm : H' →ₐc[k] H)
    rw [← AlgHom.mapDomainMulEquiv_symm_apply e,
      ← AlgHom.mapDomainMulEquiv_apply e] at h
    simpa only [MulEquiv.symm_apply_apply] using h
  · intro hg
    exact hg.mapDomain (e : H →ₐc[k] H')

/-- The identity point is unipotent. -/
@[simp]
theorem isUnipotentPoint_one :
    IsUnipotentPoint (1 : WithConv (H →ₐ[k] K)) := by
  intro M
  rw [map_one]
  exact GeneralLinearGroup.isUnipotent_one

/-- The inverse of a unipotent point is unipotent. -/
theorem IsUnipotentPoint.inv {g : WithConv (H →ₐ[k] K)}
    (hg : IsUnipotentPoint g) : IsUnipotentPoint g⁻¹ := by
  intro M
  have haction :
      LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g⁻¹) =
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))⁻¹ := by
    rw [map_inv, LinearMap.GeneralLinearGroup.ofLinearEquiv_inv]
  rw [haction]
  exact (hg M).inv

/-- A point is unipotent if and only if its inverse is unipotent. -/
@[simp]
theorem isUnipotentPoint_inv_iff (g : WithConv (H →ₐ[k] K)) :
    IsUnipotentPoint g⁻¹ ↔ IsUnipotentPoint g := by
  constructor
  · intro hg
    have := hg.inv
    rwa [inv_inv] at this
  · exact IsUnipotentPoint.inv

/-- The product of two commuting unipotent points is unipotent. -/
theorem IsUnipotentPoint.mul_of_commute {g h : WithConv (H →ₐ[k] K)}
    (hg : IsUnipotentPoint g) (hh : IsUnipotentPoint h)
    (hcomm : Commute g h) : IsUnipotentPoint (g * h) := by
  intro M
  rw [map_mul, LinearMap.GeneralLinearGroup.ofLinearEquiv_mul]
  apply (hg M).mul_of_commute (hh M)
  exact (LinearMap.GeneralLinearGroup.commute_ofLinearEquiv_iff _ _).2
    (hcomm.map (Comodule.pointsAction M))

/-- Every natural power of a unipotent point is unipotent. -/
theorem IsUnipotentPoint.pow {g : WithConv (H →ₐ[k] K)}
    (hg : IsUnipotentPoint g) (n : ℕ) : IsUnipotentPoint (g ^ n) := by
  intro M
  rw [map_pow]
  -- `ofLinearEquiv` has no power lemma, so expose it as the inverse of the multiplicative
  -- equivalence between units and linear equivalences; `map_pow` then applies directly.
  change GeneralLinearGroup.IsUnipotent
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv K _).symm
      (Comodule.pointsAction M g ^ n))
  rw [map_pow]
  exact (hg M).pow n

/-- Every integer power of a unipotent point is unipotent. -/
theorem IsUnipotentPoint.zpow {g : WithConv (H →ₐ[k] K)}
    (hg : IsUnipotentPoint g) (n : ℤ) : IsUnipotentPoint (g ^ n) := by
  cases n with
  | ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hg.pow n
  | negSucc n => simpa only [zpow_negSucc] using (hg.pow n.succ).inv

/-- Unipotence of points is invariant under conjugation. -/
@[simp]
theorem isUnipotentPoint_conj_iff (g h : WithConv (H →ₐ[k] K)) :
    IsUnipotentPoint (h * g * h⁻¹) ↔ IsUnipotentPoint g := by
  constructor
  · intro hg M
    have hM := hg M
    simp only [map_mul, map_inv, LinearMap.GeneralLinearGroup.ofLinearEquiv_mul,
      LinearMap.GeneralLinearGroup.ofLinearEquiv_inv] at hM
    exact (GeneralLinearGroup.isUnipotent_conj_iff
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M h))).mp hM
  · intro hg M
    simp only [map_mul, map_inv, LinearMap.GeneralLinearGroup.ofLinearEquiv_mul,
      LinearMap.GeneralLinearGroup.ofLinearEquiv_inv]
    exact (GeneralLinearGroup.isUnipotent_conj_iff
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M h))).mpr (hg M)

end HopfAlgebra

end TauCeti
