/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import TauCeti.Algebra.AlgebraicGroup.Product
public import TauCeti.Algebra.AlgebraicGroup.Representation.ScalarExtension
public import TauCeti.LinearAlgebra.JordanChevalley.Functoriality
import TauCeti.LinearAlgebra.GeneralLinearGroup.Intertwining

/-!
# Semisimple points of a Hopf algebra

Let `H` be a Hopf algebra over a commutative semiring `k` and let `K` be a field equipped with a
`k`-algebra structure. A `K`-valued point `g : WithConv (H →ₐ[k] K)` acts on the scalar extension
of every finitely generated `H`-comodule. This file calls `g` **semisimple** when every one of those
linear automorphisms is semisimple. The `WithConv` wrapper supplies the convolution group
structure from the antipode of `H`; all group operations in the closure API below refer to that
convolution law.

For the commutative coordinate Hopf algebra of an affine group scheme, taking `K` to be an
algebraic closure of `k` gives the representation-theoretic definition of a geometric semisimple
element. Semisimple points contain the identity and are closed under inverses and integer powers.
Products of commuting semisimple points are semisimple over a perfect field, and semisimplicity is
invariant under conjugation.

## Main declarations

* `TauCeti.HopfAlgebra.IsSemisimplePoint`: a point acts semisimply in every finitely generated
  comodule.
* `TauCeti.HopfAlgebra.isSemisimplePoint_iff_forall_isSemisimple_endOfPoint`: the equivalent
  formulation using the underlying comodule action endomorphisms.
* `TauCeti.HopfAlgebra.IsSemisimplePoint.inv`, `.mul_of_commute`, and `.zpow`: closure under
  inversion, commuting products, and integer powers.
* `TauCeti.HopfAlgebra.IsSemisimplePoint.mapDomain`: precomposition by a bialgebra morphism
  preserves semisimple points.
* `TauCeti.HopfAlgebra.isSemisimplePoint_mapDomain_iff`: invariance of point semisimplicity under
  bialgebra isomorphisms.
* `TauCeti.HopfAlgebra.isSemisimplePoint_pointsMulEquiv_iff`: over a perfect field, a point of a
  product affine group is semisimple if and only if both component points are semisimple.
* `TauCeti.HopfAlgebra.isSemisimplePoint_conj_iff`: invariance under conjugation.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This supplies the intrinsic semisimple-element predicate needed by Layer 4, "Jordan
decomposition", of the ReductiveGroups roadmap. It uses the representation--comodule dictionary
built in Layer 1.
-/

public section

open LinearMap WithConv
open scoped TensorProduct

namespace TauCeti

namespace HopfAlgebra

universe u v w x

variable {k : Type u} {H : Type v} {K : Type x}
variable [CommSemiring k] [Semiring H] [_root_.HopfAlgebra k H] [Field K] [Algebra k K]

/-- A point `g : WithConv (H →ₐ[k] K)` of a Hopf algebra is semisimple when it acts by a
semisimple linear automorphism on the scalar extension of every finitely generated comodule. The
point type carries the convolution group structure supplied by the antipode of `H`, and the closure
properties below use this group law.

When `H` is the commutative coordinate Hopf algebra of an affine group over `k` and `K` is an
algebraic closure, this is the standard representation-theoretic definition of a geometric
semisimple element. -/
def IsSemisimplePoint (g : WithConv (H →ₐ[k] K)) : Prop :=
  ∀ M : FGComoduleCat.{u, v, u} k H,
    GeneralLinearGroup.IsSemisimple
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))

/-- A point is semisimple exactly when it acts semisimply on each finitely generated comodule. -/
theorem isSemisimplePoint_def (g : WithConv (H →ₐ[k] K)) :
    IsSemisimplePoint g ↔ ∀ M : FGComoduleCat.{u, v, u} k H,
      GeneralLinearGroup.IsSemisimple
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) :=
  Iff.rfl

section MapDomain

variable {H₁ : Type v} {H₂ : Type w}
variable [Semiring H₁] [Semiring H₂]
variable [_root_.HopfAlgebra k H₁] [_root_.HopfAlgebra k H₂]

/-- Precomposition by a bialgebra morphism preserves semisimple points. For commutative coordinate
Hopf algebras, this says that a homomorphism of affine groups sends semisimple points to semisimple
points. -/
theorem IsSemisimplePoint.mapDomain {g : WithConv (H₂ →ₐ[k] K)}
    (hg : IsSemisimplePoint g) (φ : H₁ →ₐc[k] H₂) :
    IsSemisimplePoint (AlgHom.mapDomain φ g) := by
  rw [isSemisimplePoint_def] at hg ⊢
  intro M
  rw [← Comodule.pointsAction_corestrict_obj φ M g]
  exact hg ((FGComoduleCat.corestrict φ.toCoalgHom).obj M)

/-- Semisimplicity of points is invariant under precomposition by a bialgebra isomorphism. -/
theorem isSemisimplePoint_mapDomain_iff
    (e : H₁ ≃ₐc[k] H₂) (g : WithConv (H₂ →ₐ[k] K)) :
    IsSemisimplePoint (AlgHom.mapDomain (e : H₁ →ₐc[k] H₂) g) ↔ IsSemisimplePoint g := by
  constructor
  · intro hg
    have h := hg.mapDomain (e.symm : H₂ →ₐc[k] H₁)
    have he : AlgHom.mapDomain (e.symm : H₂ →ₐc[k] H₁)
        (AlgHom.mapDomain (e : H₁ →ₐc[k] H₂) g) = g := by
      rw [← AlgHom.mapDomainMulEquiv_symm_apply e, ← AlgHom.mapDomainMulEquiv_apply e]
      exact (AlgHom.mapDomainMulEquiv (A := K) e).left_inv g
    rwa [he] at h
  · intro hg
    exact hg.mapDomain (e : H₁ →ₐc[k] H₂)

end MapDomain

private theorem isSemisimple_pointAction_iff_endOfPoint
    (g : WithConv (H →ₐ[k] K)) (M : FGComoduleCat.{u, v, u} k H) :
    GeneralLinearGroup.IsSemisimple
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) ↔
      Module.End.IsSemisimple (Comodule.endOfPoint M g.ofConv) := by
  rw [GeneralLinearGroup.isSemisimple_def]
  rw [← LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap]
  have haction :
      LinearMap.GeneralLinearGroup.generalLinearEquiv K _
          (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) =
        Comodule.pointsAction M g :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K _).apply_symm_apply _
  rw [haction]
  simp only [Comodule.pointsAction_toLinearMap]

/-- A point is semisimple exactly when each underlying point-action endomorphism is
semisimple. -/
theorem isSemisimplePoint_iff_forall_isSemisimple_endOfPoint
    (g : WithConv (H →ₐ[k] K)) :
    IsSemisimplePoint g ↔
      ∀ M : FGComoduleCat.{u, v, u} k H,
        Module.End.IsSemisimple (Comodule.endOfPoint M g.ofConv) := by
  constructor
  · intro h M
    exact (isSemisimple_pointAction_iff_endOfPoint g M).mp (h M)
  · intro h M
    exact (isSemisimple_pointAction_iff_endOfPoint g M).mpr (h M)

/-- The identity point is semisimple. -/
@[simp]
theorem isSemisimplePoint_one :
    IsSemisimplePoint (1 : WithConv (H →ₐ[k] K)) := by
  intro M
  rw [map_one]
  exact GeneralLinearGroup.isSemisimple_one

/-- The inverse of a semisimple point is semisimple. -/
theorem IsSemisimplePoint.inv {g : WithConv (H →ₐ[k] K)}
    (hg : IsSemisimplePoint g) : IsSemisimplePoint g⁻¹ := by
  intro M
  have haction :
      LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g⁻¹) =
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))⁻¹ := by
    rw [map_inv, LinearMap.GeneralLinearGroup.ofLinearEquiv_inv]
  rw [haction]
  exact (hg M).inv

/-- A point is semisimple if and only if its inverse is semisimple. -/
@[simp]
theorem isSemisimplePoint_inv_iff (g : WithConv (H →ₐ[k] K)) :
    IsSemisimplePoint g⁻¹ ↔ IsSemisimplePoint g := by
  constructor
  · intro hg
    have := hg.inv
    rwa [inv_inv] at this
  · exact IsSemisimplePoint.inv

/-- Every natural power of a semisimple point is semisimple. -/
theorem IsSemisimplePoint.pow {g : WithConv (H →ₐ[k] K)}
    (hg : IsSemisimplePoint g) (n : ℕ) : IsSemisimplePoint (g ^ n) := by
  intro M
  rw [map_pow]
  have hpow :
      LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g ^ n) =
        LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g) ^ n :=
    map_pow (LinearMap.GeneralLinearGroup.generalLinearEquiv K _).symm.toMonoidHom _ n
  rw [hpow]
  exact (hg M).pow n

/-- Every integer power of a semisimple point is semisimple. -/
theorem IsSemisimplePoint.zpow {g : WithConv (H →ₐ[k] K)}
    (hg : IsSemisimplePoint g) (n : ℤ) : IsSemisimplePoint (g ^ n) := by
  cases n with
  | ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hg.pow n
  | negSucc n => simpa only [zpow_negSucc] using (hg.pow n.succ).inv

/-- Semisimplicity of points is invariant under conjugation. -/
@[simp]
theorem isSemisimplePoint_conj_iff (g h : WithConv (H →ₐ[k] K)) :
    IsSemisimplePoint (h * g * h⁻¹) ↔ IsSemisimplePoint g := by
  unfold IsSemisimplePoint
  simp only [map_mul, map_inv,
    LinearMap.GeneralLinearGroup.ofLinearEquiv_mul,
    LinearMap.GeneralLinearGroup.ofLinearEquiv_inv,
    GeneralLinearGroup.isSemisimple_conj_iff]

section PerfectField

variable [PerfectField K]

/-- The product of two commuting semisimple points is semisimple. -/
theorem IsSemisimplePoint.mul_of_commute {g h : WithConv (H →ₐ[k] K)}
    (hg : IsSemisimplePoint g) (hh : IsSemisimplePoint h)
    (hcomm : Commute g h) : IsSemisimplePoint (g * h) := by
  intro M
  rw [map_mul, LinearMap.GeneralLinearGroup.ofLinearEquiv_mul]
  apply (hg M).mul_of_commute (hh M)
  exact (LinearMap.GeneralLinearGroup.commute_ofLinearEquiv_iff _ _).2
    (hcomm.map (Comodule.pointsAction M))

end PerfectField

section Product

variable {H₁ H₂ : Type v} [CommSemiring H₁] [CommSemiring H₂]
variable [_root_.HopfAlgebra k H₁] [_root_.HopfAlgebra k H₂] [PerfectField K]

/-- Over a perfect field, a point of a product affine group is semisimple exactly when both factor
points are semisimple. -/
@[simp]
theorem isSemisimplePoint_pointsMulEquiv_iff
    (g : WithConv ((H₁ ⊗[k] H₂) →ₐ[k] K)) :
    IsSemisimplePoint g ↔
      IsSemisimplePoint (AffineGroup.Product.pointsMulEquiv g).1 ∧
        IsSemisimplePoint (AffineGroup.Product.pointsMulEquiv g).2 := by
  constructor
  · intro hg
    exact ⟨hg.mapDomain Bialgebra.TensorProduct.includeLeft,
      hg.mapDomain Bialgebra.TensorProduct.includeRight⟩
  · rintro ⟨hleft, hright⟩
    let e := AffineGroup.Product.pointsMulEquiv
      (R := k) (H₁ := H₁) (H₂ := H₂) (A := K)
    let gleft := e.symm ((e g).1, 1)
    let gright := e.symm (1, (e g).2)
    have hgleft : IsSemisimplePoint gleft := by
      have h := hleft.mapDomain (Bialgebra.TensorProduct.projectLeft
        (R := k) (H₁ := H₁) (H₂ := H₂))
      simpa only [AlgHom.mapDomain_apply, gleft, e,
        AffineGroup.Product.mapDomain_projectLeft] using h
    have hgright : IsSemisimplePoint gright := by
      have h := hright.mapDomain (Bialgebra.TensorProduct.projectRight
        (R := k) (H₁ := H₁) (H₂ := H₂))
      simpa only [AlgHom.mapDomain_apply, gright, e,
        AffineGroup.Product.mapDomain_projectRight] using h
    have hfactor : g = gleft * gright := by
      simpa only [e, gleft, gright, map_mul, MulEquiv.symm_apply_apply] using
        congrArg e.symm (Prod.fst_mul_snd (e g)).symm
    rw [hfactor]
    exact hgleft.mul_of_commute hgright <| (MonoidHom.commute_inl_inr _ _).map e.symm

end Product

end HopfAlgebra

end TauCeti
