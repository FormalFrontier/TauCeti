/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Corestrict
public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# The points action of a comodule, by automorphisms

Over a Hopf algebra the points form a group under convolution — the points of the
corresponding affine group scheme, when `H` is commutative — so the points action of
a comodule (`TauCeti.Comodule.endOfPoint`,
`TauCeti.Comodule.pointsRepresentation`) lands in the units of the endomorphism
monoid: the action upgrades to linear automorphisms of the scalar extension via
`Representation.asGroupHom`, with inverses provided by the group structure rather
than by an antipode computation.

## Main declarations

* `TauCeti.Comodule.pointsAction`: the action of the group of points by linear
  automorphisms of `A ⊗[R] V`.
* `TauCeti.Comodule.pointsAction_corestrict`: compatibility of point actions with
  corestriction and precomposition, also provided for bundled finite comodules by
  `TauCeti.Comodule.pointsAction_corestrict_obj`.
-/

public section

namespace TauCeti

namespace Comodule

open _root_.Coalgebra WithConv TensorProduct

variable {R H V A : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]
  [AddCommMonoid V] [Module R V] [Comodule R H V]
  [CommSemiring A] [Algebra R A]

variable (V) in
/-- Over a Hopf algebra the points act by linear automorphisms of the scalar
extension: the group of points lands in the units of the endomorphism monoid, with
inverses provided by the group structure rather than by an antipode computation. -/
noncomputable def pointsAction :
    WithConv (H →ₐ[R] A) →* ((A ⊗[R] V) ≃ₗ[A] (A ⊗[R] V)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[R] V)).toMonoidHom.comp
    (pointsRepresentation V).asGroupHom

variable (V) in
@[simp]
lemma pointsAction_toLinearMap (g : WithConv (H →ₐ[R] A)) :
    (pointsAction V g : A ⊗[R] V →ₗ[A] A ⊗[R] V) = endOfPoint V g.ofConv := by
  -- `pointsAction` has no equation lemma to rewrite with; `change` spells out its
  -- definitional unfolding once, explicitly.
  change ((LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[R] V))
    ((pointsRepresentation V).asGroupHom g) : A ⊗[R] V →ₗ[A] A ⊗[R] V) = _
  rw [LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
    Representation.asGroupHom_apply, pointsRepresentation_apply]

universe u v w x y

section Corestrict

variable {R : Type u} {H₁ : Type v} {H₂ : Type w} {A : Type x}
variable [CommSemiring R] [Semiring H₁] [Semiring H₂]
variable [CommSemiring A] [Algebra R A]

section HopfAlgebra

variable [HopfAlgebra R H₁] [HopfAlgebra R H₂]
variable {V : Type*} [AddCommMonoid V] [Module R V] [Comodule R H₁ V]

/-- The linear action of a precomposed point agrees with the action of the original point on
the corestricted comodule. -/
theorem pointsAction_corestrict (φ : H₁ →ₐc[R] H₂)
    (g : WithConv (H₂ →ₐ[R] A)) :
    (letI : Comodule R H₂ V := Corestrict φ.toCoalgHom
     pointsAction V g) = pointsAction V (AlgHom.mapDomain φ g) := by
  let : Comodule R H₂ V := Corestrict φ.toCoalgHom
  apply LinearEquiv.ext
  exact LinearMap.congr_fun <|
    (pointsAction_toLinearMap V g).trans <|
      (endOfPoint_corestrict φ g.ofConv).trans <|
        (by
          rw [AlgHom.mapDomain_apply, ofConv_toConv]
          exact (pointsAction_toLinearMap V
            (toConv (g.ofConv.comp (φ : H₁ →ₐ[R] H₂)))).symm)

/-- Simp-normal form of `pointsAction_corestrict`, with the precomposed point written
after normalization by `AlgHom.mapDomain_apply`. -/
@[simp]
theorem pointsAction_corestrict_toConv_comp (φ : H₁ →ₐc[R] H₂)
    (g : WithConv (H₂ →ₐ[R] A)) :
    (letI : Comodule R H₂ V := Corestrict φ.toCoalgHom
     pointsAction V g) =
      pointsAction V (toConv (g.ofConv.comp (φ : H₁ →ₐ[R] H₂))) := by
  simpa only [AlgHom.mapDomain_apply] using pointsAction_corestrict φ g

/-- Bundled finite-comodule form of `pointsAction_corestrict`. This avoids exposing the
definitionally equal comodule instance carried by the corestricted object to callers. -/
theorem pointsAction_corestrict_obj (φ : H₁ →ₐc[R] H₂)
    (M : FGComoduleCat.{u, v, y} R H₁) (g : WithConv (H₂ →ₐ[R] A)) :
    pointsAction ((FGComoduleCat.corestrict φ.toCoalgHom).obj M) g =
      pointsAction M (AlgHom.mapDomain φ g) := by
  -- The bundled object's comodule instance is definitionally `Corestrict`; expose that
  -- identification once here so downstream proofs can rewrite by a named theorem.
  change (letI : Comodule R H₂ M := Corestrict φ.toCoalgHom
    pointsAction M g) = pointsAction M (AlgHom.mapDomain φ g)
  exact pointsAction_corestrict φ g

/-- Simp-normal form of `pointsAction_corestrict_obj`, with the precomposed point written
after normalization by `AlgHom.mapDomain_apply`. -/
-- Prefer this bundled normal form before `corestrict_obj_coe` exposes the carrier.
@[simp↓ high]
theorem pointsAction_corestrict_obj_toConv_comp (φ : H₁ →ₐc[R] H₂)
    (M : FGComoduleCat.{u, v, y} R H₁) (g : WithConv (H₂ →ₐ[R] A)) :
    pointsAction ((FGComoduleCat.corestrict φ.toCoalgHom).obj M) g =
      pointsAction M (toConv (g.ofConv.comp (φ : H₁ →ₐ[R] H₂))) := by
  simpa only [AlgHom.mapDomain_apply] using pointsAction_corestrict_obj φ M g

end HopfAlgebra

end Corestrict

end Comodule

end TauCeti
