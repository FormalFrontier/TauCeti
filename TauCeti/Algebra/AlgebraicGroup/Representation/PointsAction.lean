/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.Coalgebra.Comodule.Corestrict
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
* `TauCeti.Comodule.endOfPoint_corestrict` and
  `TauCeti.Comodule.pointsAction_corestrict`: compatibility of point actions with
  corestriction and precomposition.
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

universe u v w x

section Corestrict

variable {R : Type u} {H₁ : Type v} {H₂ : Type w} {A : Type x}
variable [CommSemiring R] [Semiring H₁] [Semiring H₂]
variable [CommSemiring A] [Algebra R A]

section Bialgebra

variable [Bialgebra R H₁] [Bialgebra R H₂]
variable {V : Type*} [AddCommMonoid V] [Module R V] [Comodule R H₁ V]

/-- Acting on a comodule by a point precomposed with a bialgebra morphism is the same as
corestricting the comodule along that morphism and acting by the original point. -/
theorem endOfPoint_corestrict (φ : H₁ →ₐc[R] H₂)
    (g : WithConv (H₂ →ₐ[R] A)) :
    (letI : Comodule R H₂ V := Corestrict φ.toCoalgHom
     endOfPoint V g.ofConv) = endOfPoint V (AlgHom.mapDomain φ g).ofConv := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a v
  rw [endOfPoint_tmul, endOfPoint_tmul]
  simp only [corestrict_coact_apply, AlgHom.mapDomain_apply,
    AlgHom.comp_toLinearMap]
  rw [LinearMap.lTensor_comp, LinearMap.comp_apply]
  rfl

end Bialgebra

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
      (endOfPoint_corestrict φ g).trans <|
        (pointsAction_toLinearMap V (AlgHom.mapDomain φ g)).symm

end HopfAlgebra

end Corestrict

end Comodule

end TauCeti
