/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
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
-/

public section

namespace TauCeti

namespace Comodule

open Coalgebra WithConv TensorProduct

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

end Comodule

end TauCeti
