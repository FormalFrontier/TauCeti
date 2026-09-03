/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Rat
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Base change of a rational vector space along `ℤ → ℚ`

A `ℚ`-vector space is already its own extension of scalars from `ℤ` to `ℚ`: any additive map out
of it into a `ℚ`-module is automatically `ℚ`-linear, which is exactly the universal property
`IsBaseChange` asks for. Consequently, for a `ℚ`-algebra `A`, the concrete tensor product
`A ⊗[ℚ] U` is a base change of `U` along `ℤ → A`, not merely along `ℚ → A`.

This is what allows a `ℚ`-vector space to be fed to constructions that take an integral module
together with an abstract model of its complexification, such as the conjugation and the pure
Hodge structures of `TauCeti/Geometry/Hodge/`.

## Main results

* `TauCeti.isBaseChange_rat_id`: the identity of a `ℚ`-vector space, viewed as `ℤ`-linear,
  exhibits it as its own rationalification.
* `TauCeti.isBaseChange_ratTensorMap`: for a `ℚ`-algebra `A`, the map `u ↦ 1 ⊗ₜ u` exhibits
  `A ⊗[ℚ] U` as the base change of `U` along `ℤ → A`.
-/

public section

namespace TauCeti

open scoped TensorProduct

universe u v

/-- A `ℚ`-vector space is its own rationalification: the identity map, viewed as a map of
`ℤ`-modules, exhibits `U` as the extension of scalars of `U` along `ℤ → ℚ`. -/
theorem isBaseChange_rat_id (U : Type u) [AddCommGroup U] [Module ℚ U] :
    IsBaseChange ℚ ((LinearMap.id : U →ₗ[ℚ] U).restrictScalars ℤ) := by
  refine IsBaseChange.of_lift_unique _ fun Q _ _ _ _ g ↦ ?_
  -- A `ℚ`-module is automatically an additive group, which `AddMonoidHom.toRatLinearMap` needs.
  let _ : AddCommGroup Q := Module.addCommMonoidToAddCommGroup ℚ
  refine ⟨g.toAddMonoidHom.toRatLinearMap, ?_, fun g' hg' ↦ ?_⟩
  · ext x
    rfl
  · ext x
    exact congrFun (congrArg (fun h : U →ₗ[ℤ] Q ↦ (h : U → Q)) hg') x

variable (A : Type v) [CommRing A] [Algebra ℚ A]
variable (U : Type u) [AddCommGroup U] [Module ℚ U]

/-- The canonical map of a rational vector space into its scalar extension `A ⊗[ℚ] U`, viewed as
a map of `ℤ`-modules. -/
def ratTensorMap : U →ₗ[ℤ] A ⊗[ℚ] U :=
  ((TensorProduct.mk ℚ A U 1).restrictScalars ℤ).comp
    ((LinearMap.id : U →ₗ[ℚ] U).restrictScalars ℤ)

@[simp]
theorem ratTensorMap_apply (u : U) : ratTensorMap A U u = 1 ⊗ₜ[ℚ] u := (rfl)

/-- For a `ℚ`-algebra `A`, the tensor product `A ⊗[ℚ] U` of a rational vector space is a base
change of `U` along `ℤ → A`, and not only along `ℚ → A`. -/
theorem isBaseChange_ratTensorMap : IsBaseChange A (ratTensorMap A U) :=
  (isBaseChange_rat_id U).comp (TensorProduct.isBaseChange ℚ U A)

end TauCeti
