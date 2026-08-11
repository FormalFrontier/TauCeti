/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.Tactic.Module

/-!
# Scalar shifts of partial linear maps

For a partial linear map `A`, subtracting the scalar operator `omega I` leaves its domain
unchanged.  This file develops the generic construction and its basic normalization API.

## Main results

* `TauCeti.LinearPMap.subScalar`: the operator `A - omega I` on the domain of `A`.
* `TauCeti.LinearPMap.subScalar_domain`: scalar shifts preserve the domain.
* `TauCeti.LinearPMap.subScalar_apply`: pointwise evaluation of a scalar shift.
-/

public section

namespace TauCeti.LinearPMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Subtract the scalar operator `omega I` from an unbounded operator `A`, without changing its
domain. -/
def subScalar (A : X →ₗ.[ℝ] X) (omega : ℝ) : X →ₗ.[ℝ] X :=
  (-omega • (LinearMap.id : X →ₗ[ℝ] X)) +ᵥ A

/-- A scalar shift does not change the domain of an unbounded operator. -/
@[simp]
theorem subScalar_domain (A : X →ₗ.[ℝ] X) (omega : ℝ) :
    (subScalar A omega).domain = A.domain := by
  exact LinearPMap.vadd_domain _ _

/-- Pointwise evaluation of the shifted operator `A - omega I`. -/
@[simp]
theorem subScalar_apply (A : X →ₗ.[ℝ] X) (omega : ℝ) (x : (subScalar A omega).domain) :
    subScalar A omega x = A ⟨x, by simpa using x.property⟩ - omega • (x : X) := by
  change (-omega) • (x : X) + A x = A x - omega • (x : X)
  module

/-- The zero scalar shift is the original operator. -/
@[simp]
theorem subScalar_zero (A : X →ₗ.[ℝ] X) : subScalar A 0 = A := by
  simp [subScalar]

/-- Successive scalar shifts add their parameters. -/
@[simp]
theorem subScalar_subScalar (A : X →ₗ.[ℝ] X) (omega mu : ℝ) :
    subScalar (subScalar A omega) mu = subScalar A (omega + mu) := by
  apply LinearPMap.ext (by simp)
  intro x hx hy
  simp only [subScalar_apply]
  module

end TauCeti.LinearPMap

end
