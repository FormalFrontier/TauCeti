/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
* `TauCeti.LinearPMap.vadd_subScalar` and `TauCeti.LinearPMap.subScalar_vadd`: scalar shifts
  commute with adding a globally defined map, and absorb into it.
-/

public section

namespace TauCeti.LinearPMap

variable {R X : Type*} [CommRing R] [AddCommGroup X] [Module R X]

/-- Subtract the scalar operator `omega I` from an unbounded operator `A`, without changing its
domain. -/
def subScalar (A : X →ₗ.[R] X) (omega : R) : X →ₗ.[R] X :=
  (-omega • (LinearMap.id : X →ₗ[R] X)) +ᵥ A

/-- A scalar shift does not change the domain of an unbounded operator. -/
@[simp]
theorem subScalar_domain (A : X →ₗ.[R] X) (omega : R) :
    (subScalar A omega).domain = A.domain := by
  exact LinearPMap.vadd_domain _ _

/-- Pointwise evaluation of the shifted operator `A - omega I`. -/
@[simp]
theorem subScalar_apply (A : X →ₗ.[R] X) (omega : R) (x : (subScalar A omega).domain) :
    subScalar A omega x =
      A ⟨x, (subScalar_domain A omega) ▸ x.2⟩ - omega • (x : X) := by
  -- Unfold the domain-preserving `VAdd` so both sides use its definitionally equal subtype.
  change (-omega) • (x : X) + A x = A x - omega • (x : X)
  module

/-- The zero scalar shift is the original operator. -/
@[simp]
theorem subScalar_zero (A : X →ₗ.[R] X) : subScalar A 0 = A := by
  simp [subScalar]

/-- Successive scalar shifts add their parameters. -/
@[simp]
theorem subScalar_subScalar (A : X →ₗ.[R] X) (omega mu : R) :
    subScalar (subScalar A omega) mu = subScalar A (omega + mu) := by
  apply LinearPMap.ext (by simp)
  intro x hx hy
  simp only [subScalar_apply]
  module

/-- A globally defined linear summand and a scalar shift commute: adding the map to `A` and then
subtracting `omega I` gives the same operator either way round. -/
@[simp]
theorem vadd_subScalar {A : X →ₗ.[R] X} (f : X →ₗ[R] X) (omega : R) :
    f +ᵥ subScalar A omega = subScalar (f +ᵥ A) omega := by
  refine LinearPMap.ext rfl fun x hf hg => ?_
  rw [LinearPMap.vadd_apply, subScalar_apply, subScalar_apply, LinearPMap.vadd_apply]
  module

/-- A scalar shift of a globally defined linear perturbation absorbs into the perturbing map.
This is the form in which the domain of a shifted perturbation is visibly the domain of `A`. -/
@[simp]
theorem subScalar_vadd {A : X →ₗ.[R] X} (f : X →ₗ[R] X) (omega : R) :
    subScalar (f +ᵥ A) omega = (f - omega • LinearMap.id) +ᵥ A := by
  refine LinearPMap.ext rfl fun x hf hg => ?_
  rw [subScalar_apply, LinearPMap.vadd_apply, LinearPMap.vadd_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply]
  module

end TauCeti.LinearPMap

end
