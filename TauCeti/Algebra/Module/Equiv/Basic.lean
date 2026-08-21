/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Evaluating multiplication by a unit of the base ring

Mathlib's `LinearEquiv.smulOfUnit` packages multiplication by a unit `u` of the base ring as a
linear equivalence, but records no lemma evaluating it at a vector. This file supplies that
evaluation lemma, in the `simp`-normal form that rewrites an application of
`LinearEquiv.smulOfUnit` to a scalar multiplication.

## Main results

* `LinearEquiv.smulOfUnit_apply`: `LinearEquiv.smulOfUnit u` acts as multiplication by `u`.
-/

public section

namespace LinearEquiv

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Multiplication by a unit of the base ring, evaluated: `LinearEquiv.smulOfUnit u` sends `x` to
`u • x`. -/
@[simp]
theorem smulOfUnit_apply (u : Rˣ) (x : M) : (smulOfUnit u : M ≃ₗ[R] M) x = (u : R) • x :=
  (rfl)

end LinearEquiv
