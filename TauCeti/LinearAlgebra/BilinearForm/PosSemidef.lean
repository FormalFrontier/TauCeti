/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Positive-semidefinite bilinear forms

This file records a pointwise characterization of positive semidefiniteness for symmetric
bilinear forms. It converts `IsPosSemidef` into diagonal nonnegativity, the form consumed by
quadratic-form signature criteria and other pointwise positivity arguments.

## Main results

* `LinearMap.BilinForm.isPosSemidef_iff_forall_nonneg`: a symmetric bilinear form is
  positive-semidefinite exactly when its diagonal values are nonnegative.
-/

public section

namespace LinearMap.BilinForm

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [LE R]

/-- A symmetric bilinear form is positive-semidefinite if and only if its values on all vectors
are nonnegative. -/
@[grind =]
theorem isPosSemidef_iff_forall_nonneg (B : LinearMap.BilinForm R M) (hB : B.IsSymm) :
    B.IsPosSemidef ↔ ∀ x, 0 ≤ B x x := by
  rw [LinearMap.BilinForm.isPosSemidef_def, LinearMap.BilinForm.isNonneg_def]
  simp only [hB, true_and]

end LinearMap.BilinForm
