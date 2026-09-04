/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Positive-semidefinite bilinear forms

This file records a pointwise characterization of positive semidefiniteness for symmetric
bilinear forms. It converts `IsPosSemidef` into diagonal nonnegativity, the form consumed by
quadratic-form signature criteria and other pointwise positivity arguments.

## Main results

* `LinearMap.BilinForm.isPosSemidef_iff_forall_nonneg`: a symmetric bilinear form is
  positive-semidefinite exactly when its diagonal values are nonnegative.
* `LinearMap.BilinForm.IsPosSemidef.sq_apply_le_mul_apply_self`: the Cauchy--Schwarz inequality
  `B u v ^ 2 ≤ B u u * B v v` for a positive-semidefinite form over a linearly ordered field.
  The form need not be definite, so this covers the energy form of a merely coercive variational
  problem as well as an inner product.
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

section LinearOrderedField

variable {R M : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M]
  [Module R M] {B : LinearMap.BilinForm R M}

/-- **The Cauchy--Schwarz inequality for a positive-semidefinite bilinear form**:
`(B u v)² ≤ B u u · B v v`.  Definiteness is not needed: the quadratic
`t ↦ B (u + t • v) (u + t • v)` is nonnegative, so its discriminant is nonpositive. -/
theorem IsPosSemidef.sq_apply_le_mul_apply_self (hB : B.IsPosSemidef) (u v : M) :
    B u v ^ 2 ≤ B u u * B v v := by
  have hsymm := LinearMap.BilinForm.isSymm_def.1 hB.isSymm
  have hexp : ∀ t : R, B (u + t • v) (u + t • v) = B v v * (t * t) + 2 * B u v * t + B u u := by
    intro t
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hsymm v u]
    ring
  have hquad : ∀ t : R, 0 ≤ B v v * (t * t) + 2 * B u v * t + B u u := fun t =>
    (hexp t) ▸ hB.isNonneg.nonneg (u + t • v)
  have hdiscrim := discrim_le_zero hquad
  simp only [discrim] at hdiscrim
  linarith [hdiscrim]

end LinearOrderedField

end LinearMap.BilinForm
