/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Bilinear forms and base change

This file relates bilinear forms transported along an `IsBaseChange` equivalence to Mathlib's
canonical base change of bilinear forms.

## Main declarations

* `TauCeti.IsBaseChange.bilinForm_baseChange`: evaluating a bilinear form through a base-change
  equivalence agrees with the canonical base change of the original form.
-/

public section

open Module TensorProduct

namespace TauCeti

namespace IsBaseChange

variable {R : Type*} {A : Type*} {M : Type*} {N : Type*}
variable [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module A N] [Module R N] [IsScalarTower R A N]
variable {f : M →ₗ[R] N} (h : IsBaseChange A f)

/-- Evaluating a bilinear form on base-changed vectors via an `IsBaseChange` equivalence
identifies it with the canonical base change of the original bilinear form. -/
theorem bilinForm_baseChange (B' : LinearMap.BilinForm R M) (B : LinearMap.BilinForm A N)
    (hB : ∀ x y : M, B (f x) (f y) = algebraMap R A (B' x y)) (x y : A ⊗[R] M) :
    B (h.equiv x) (h.equiv y) = B'.baseChange A x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [map_add, LinearMap.add_apply, hx₁, hx₂]
  | tmul a m =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ hy₁ hy₂ =>
      simp only [map_add, hy₁, hy₂]
    | tmul a' m' =>
      simp only [IsBaseChange.equiv_tmul, LinearMap.BilinForm.smul_left,
        LinearMap.BilinForm.smul_right, LinearMap.BilinForm.baseChange_tmul,
        hB, Algebra.smul_def]
      ring

end IsBaseChange

end TauCeti
