/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Tensor products in the general linear group

This file packages the tensor product of two linear automorphisms as an automorphism and records
its compatibility with multiplication, inverses, and pure tensors.

## Main declarations

* `LinearMap.GeneralLinearGroup.tensorProduct`: the tensor product of two linear automorphisms.
* `LinearMap.GeneralLinearGroup.tensorProduct_tmul`: its action on a pure tensor.
-/

public section

open scoped TensorProduct

namespace LinearMap.GeneralLinearGroup

universe u v w

variable {K : Type u} {V : Type v} {W : Type w}
variable [CommSemiring K] [AddCommMonoid V] [Module K V]
  [AddCommMonoid W] [Module K W]

/-- The tensor product of two linear automorphisms. -/
def tensorProduct (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    GeneralLinearGroup K (V ⊗[K] W) :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv
    (TensorProduct.congr g.toLinearEquiv h.toLinearEquiv)

/-- The endomorphism underlying a tensor-product automorphism is `TensorProduct.map`. -/
theorem coe_tensorProduct (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    (tensorProduct g h : Module.End K (V ⊗[K] W)) =
      TensorProduct.map (g : Module.End K V) (h : Module.End K W) :=
  (rfl)

/-- A tensor-product automorphism acts factorwise on pure tensors. -/
@[simp]
theorem tensorProduct_tmul (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W)
    (v : V) (w : W) :
    (tensorProduct g h : Module.End K (V ⊗[K] W)) (v ⊗ₜ[K] w) =
      (g : Module.End K V) v ⊗ₜ[K] (h : Module.End K W) w :=
  (rfl)

/-- Tensor products preserve multiplication. -/
@[simp]
theorem tensorProduct_mul (g₁ g₂ : GeneralLinearGroup K V)
    (h₁ h₂ : GeneralLinearGroup K W) :
    tensorProduct (g₁ * g₂) (h₁ * h₂) =
      tensorProduct g₁ h₁ * tensorProduct g₂ h₂ := by
  simp only [tensorProduct, LinearMap.GeneralLinearGroup.toLinearEquiv_mul,
    TensorProduct.congr_mul,
    LinearMap.GeneralLinearGroup.ofLinearEquiv_mul]

/-- The tensor product of two identity automorphisms is the identity. -/
@[simp]
theorem tensorProduct_one :
    tensorProduct (1 : GeneralLinearGroup K V) (1 : GeneralLinearGroup K W) = 1 := by
  symm
  apply mul_left_cancel (a := tensorProduct (1 : GeneralLinearGroup K V)
    (1 : GeneralLinearGroup K W))
  simpa only [one_mul, mul_one] using
    (tensorProduct_mul (1 : GeneralLinearGroup K V) 1 (1 : GeneralLinearGroup K W) 1)

/-- Tensor products preserve inverses. -/
@[simp]
theorem tensorProduct_inv (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    tensorProduct g⁻¹ h⁻¹ = (tensorProduct g h)⁻¹ := by
  exact eq_inv_of_mul_eq_one_left <| by
    rw [← tensorProduct_mul, inv_mul_cancel, inv_mul_cancel, tensorProduct_one]

end LinearMap.GeneralLinearGroup
