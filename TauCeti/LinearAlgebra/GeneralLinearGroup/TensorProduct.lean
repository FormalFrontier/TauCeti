/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor products in the general linear group

This file packages the tensor product of two linear automorphisms as an automorphism and records
its compatibility with multiplication, inverses, and pure tensors.

## Main declarations

* `TauCeti.GeneralLinearGroup.tensorProduct`: the tensor product of two linear automorphisms.
* `TauCeti.GeneralLinearGroup.tensorProduct_apply_tmul`: its action on a pure tensor.
-/

public section

namespace TauCeti

open LinearMap
open scoped TensorProduct

namespace GeneralLinearGroup

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
theorem tensorProduct_apply_tmul (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W)
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
  apply Units.ext
  -- Reduce equality of units to Mathlib's multiplicativity of `TensorProduct.map`.
  change TensorProduct.map (↑(g₁ * g₂)) (↑(h₁ * h₂)) =
    TensorProduct.map (g₁ : Module.End K V) (h₁ : Module.End K W) *
      TensorProduct.map (g₂ : Module.End K V) (h₂ : Module.End K W)
  simpa only [Units.val_mul] using TensorProduct.map_mul
    (g₁ : Module.End K V) (g₂ : Module.End K V)
    (h₁ : Module.End K W) (h₂ : Module.End K W)

/-- The tensor product of two identity automorphisms is the identity. -/
@[simp]
theorem tensorProduct_one :
    tensorProduct (1 : GeneralLinearGroup K V) (1 : GeneralLinearGroup K W) = 1 := by
  apply Units.ext
  -- Reduce equality of units to Mathlib's identity law for `TensorProduct.map`.
  change TensorProduct.map (1 : Module.End K V) (1 : Module.End K W) = 1
  exact TensorProduct.map_one

/-- Tensor products preserve inverses. -/
@[simp]
theorem tensorProduct_inv (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    tensorProduct g⁻¹ h⁻¹ = (tensorProduct g h)⁻¹ := by
  apply mul_left_cancel (a := tensorProduct g h)
  rw [← tensorProduct_mul, mul_inv_cancel, mul_inv_cancel, tensorProduct_one,
    mul_inv_cancel]

end GeneralLinearGroup

end TauCeti
