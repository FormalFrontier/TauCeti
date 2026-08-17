/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Prod

/-!
# Products in the general linear group

This file defines the componentwise product of two linear automorphisms and proves its basic
compatibility with the group operations.

## Main declarations

* `TauCeti.GeneralLinearGroup.prodMap`: the componentwise product of two linear automorphisms.
* `TauCeti.GeneralLinearGroup.prodMap_apply`: the product automorphism acts componentwise.
-/

public section

namespace TauCeti

open LinearMap

namespace GeneralLinearGroup

universe u v w

variable {K : Type u} {V : Type v} {W : Type w}
variable [Semiring K] [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]

/-- The product map of two linear automorphisms, acting componentwise on the product module. -/
def prodMap (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    GeneralLinearGroup K (V × W) :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv (g.toLinearEquiv.prodCongr h.toLinearEquiv)

/-- The endomorphism underlying a product-map automorphism is `LinearMap.prodMap`. -/
theorem coe_prodMap (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    (prodMap g h : Module.End K (V × W)) =
      (g : Module.End K V).prodMap (h : Module.End K W) :=
  (rfl)

/-- A product-map automorphism acts componentwise. -/
@[simp]
theorem prodMap_apply (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) (x : V × W) :
    (prodMap g h : Module.End K (V × W)) x =
      ((g : Module.End K V) x.1, (h : Module.End K W) x.2) := by
  rw [coe_prodMap, LinearMap.prodMap_apply]

/-- Product maps preserve multiplication. -/
@[simp]
theorem prodMap_mul (g₁ g₂ : GeneralLinearGroup K V) (h₁ h₂ : GeneralLinearGroup K W) :
    prodMap (g₁ * g₂) (h₁ * h₂) = prodMap g₁ h₁ * prodMap g₂ h₂ := by
  ext x <;> rfl

/-- The product map of two identity automorphisms is the identity. -/
@[simp]
theorem prodMap_one : prodMap (1 : GeneralLinearGroup K V) (1 : GeneralLinearGroup K W) = 1 := by
  ext x <;> rfl

/-- Product maps preserve inverses. -/
@[simp]
theorem prodMap_inv (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    prodMap g⁻¹ h⁻¹ = (prodMap g h)⁻¹ := by
  ext x <;> rfl

end GeneralLinearGroup

end TauCeti
