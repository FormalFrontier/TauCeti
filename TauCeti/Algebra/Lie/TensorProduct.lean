/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Prod
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Lie homomorphisms from products to tensor products

Two Lie homomorphisms into associative algebras induce a Lie homomorphism from the product of
their domains to the tensor product of their codomains. The two images commute because they lie
in separate tensor factors.

## Main definitions

* `LieHom.prodToTensor`: the induced Lie homomorphism from a product to a tensor product.
-/

public section

open scoped TensorProduct

namespace LieHom

universe u v w x y

variable {R : Type u} {L : Type v} {M : Type w} {A : Type x} {B : Type y}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]
variable [Ring A] [Algebra R A] [Ring B] [Algebra R B]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Two Lie homomorphisms into associative algebras induce a Lie homomorphism from the product of
their domains to the tensor product of their codomains, with each image placed in its corresponding
tensor factor. -/
def prodToTensor (f : L →ₗ⁅R⁆ A) (g : M →ₗ⁅R⁆ B) :
    (L × M) →ₗ⁅R⁆ (A ⊗[R] B) := by
  refine
    { toLinearMap := LinearMap.coprod
        (Algebra.TensorProduct.includeLeft.toLinearMap.comp f.toLinearMap)
        (Algebra.TensorProduct.includeRight.toLinearMap.comp g.toLinearMap)
      map_lie' := ?_ }
  intro z z'
  -- Expose the coproduct and tensor inclusions through their stable API lemmas before
  -- simplifying the Lie bracket below.
  simp only [LinearMap.toFun_eq_coe, AlgHom.toLinearMap_apply, LieAlgebra.Prod.bracket_apply,
    LinearMap.coprod_apply,
    LinearMap.comp_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply]
  have hf : f.toLinearMap ⁅z.1, z'.1⁆ = ⁅f z.1, f z'.1⁆ := f.map_lie _ _
  have hg : g.toLinearMap ⁅z.2, z'.2⁆ = ⁅g z.2, g z'.2⁆ := g.map_lie _ _
  rw [hf, hg]
  simp only [LieHom.coe_toLinearMap]
  simp only [LieRing.of_associative_ring_bracket, mul_add, add_mul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
    TensorProduct.sub_tmul, TensorProduct.tmul_sub]
  abel

/-- Compute the product-to-tensor Lie homomorphism on a pair:
`prodToTensor f g (x, y) = f x ⊗ 1 + 1 ⊗ g y`. -/
@[simp]
theorem prodToTensor_apply (f : L →ₗ⁅R⁆ A) (g : M →ₗ⁅R⁆ B) (z : L × M) :
    prodToTensor f g z = f z.1 ⊗ₜ[R] (1 : B) + (1 : A) ⊗ₜ[R] g z.2 := by
  have h : (prodToTensor f g).toLinearMap z = f z.1 ⊗ₜ[R] (1 : B) + (1 : A) ⊗ₜ[R] g z.2 := by
    simp only [prodToTensor, LieHom.coe_toLinearMap, LinearMap.coprod_apply, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply]
  simpa only [LieHom.coe_toLinearMap] using h

end LieHom
