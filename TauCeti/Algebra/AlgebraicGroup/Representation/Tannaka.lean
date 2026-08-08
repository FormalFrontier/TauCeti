/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Monoidal

/-!
# Tensor compatibility of point actions

Let `H` be a Hopf algebra over a commutative ring `R`, and let `A` be a commutative
`R`-algebra. Scalar extension defines a fiber functor from finitely generated `H`-comodules to
`A`-modules,

```text
M ↦ A ⊗[R] M.
```

Every `A`-valued point `g : H →ₐ[R] A` already acts naturally on each scalar extension. This
file proves that those actions preserve the canonical tensor comparison and act trivially on the
trivial comodule. These are the two nontrivial monoidal identities needed to package a point as a
tensor automorphism of the fiber functor.

This file supplies the mathematical compatibility step, not the full categorical packaging or
the reconstruction theorem. Constructing the monoidal fiber functor and proving that every tensor
automorphism comes from a unique point remain.

## Main declarations

* `TauCeti.Tannaka.endOfPoint_tensor`: the action preserves tensor products under the canonical
  scalar-extension comparison.
* `TauCeti.Tannaka.endOfPoint_trivial`: the action is the identity on the trivial comodule.

## References

These identities are the forward-direction monoidal compatibility in Tannakian reconstruction for
affine group schemes; see J. S. Milne, *Algebraic Groups* (2017), §§4.5 and 9.4. The proof reuses
Mathlib's `TensorProduct.AlgebraTensorModule.distribBaseChange` and Tau Ceti's existing point action
and tensor coaction. This advances Layer 1, "Tannakian reconstruction", of the ReductiveGroups
roadmap.
-/

public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace TauCeti.Tannaka

universe u v

variable (R : Type u) [CommRing R]
variable (H : Type v) [Semiring H] [HopfAlgebra R H]
variable (A : Type u) [CommRing A] [Algebra R A]

private theorem distribute_pointAction_tensor (g : WithConv (H →ₐ[R] A))
    (M N : FGComoduleCat.{u, v, u} R H) (x : M ⊗[R] H) (y : N ⊗[R] H) :
    (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm
        ((TensorProduct.comm R M A
            (LinearMap.lTensor M g.ofConv.toLinearMap x)) ⊗ₜ[A]
          TensorProduct.comm R N A
            (LinearMap.lTensor N g.ofConv.toLinearMap y)) =
      TensorProduct.comm R (M ⊗[R] N) A
        (LinearMap.lTensor (M ⊗[R] N) g.ofConv.toLinearMap
          (Comodule.tensorCombine (x ⊗ₜ[R] y))) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ hx₁ hx₂ =>
      simpa only [map_add, TensorProduct.add_tmul] using
        congrArg₂ (fun a b ↦ a + b) hx₁ hx₂
  | tmul m h =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y₁ y₂ hy₁ hy₂ =>
          simpa only [map_add, TensorProduct.tmul_add] using
            congrArg₂ (fun a b ↦ a + b) hy₁ hy₂
      | tmul n k =>
          simp [Comodule.tensorCombine_tmul_tmul]

/-- On pure tensors, acting separately on two comodules and applying the scalar-extension
tensor comparison agrees with acting on their tensor-product comodule. -/
theorem endOfPoint_tensor_tmul (g : WithConv (H →ₐ[R] A))
    (M N : FGComoduleCat.{u, v, u} R H) (a b : A) (m : M) (n : N) :
    (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm
        (Comodule.endOfPoint M.obj g.ofConv (a ⊗ₜ[R] m) ⊗ₜ[A]
          Comodule.endOfPoint N.obj g.ofConv (b ⊗ₜ[R] n)) =
      Comodule.endOfPoint (M ⊗ N : FGComoduleCat.{u, v, u} R H).obj g.ofConv
        ((a * b) ⊗ₜ[R] (m ⊗ₜ[R] n)) := by
  rw [Comodule.endOfPoint_tmul, Comodule.endOfPoint_tmul, Comodule.endOfPoint_tmul,
    FGComoduleCat.tensor_coact, Comodule.tensorCoact_tmul]
  simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
  rw [mul_comm b a, ← TensorProduct.smul_tmul', map_smul]
  congr 1
  exact distribute_pointAction_tensor R H A g M N (Comodule.coact m) (Comodule.coact n)

/-- A point action preserves tensor products. Under the canonical comparison
`(A ⊗ M) ⊗[A] (A ⊗ N) ≃ A ⊗ (M ⊗ N)`, acting on the two factors separately equals acting on
the tensor-product comodule. -/
theorem endOfPoint_tensor (g : WithConv (H →ₐ[R] A))
    (M N : FGComoduleCat.{u, v, u} R H) :
    (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap ∘ₗ
        TensorProduct.map (Comodule.endOfPoint M.obj g.ofConv)
          (Comodule.endOfPoint N.obj g.ofConv) =
      Comodule.endOfPoint (M ⊗ N : FGComoduleCat.{u, v, u} R H).obj g.ofConv ∘ₗ
        (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro x y
  induction x using TensorProduct.induction_on with
  | zero =>
      rw [TensorProduct.zero_tmul, map_zero, map_zero]
  | add x₁ x₂ hx₁ hx₂ =>
      rw [TensorProduct.add_tmul, map_add, map_add]
      exact congrArg₂ (fun a b ↦ a + b) hx₁ hx₂
  | tmul a m =>
      induction y using TensorProduct.induction_on with
      | zero =>
          rw [TensorProduct.tmul_zero, map_zero, map_zero]
      | add y₁ y₂ hy₁ hy₂ =>
          rw [TensorProduct.tmul_add, map_add, map_add]
          exact congrArg₂ (fun a b ↦ a + b) hy₁ hy₂
      | tmul b n =>
          simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe]
          rw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul]
          exact endOfPoint_tensor_tmul R H A g M N a b m n

/-- A point acts trivially on the trivial comodule, which is the tensor unit of finite
comodules. -/
theorem endOfPoint_trivial (g : WithConv (H →ₐ[R] A)) :
    let _ : Comodule R H R := Comodule.trivial (R := R) (C := H) (M := R)
    Comodule.endOfPoint R g.ofConv = LinearMap.id := by
  let _ : Comodule R H R := Comodule.trivial (R := R) (C := H) (M := R)
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a r =>
      simp only [Comodule.endOfPoint_tmul, Comodule.trivial_coact_apply,
        LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, map_one,
        TensorProduct.comm_tmul]
      rw [TensorProduct.smul_tmul']
      simp

end TauCeti.Tannaka
