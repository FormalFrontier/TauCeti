/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Semisimple endomorphisms of tensor products

Tensoring a semisimple endomorphism with the identity preserves semisimplicity.  After choosing a
basis of the unchanged factor, the tensor product is a direct sum of copies of the original
module, and the tensor endomorphism acts componentwise.

## Main declarations

* `TauCeti.Module.End.IsSemisimple.rTensor`: `f ⊗ 1` is semisimple when `f` is.
* `TauCeti.Module.End.IsSemisimple.lTensor`: `1 ⊗ f` is semisimple when `f` is.
-/

public section

namespace TauCeti

open Polynomial
open scoped TensorProduct

namespace Module.End

universe u v w

variable {K : Type u} {V : Type v} {W : Type w}
variable [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

private theorem aeval_rTensor (f : _root_.Module.End K V) (p : K[X]) :
    aeval (f.rTensor W) p = (aeval f p).rTensor W := by
  -- Present one-sided tensoring through its algebra homomorphism so `aeval_algHom_apply` applies.
  change aeval ((_root_.Module.End.rTensorAlgHom K V W) f) p =
    (_root_.Module.End.rTensorAlgHom K V W) (aeval f p)
  exact Polynomial.aeval_algHom_apply (_root_.Module.End.rTensorAlgHom K V W) f p

private theorem aeval_lTensor (f : _root_.Module.End K W) (p : K[X]) :
    aeval (f.lTensor V) p = (aeval f p).lTensor V := by
  -- Present one-sided tensoring through its algebra homomorphism so `aeval_algHom_apply` applies.
  change aeval ((_root_.Module.End.lTensorAlgHom K W V) f) p =
    (_root_.Module.End.lTensorAlgHom K W V) (aeval f p)
  exact Polynomial.aeval_algHom_apply (_root_.Module.End.lTensorAlgHom K W V) f p

section Right

variable [Module.Free K W]

/-- Tensoring a semisimple endomorphism on the right with an identity endomorphism preserves
semisimplicity. -/
theorem IsSemisimple.rTensor {f : _root_.Module.End K V} (hf : f.IsSemisimple) :
    _root_.Module.End.IsSemisimple (f.rTensor W) := by
  classical
  rw [_root_.Module.End.IsSemisimple] at hf ⊢
  let _ : IsSemisimpleModule K[X] (Module.AEval' f) := hf
  let b := Module.Free.chooseBasis K W
  let E₀ : (V ⊗[K] W) ≃ₗ[K] (Module.Free.ChooseBasisIndex K W →₀ V) :=
    TensorProduct.equivFinsuppOfBasisRight b
  let E : Module.AEval' (f.rTensor W) ≃ₗ[K[X]]
      (Module.Free.ChooseBasisIndex K W →₀ Module.AEval' f) := by
    exact {
      toFun := fun x ↦ E₀ x
      invFun := fun x ↦ E₀.symm x
      left_inv := E₀.left_inv
      right_inv := E₀.right_inv
      map_add' := E₀.map_add
      map_smul' := fun p x ↦ by
        -- Polynomial scalar multiplication on `AEval'` is evaluation at its endomorphism.
        change E₀ (aeval (f.rTensor W) p x) = _
        rw [aeval_rTensor]
        ext i
        change E₀ ((aeval f p).rTensor W x) i = aeval f p (E₀ x i)
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul v w =>
            simp [E₀]
        | add x y hx hy => simp [hx, hy]
    }
  exact IsSemisimpleModule.congr E

end Right

section Left

variable [Module.Free K V]

/-- Tensoring a semisimple endomorphism on the left with an identity endomorphism preserves
semisimplicity. -/
theorem IsSemisimple.lTensor {f : _root_.Module.End K W} (hf : f.IsSemisimple) :
    _root_.Module.End.IsSemisimple (f.lTensor V) := by
  classical
  rw [_root_.Module.End.IsSemisimple] at hf ⊢
  let _ : IsSemisimpleModule K[X] (Module.AEval' f) := hf
  let b := Module.Free.chooseBasis K V
  let E₀ : (V ⊗[K] W) ≃ₗ[K] (Module.Free.ChooseBasisIndex K V →₀ W) :=
    TensorProduct.equivFinsuppOfBasisLeft b
  let E : Module.AEval' (f.lTensor V) ≃ₗ[K[X]]
      (Module.Free.ChooseBasisIndex K V →₀ Module.AEval' f) := by
    exact {
      toFun := fun x ↦ E₀ x
      invFun := fun x ↦ E₀.symm x
      left_inv := E₀.left_inv
      right_inv := E₀.right_inv
      map_add' := E₀.map_add
      map_smul' := fun p x ↦ by
        -- Polynomial scalar multiplication on `AEval'` is evaluation at its endomorphism.
        change E₀ (aeval (f.lTensor V) p x) = _
        rw [aeval_lTensor]
        ext i
        change E₀ ((aeval f p).lTensor V x) i = aeval f p (E₀ x i)
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul v w =>
            simp [E₀]
        | add x y hx hy => simp [hx, hy]
    }
  exact IsSemisimpleModule.congr E

end Left

end Module.End

end TauCeti
