/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Coalgebra.TensorProduct

/-!
# Base change of coalgebras

This file records formulas for the coalgebra structure on a scalar extension `A ⊗[R] H`.

## Main declarations

* `TauCeti.Coalgebra.baseChange_comul_tmul`: the comultiplication of a scalar extension on
  pure tensors.
-/

public section

open scoped TensorProduct

namespace TauCeti.Coalgebra

universe u v w

variable {R : Type u} (A : Type v) {H : Type w}
variable [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommMonoid H] [Module R H] [CoalgebraStruct R H]

/-- The comultiplication of a base-changed coalgebra on a pure tensor. -/
theorem baseChange_comul_tmul (a : A) (h : H) :
    Coalgebra.comul (R := A) (A := A ⊗[R] H) (a ⊗ₜ[R] h) =
      TensorProduct.AlgebraTensorModule.distribBaseChange R A H H
        (a ⊗ₜ[R] Coalgebra.comul (R := R) (A := H) h) := by
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply]
  induction Coalgebra.comul (R := R) (A := H) h using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul g k =>
      simp only [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
        TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
      rw [TensorProduct.tmul_eq_smul_one_tmul a g,
        TensorProduct.tmul_eq_smul_one_tmul a k, TensorProduct.tmul_smul]
      exact TensorProduct.smul_tmul' a (1 ⊗ₜ[R] g) (1 ⊗ₜ[R] k)

end TauCeti.Coalgebra
