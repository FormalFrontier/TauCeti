/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Dual.BaseChange

/-!
# Evaluation after scalar extension

This file defines the canonical pairing between the scalar extensions of a module and its linear
dual. It sends an `R`-linear functional extended to `A` to the corresponding `A`-linear functional
on the scalar extension of its domain. No finiteness hypothesis is required, and the construction
is not asserted to identify the scalar extension of the dual with the full dual of the scalar
extension.

## Main declarations

* `TauCeti.Module.Dual.baseChangeEvaluation`: the canonical scalar-extended evaluation map.
* `TauCeti.Module.Dual.baseChangeEvaluation_tmul`: its value on two pure tensors.
-/

public section

open scoped TensorProduct

namespace TauCeti.Module.Dual

universe u w x

variable {R : Type u} {M : Type w} {A : Type x}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [CommSemiring A] [Algebra R A]

/-- The canonical pairing of scalar extensions, as the map sending a scalar-extended
`R`-linear functional to an `A`-linear functional on the scalar extension of its domain.

This map requires no finiteness hypothesis and is not asserted to be an equivalence. -/
def baseChangeEvaluation :
    A ⊗[R] Module.Dual R M →ₗ[A] Module.Dual A (A ⊗[R] M) :=
  (Module.Dual.baseChange A).liftBaseChange A

/-- On pure tensors, scalar-extended evaluation is
`⟨a ⊗ φ, b ⊗ m⟩ = a * b * algebraMap R A (φ m)`. -/
@[simp]
theorem baseChangeEvaluation_tmul (a b : A) (φ : Module.Dual R M) (m : M) :
    baseChangeEvaluation (R := R) (M := M) (A := A) (a ⊗ₜ[R] φ) (b ⊗ₜ[R] m) =
      a * b * algebraMap R A (φ m) := by
  simp only [baseChangeEvaluation, LinearMap.liftBaseChange_tmul, LinearMap.smul_apply,
    Module.Dual.baseChange_apply_tmul, Algebra.smul_def]
  rw [Algebra.algebraMap_self_apply]
  ac_rfl

end TauCeti.Module.Dual
