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
* `TauCeti.Module.Dual.baseChange_coord`: base-changed dual basis elements recover the
  coordinates in the base-changed basis.
* `TauCeti.Module.Dual.eq_of_baseChange_eq`: base changes of all dual elements jointly
  separate vectors when the original module is free.
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

/-- A coordinate in a base-changed basis is evaluation against the base change of the
corresponding element of the dual basis. -/
@[simp]
theorem baseChange_coord {ι : Type*} (b : Module.Basis ι R M) (i : ι) (z : A ⊗[R] M) :
    ((TensorProduct.isBaseChange R M A).basis b).repr z i =
      Module.Dual.baseChange A (b.coord i) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simpa only [map_add, Finsupp.add_apply] using congrArg₂ (· + ·) hz hw
  | tmul a m =>
      calc
        ((TensorProduct.isBaseChange R M A).basis b).repr (a ⊗ₜ[R] m) i =
            ((TensorProduct.isBaseChange R M A).basis b).repr
              (a • (1 ⊗ₜ[R] m)) i := by
          simp [TensorProduct.smul_tmul']
        _ = a * ((TensorProduct.isBaseChange R M A).basis b).repr (1 ⊗ₜ[R] m) i := by simp
        _ = a * algebraMap R A (b.repr m i) := by
          simpa only [TensorProduct.mk_apply] using congrArg (a * ·)
            (IsBaseChange.basis_repr_comp_apply b (TensorProduct.isBaseChange R M A) m i)
        _ = Module.Dual.baseChange A (b.coord i) (a ⊗ₜ[R] m) := by
          simp [Module.Basis.coord_apply, Algebra.smul_def, mul_comm]

/-- If `M` is free, the base changes of its `R`-linear functionals jointly separate vectors
in `A ⊗[R] M`. -/
theorem eq_of_baseChange_eq [Module.Free R M] {x y : A ⊗[R] M}
    (h : ∀ φ : Module.Dual R M,
      Module.Dual.baseChange A φ x = Module.Dual.baseChange A φ y) : x = y := by
  let b := Module.Free.chooseBasis R M
  let bA := (TensorProduct.isBaseChange R M A).basis b
  apply bA.ext_elem
  intro i
  rw [baseChange_coord b i x, baseChange_coord b i y]
  exact h (b.coord i)

end TauCeti.Module.Dual
