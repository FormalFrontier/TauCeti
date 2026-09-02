/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.BaseChange
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Matrix
public import TauCeti.LinearAlgebra.Dual.BaseChange

/-!
# Matrix coefficients under base change

Extending a finite free comodule and its coefficient coalgebra along the same scalar morphism
extends every entry of its coefficient matrix. This is the coordinate calculation needed to
transport faithful representations across field extensions.

## Main declaration

* `TauCeti.Comodule.coefficientMatrix_baseChange`: the coefficient matrix in the base-changed
  basis is obtained by sending `cᵢⱼ` to `1 ⊗ cᵢⱼ`.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2.

This supplies the matrix-coefficient compatibility needed for base-change invariance of
geometric unipotence in Layer 5 of the ReductiveGroups roadmap.
-/

public section

open Module
open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w x

noncomputable section

variable {R : Type u} {A : Type v} {C : Type w} {M : Type x} {ι : Type*}
variable [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- Base change sends every entry of a comodule's coefficient matrix to the corresponding pure
tensor in the base-changed coefficient coalgebra. -/
@[simp]
theorem coefficientMatrix_baseChange (b : Basis ι R M) :
    letI := Comodule.baseChange (R := R) (H := C) (M := M) A
    coefficientMatrix (C := A ⊗[R] C) (b.baseChange A) =
      (coefficientMatrix (C := C) b).map
        ((TensorProduct.mk R A C) 1) := by
  let _ := Comodule.baseChange (R := R) (H := C) (M := M) A
  ext i j
  rw [coefficientMatrix_apply, Matrix.map_apply, coefficientMatrix_apply,
    matrixCoefficient_def, matrixCoefficient_def, Basis.baseChange_apply,
    baseChange_coact, baseChangeCoact_tmul]
  induction coact (R := R) (C := C) (M := M) (b j) using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, TensorProduct.tmul_add, hz, hw]
  | tmul m c => simp

end

end TauCeti.Comodule
