/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.MatrixAlgebra

/-!
# Scalar extension of matrix Lie algebras

For a commutative ring map `R → A`, extending scalars in the matrix Lie algebra over `R`
gives the matrix Lie algebra over `A`. The equivalence in this file is the `A`-linear form of
Mathlib's algebra equivalence `matrixEquivTensor`; on a pure tensor it sends
`a ⊗ M` to the entrywise scalar multiple `a • M.map (algebraMap R A)`.

## Main definitions

* `TauCeti.Matrix.scalarExtensionLieEquiv`: the Lie equivalence
  `A ⊗[R] Matrix n n R ≃ Matrix n n A`.
-/

public section

namespace TauCeti.Matrix

open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n R A : Type*) [Fintype n] [DecidableEq n]
  [CommRing R] [CommRing A] [Algebra R A]

/-- **Scalar extension commutes with forming a matrix Lie algebra.** This is the canonical
`A`-linear Lie equivalence from the scalar extension of `R`-matrices to `A`-matrices. -/
noncomputable def scalarExtensionLieEquiv :
    A ⊗[R] _root_.Matrix n n R ≃ₗ⁅A⁆ _root_.Matrix n n A where
  toFun := (matrixEquivTensor n R A).symm
  invFun := matrixEquivTensor n R A
  left_inv := (matrixEquivTensor n R A).apply_symm_apply
  right_inv := (matrixEquivTensor n R A).symm_apply_apply
  map_add' := map_add (matrixEquivTensor n R A).symm
  map_smul' a x := by
    induction x with
    | zero => simp
    | tmul b M => simp [TensorProduct.smul_tmul', mul_smul]
    | add x y hx hy => simp [hx, hy]
  map_lie' {x y} := by
    induction x with
    | zero => simp
    | tmul a M =>
      induction y with
      | zero => simp
      | tmul b N =>
        simp only [LieAlgebra.ExtendScalars.bracket_tmul, matrixEquivTensor_apply_symm,
          LieRing.of_associative_ring_bracket]
        rw [_root_.Matrix.map_sub _ (map_sub (algebraMap R A)), _root_.Matrix.map_mul,
          _root_.Matrix.map_mul, smul_sub]
        simp only [_root_.Matrix.smul_mul, _root_.Matrix.mul_smul, smul_smul, mul_comm]
      | add y z hy hz => simp [hy, hz]
    | add x z hx hz => simp [hx, hz]

/-- On a pure tensor, the scalar-extension equivalence applies the structure map entrywise and
then scales the resulting matrix. -/
@[simp]
theorem scalarExtensionLieEquiv_tmul (a : A) (M : _root_.Matrix n n R) :
    scalarExtensionLieEquiv n R A (a ⊗ₜ[R] M) = a • M.map (algebraMap R A) :=
  matrixEquivTensor_apply_symm n R A a M

end TauCeti.Matrix
