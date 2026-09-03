/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.OfAssociative
public import TauCeti.Algebra.Matrix.BaseChange

/-!
# Scalar extension of matrix Lie algebras

The associative matrix-algebra base-change equivalence also identifies Mathlib's scalar extension
of the matrix Lie algebra with the matrix Lie algebra over the target ring. The explicit Lie
equivalence is needed because the scalar-extension bracket and the associative commutator bracket
are propositionally equal but come from different, non-definitionally-equal `LieRing` instances.

## Main definitions

* `TauCeti.matrixBaseChangeLieEquiv`: the Lie equivalence
  `A ⊗[R] Matrix n n R ≃ Matrix n n A`.
-/

public section

namespace TauCeti

open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n R A : Type*) [Fintype n] [DecidableEq n]
  [CommRing R] [CommRing A] [Algebra R A]

/-- Scalar extension commutes with forming a matrix Lie algebra. The underlying linear
equivalence is `TauCeti.Algebra.matrixBaseChangeAlgEquiv`; the Lie proof bridges Mathlib's
scalar-extension bracket with the associative commutator bracket on matrices. -/
noncomputable def matrixBaseChangeLieEquiv :
    A ⊗[R] Matrix n n R ≃ₗ⁅A⁆ Matrix n n A where
  toFun := Algebra.matrixBaseChangeAlgEquiv R A n
  invFun := (Algebra.matrixBaseChangeAlgEquiv R A n).symm
  left_inv := (Algebra.matrixBaseChangeAlgEquiv R A n).left_inv
  right_inv := (Algebra.matrixBaseChangeAlgEquiv R A n).right_inv
  map_add' := map_add (Algebra.matrixBaseChangeAlgEquiv R A n)
  map_smul' := map_smul (Algebra.matrixBaseChangeAlgEquiv R A n)
  map_lie' {x y} := by
    induction x with
    | zero => simp
    | tmul a M =>
      induction y with
      | zero => simp
      | tmul b N =>
        simp only [LieAlgebra.ExtendScalars.bracket_tmul,
          Algebra.matrixBaseChangeAlgEquiv_tmul, LieRing.of_associative_ring_bracket]
        rw [Matrix.map_sub _ (map_sub (algebraMap R A)), Matrix.map_mul, Matrix.map_mul,
          smul_sub]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]
      | add y z hy hz => simp [hy, hz]
    | add x z hx hz => simp [hx, hz]

/-- The scalar-extension equivalence sends a pure tensor to the entrywise scalar extension. -/
@[simp]
theorem matrixBaseChangeLieEquiv_tmul (a : A) (M : Matrix n n R) :
    matrixBaseChangeLieEquiv n R A (a ⊗ₜ[R] M) = a • M.map (algebraMap R A) :=
  Algebra.matrixBaseChangeAlgEquiv_tmul R A n a M

end TauCeti
