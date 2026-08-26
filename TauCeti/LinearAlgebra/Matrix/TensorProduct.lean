/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MatrixAlgebra
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Tensor products of matrix algebras

This file records the finite-index form of the Kronecker equivalence for tensor products of
matrix algebras.

## Main result

* `Matrix.kroneckerTMulFinAlgEquiv`: matrix absorption
  `M_m(A) ⊗[R] M_n(B) ≃ₐ[R] M_(mn)(A ⊗[R] B)`.
-/

public section

open scoped Kronecker TensorProduct

namespace Matrix

/-- **Matrix absorption**: `M_m(A) ⊗[R] M_n(B) ≃ₐ[R] M_(mn)(A ⊗[R] B)`, over any commutative
semiring `R` and any two `R`-algebras, in any two sizes. -/
def kroneckerTMulFinAlgEquiv (m n : ℕ) (R : Type*) [CommSemiring R] (A : Type*) [Semiring A]
    [Algebra R A] (B : Type*) [Semiring B] [Algebra R B] :
    Matrix (Fin m) (Fin m) A ⊗[R] Matrix (Fin n) (Fin n) B ≃ₐ[R]
      Matrix (Fin (m * n)) (Fin (m * n)) (A ⊗[R] B) :=
  (Matrix.kroneckerTMulAlgEquiv (Fin m) (Fin n) R R A B).trans
    (Matrix.reindexAlgEquiv R _ finProdFinEquiv)

/-- The finite-index matrix absorption equivalence sends a pure tensor to the reindexed
Kronecker tensor product. -/
@[simp]
theorem kroneckerTMulFinAlgEquiv_tmul (m n : ℕ) (R : Type*) [CommSemiring R]
    (A : Type*) [Semiring A] [Algebra R A] (B : Type*) [Semiring B] [Algebra R B]
    (a : Matrix (Fin m) (Fin m) A) (b : Matrix (Fin n) (Fin n) B) :
    Matrix.kroneckerTMulFinAlgEquiv m n R A B (a ⊗ₜ[R] b) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (a ⊗ₖₜ b) := by
  simp only [kroneckerTMulFinAlgEquiv, AlgEquiv.trans_apply,
    Matrix.kroneckerTMulAlgEquiv_apply, kroneckerTMulLinearEquiv_tmul,
    Matrix.coe_reindexAlgEquiv]

/-- The inverse finite-index matrix absorption equivalence sends a matrix unit at paired finite
indices with a pure-tensor coefficient to the tensor of the two corresponding matrix units. -/
@[simp]
theorem kroneckerTMulFinAlgEquiv_symm_single_tmul (m n : ℕ) (R : Type*)
    [CommSemiring R] (A : Type*) [Semiring A] [Algebra R A] (B : Type*) [Semiring B]
    [Algebra R B] (ia ja : Fin m) (ib jb : Fin n) (a : A) (b : B) :
    (Matrix.kroneckerTMulFinAlgEquiv m n R A B).symm
        (Matrix.single (finProdFinEquiv (ia, ib)) (finProdFinEquiv (ja, jb)) (a ⊗ₜ[R] b)) =
      Matrix.single ia ja a ⊗ₜ[R] Matrix.single ib jb b := by
  rw [AlgEquiv.symm_apply_eq]
  rw [Matrix.kroneckerTMulFinAlgEquiv_tmul, Matrix.single_kroneckerTMul_single]
  simp

end Matrix
