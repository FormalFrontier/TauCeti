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

* `TauCeti.Matrix.kroneckerTMulFinAlgEquiv`: matrix absorption
  `M_m(A) ⊗[R] M_n(B) ≃ₐ[R] M_(mn)(A ⊗[R] B)`.
-/

public section

open scoped TensorProduct

namespace TauCeti

/-- **Matrix absorption**: `M_m(A) ⊗[R] M_n(B) ≃ₐ[R] M_(mn)(A ⊗[R] B)`, over any commutative
semiring `R` and any two `R`-algebras, in any two sizes. -/
def Matrix.kroneckerTMulFinAlgEquiv (m n : ℕ) (R : Type*) [CommSemiring R] (A : Type*) [Semiring A]
    [Algebra R A] (B : Type*) [Semiring B] [Algebra R B] :
    Matrix (Fin m) (Fin m) A ⊗[R] Matrix (Fin n) (Fin n) B ≃ₐ[R]
      Matrix (Fin (m * n)) (Fin (m * n)) (A ⊗[R] B) :=
  (Matrix.kroneckerTMulAlgEquiv (Fin m) (Fin n) R R A B).trans
    (Matrix.reindexAlgEquiv R _ finProdFinEquiv)

end TauCeti
