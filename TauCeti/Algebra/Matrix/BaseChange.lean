/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `matrixEquivTensor` is the whole content of `TauCeti.Algebra.matrixBaseChangeAlgEquiv` below,
-- whose statement also needs `Matrix`, the `⊗[R]` notation and the `S`-algebra structure on
-- `S ⊗[R] Matrix n n R`; this Mathlib file supplies all of them.
public import Mathlib.RingTheory.MatrixAlgebra

/-!
# Base change of a matrix algebra

Extending scalars along an algebra map `R → S` of commutative semirings turns matrices over `R`
into matrices over `S`, entrywise:
`TauCeti.Algebra.matrixBaseChangeAlgEquiv : S ⊗[R] Matrix n n R ≃ₐ[S] Matrix n n S`.

Mathlib's `matrixEquivTensor` is this isomorphism read as an `R`-algebra isomorphism; the content
here is that it is `S`-linear, which is the form base change is used in. Mathlib's Kronecker
version `Matrix.kroneckerTMulAlgEquiv` is the two-sided statement and does not specialize to this
one without reindexing.

Both directions are characterized on generators by the `simp` lemmas
`TauCeti.Algebra.matrixBaseChangeAlgEquiv_tmul` and
`TauCeti.Algebra.matrixBaseChangeAlgEquiv_symm_single`, so the definition need never be unfolded.
-/

public section

namespace TauCeti

open scoped TensorProduct

namespace Algebra

variable (R : Type*) [CommSemiring R] (S : Type*) [CommSemiring S] [Algebra R S]
  (n : Type*) [Fintype n] [DecidableEq n]

/-- **Extending scalars turns matrices over `R` into matrices over `S`**:
`S ⊗[R] Matrix n n R ≃ₐ[S] Matrix n n S`, entrywise.

Mathlib's `matrixEquivTensor` is this isomorphism read as an `R`-algebra isomorphism; the content
here is that it is `S`-linear. -/
def matrixBaseChangeAlgEquiv : S ⊗[R] Matrix n n R ≃ₐ[S] Matrix n n S :=
  AlgEquiv.ofRingEquiv (f := (matrixEquivTensor n R S).symm.toRingEquiv) fun s ↦ by
    simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul',
      Matrix.map_one]

@[simp]
theorem matrixBaseChangeAlgEquiv_tmul (s : S) (M : Matrix n n R) :
    matrixBaseChangeAlgEquiv R S n (s ⊗ₜ M) = s • M.map (algebraMap R S) := by
  simp [matrixBaseChangeAlgEquiv]

@[simp]
theorem matrixBaseChangeAlgEquiv_symm_single (i j : n) (x : S) :
    (matrixBaseChangeAlgEquiv R S n).symm (Matrix.single i j x) = x ⊗ₜ Matrix.single i j 1 := by
  simp [matrixBaseChangeAlgEquiv]

end Algebra

end TauCeti
