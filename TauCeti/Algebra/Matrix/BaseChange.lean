/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `matrixEquivTensor` is the whole content of `TauCeti.Algebra.matrixBaseChangeAlgEquiv` below,
-- whose statement also needs `Matrix`, the `⊗[R]` notation and the `S`-algebra structure on
-- `S ⊗[R] Matrix n n R`; this Mathlib file supplies all of them.
public import Mathlib.RingTheory.MatrixAlgebra
-- `TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv` is one of the four steps of
-- `TauCeti.Algebra.matrixCoeffBaseChangeAlgEquiv`, and a compiled definition may not refer to a
-- privately imported one, hence the public import. It re-exports
-- `Mathlib.RingTheory.TensorProduct.Maps`, hence `Algebra.TensorProduct.congr`, used in the same
-- body, which is why that is not imported again here.
public import TauCeti.Algebra.TensorProduct.BaseChange

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

The same statement with an arbitrary, possibly noncommutative, coefficient algebra `A` in place of
`R` is `TauCeti.Algebra.matrixCoeffBaseChangeAlgEquiv`:
`S ⊗[R] Matrix n n A ≃ₐ[S] Matrix n n (S ⊗[R] A)`. It is *not* a generalization of the first
equivalence, whose target `Matrix n n S` is `Matrix n n (S ⊗[R] R)` only up to
`Algebra.TensorProduct.rid`; and it is the first equivalence, applied to the scalar matrices, that
makes the second one go through.
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

variable (A : Type*) [Semiring A] [Algebra R A]

/-- **Base change commutes with forming a matrix algebra**:
`S ⊗[R] Matrix n n A ≃ₐ[S] Matrix n n (S ⊗[R] A)`, entrywise, for an arbitrary and possibly
noncommutative coefficient algebra `A`.

The four steps are Mathlib's `matrixEquivTensor`, splitting off the scalar matrices as
`Matrix n n A ≃ₐ[R] A ⊗[R] Matrix n n R`; the distributivity
`TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv` of base change over `⊗`;
`TauCeti.Algebra.matrixBaseChangeAlgEquiv` on the scalar factor; and `matrixEquivTensor` again,
backwards, over `S`. -/
def matrixCoeffBaseChangeAlgEquiv : S ⊗[R] Matrix n n A ≃ₐ[S] Matrix n n (S ⊗[R] A) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl (R := S) (A₁ := S)) (matrixEquivTensor n R A)).trans
    ((TensorProduct.baseChangeTensorAlgEquiv R S A (Matrix n n R)).trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := S) (A₁ := S ⊗[R] A))
          (matrixBaseChangeAlgEquiv R S n)).trans
        (matrixEquivTensor n S (S ⊗[R] A)).symm))

@[simp]
theorem matrixCoeffBaseChangeAlgEquiv_tmul_apply (s : S) (M : Matrix n n A) (i j : n) :
    matrixCoeffBaseChangeAlgEquiv R S n A (s ⊗ₜ M) i j = s ⊗ₜ[R] M i j := by
  classical
  induction M using Matrix.induction_on' with
  | h_zero => simp
  | h_add M N hM hN => simp [TensorProduct.tmul_add, hM, hN]
  | h_std_basis p q a =>
    simp [matrixCoeffBaseChangeAlgEquiv, Matrix.single_apply, apply_ite (s ⊗ₜ[R] ·)]

@[simp]
theorem matrixCoeffBaseChangeAlgEquiv_symm_single (i j : n) (s : S) (a : A) :
    (matrixCoeffBaseChangeAlgEquiv R S n A).symm (Matrix.single i j (s ⊗ₜ a)) =
      s ⊗ₜ Matrix.single i j a :=
  (matrixCoeffBaseChangeAlgEquiv R S n A).symm_apply_eq.mpr <| by
    ext p q
    simp [Matrix.single_apply, apply_ite (s ⊗ₜ[R] ·)]

end Algebra

end TauCeti
