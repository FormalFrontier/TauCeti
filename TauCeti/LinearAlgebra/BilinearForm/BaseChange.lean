/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Bilinear forms and base change

This file relates bilinear forms transported along an `IsBaseChange` equivalence to Mathlib's
canonical base change of bilinear forms, and records how nondegeneracy behaves under that base
change.

Nondegeneracy is not preserved by an arbitrary base change: a form can acquire a kernel when its
discriminant becomes a zero divisor. On a finite free module it is exactly the nonvanishing of
that discriminant, so an injective structure map between integral domains preserves and reflects
it. That is `TauCeti.nondegenerate_baseChange_iff`, and the computation behind it,
`TauCeti.bilinForm_toMatrix_baseChange`, is the statement that base change acts entrywise on the
Gram matrix of a basis.

## Main declarations

* `TauCeti.IsBaseChange.bilinForm_baseChange`: if a bilinear form restricts along a map to a
  second form, evaluating it through the associated base-change equivalence agrees with the
  canonical base change of the second form.
* `TauCeti.bilinForm_toMatrix_baseChange`: the Gram matrix of a base-changed form, in the
  base-changed basis, is the entrywise image of the original Gram matrix.
* `TauCeti.nondegenerate_baseChange_iff`: a bilinear form on a finite free module over an integral
  domain is nondegenerate exactly when its base change along an injective structure map into a
  second integral domain is.
-/

public section

open Module TensorProduct

namespace TauCeti

namespace IsBaseChange

variable {R : Type*} {A : Type*} {M : Type*} {N : Type*}
variable [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module A N] [Module R N] [IsScalarTower R A N]
variable {f : M →ₗ[R] N} (h : IsBaseChange A f)

/-- If `B` restricts along `f` to `B'`, evaluating `B` on base-changed vectors agrees with the
canonical base change of `B'`. -/
theorem bilinForm_baseChange (B' : LinearMap.BilinForm R M) (B : LinearMap.BilinForm A N)
    (hB : ∀ x y : M, B (f x) (f y) = algebraMap R A (B' x y)) (x y : A ⊗[R] M) :
    B (h.equiv x) (h.equiv y) = B'.baseChange A x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [map_add, LinearMap.add_apply, hx₁, hx₂]
  | tmul a m =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ hy₁ hy₂ =>
      simp only [map_add, hy₁, hy₂]
    | tmul a' m' =>
      simp only [IsBaseChange.equiv_tmul, LinearMap.BilinForm.smul_left,
        LinearMap.BilinForm.smul_right, LinearMap.BilinForm.baseChange_tmul,
        hB, Algebra.smul_def]
      ring

end IsBaseChange

section Nondegenerate

variable {R A M ι : Type*}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M]

/-- Base change acts entrywise on the Gram matrix of a bilinear form: the matrix of `B.baseChange A`
in the base-changed basis is the image of the matrix of `B` under the structure map. -/
@[simp]
theorem bilinForm_toMatrix_baseChange [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm R M) (b : Basis ι R M) :
    LinearMap.BilinForm.toMatrix (b.baseChange A) (B.baseChange A) =
      (LinearMap.BilinForm.toMatrix b B).map (algebraMap R A) := by
  ext i j
  simp [LinearMap.BilinForm.toMatrix_apply, Basis.baseChange_apply,
    Algebra.algebraMap_eq_smul_one]

/-- **Nondegeneracy is preserved and reflected by an injective base change of integral domains.**
On a finite free module, nondegeneracy of a bilinear form is nonvanishing of the determinant of its
Gram matrix, and an injective structure map neither creates nor destroys that. -/
theorem nondegenerate_baseChange_iff [Finite ι] [IsDomain R] [IsDomain A] [FaithfulSMul R A]
    (B : LinearMap.BilinForm R M) (b : Basis ι R M) :
    (B.baseChange A).Nondegenerate ↔ B.Nondegenerate := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b.baseChange A),
    LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b, bilinForm_toMatrix_baseChange,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R A)

end Nondegenerate

end TauCeti
