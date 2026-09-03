/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.RingTheory.IsTensorProduct
import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
# Bilinear forms and base change

This file relates bilinear forms transported along an `IsBaseChange` equivalence to Mathlib's
canonical base change of bilinear forms, and records how nondegeneracy behaves under that base
change.

Nondegeneracy is not preserved by an arbitrary base change: a form can acquire a kernel when its
discriminant becomes a zero divisor. On a finite free module it is exactly the nonvanishing of
that discriminant, so any structure map between integral domains reflects it, and an injective one
also preserves it. Those are `TauCeti.nondegenerate_of_nondegenerate_baseChange` and
`TauCeti.nondegenerate_baseChange_iff`, and the computations behind them,
`TauCeti.bilinForm_toMatrix_baseChange` and `TauCeti.bilinForm_det_toMatrix_baseChange`, say that
base change acts entrywise on the Gram matrix of a basis and maps its determinant accordingly.

## Main declarations

* `TauCeti.IsBaseChange.bilinForm_baseChange`: if a bilinear form restricts along a map to a
  second form, evaluating it through the associated base-change equivalence agrees with the
  canonical base change of the second form.
* `TauCeti.bilinForm_toMatrix_baseChange`: the Gram matrix of a base-changed form, in the
  base-changed basis, is the entrywise image of the original Gram matrix.
* `TauCeti.bilinForm_det_toMatrix_baseChange`: the determinant of that Gram matrix is the image of
  the original determinant.
* `TauCeti.nondegenerate_of_nondegenerate_baseChange`: a bilinear form on a finite free
  module over an integral domain is nondegenerate as soon as its base change into a second integral
  domain is, with no hypothesis on the structure map.
* `TauCeti.nondegenerate_baseChange_iff`: along an injective structure map between
  integral domains the implication is an equivalence.
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

section Semiring

variable {R A M ι : Type*}
variable [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M]

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

end Semiring

section Nondegenerate

variable {R A M ι : Type*}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M]

/-- The Gram determinant of a base-changed bilinear form is the image of the original Gram
determinant under the structure map. -/
theorem bilinForm_det_toMatrix_baseChange [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm R M) (b : Basis ι R M) :
    (LinearMap.BilinForm.toMatrix (b.baseChange A) (B.baseChange A)).det =
      algebraMap R A (LinearMap.BilinForm.toMatrix b B).det := by
  rw [bilinForm_toMatrix_baseChange, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

variable (A) in
/-- **Nondegeneracy descends along any base change of integral domains.** On a finite free module,
nondegeneracy of a bilinear form is nonvanishing of the determinant of its Gram matrix, and the
structure map sends that determinant to the determinant of the base-changed Gram matrix, so a
nondegenerate base change forces a nondegenerate form. No hypothesis on the structure map is
needed. -/
theorem nondegenerate_of_nondegenerate_baseChange [Finite ι] [IsDomain R] [IsDomain A]
    (B : LinearMap.BilinForm R M) (b : Basis ι R M) (h : (B.baseChange A).Nondegenerate) :
    B.Nondegenerate := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b.baseChange A),
    bilinForm_det_toMatrix_baseChange] at h
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b]
  exact fun hdet ↦ h (by rw [hdet, map_zero])

/-- **Nondegeneracy is preserved and reflected by an injective base change of integral domains.**
On a finite free module, nondegeneracy of a bilinear form is nonvanishing of the determinant of its
Gram matrix, and an injective structure map neither creates nor destroys that. -/
theorem nondegenerate_baseChange_iff [Finite ι] [IsDomain A] [FaithfulSMul R A]
    (B : LinearMap.BilinForm R M) (b : Basis ι R M) :
    (B.baseChange A).Nondegenerate ↔ B.Nondegenerate := by
  classical
  have : IsDomain R :=
    Function.Injective.isDomain (algebraMap R A) (FaithfulSMul.algebraMap_injective R A)
  have : Fintype ι := Fintype.ofFinite ι
  refine ⟨nondegenerate_of_nondegenerate_baseChange A B b, fun h ↦ ?_⟩
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b.baseChange A),
    bilinForm_det_toMatrix_baseChange]
  exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R A)).mpr
    ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp h)

end Nondegenerate

end TauCeti
