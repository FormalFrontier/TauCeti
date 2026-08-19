/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.RingTheory.TensorProduct.Free
public import TauCeti.Geometry.Hodge.Conjugation

/-!
# Complexification of an integral bilinear form

An integral bilinear form on a lattice extends uniquely to a complex bilinear form on any
abstract complexification of that lattice. This file constructs that extension,
`TauCeti.Hodge.integralFormToComplex`, from Mathlib's base change of a bilinear form along the
canonical tensor model, and characterizes it by its values on integral vectors.

Two properties make the extension usable in Hodge theory. It is *real*: conjugating both arguments
conjugates the value, because lattice-induced conjugation fixes the integral vectors. And it is
nondegenerate as soon as the integral form is, provided the lattice is finite free, since
nondegeneracy of a form on a finite free module over a domain is the nonvanishing of the
determinant of its Gram matrix.

## Main declarations

* `TauCeti.Hodge.integralFormToComplex`: the complex bilinear form extending an integral one.
* `TauCeti.Hodge.integralFormToComplex_ι`: its values on integral vectors.
* `TauCeti.Hodge.integralFormToComplex_unique`: it is the only such extension.
* `TauCeti.Hodge.integralFormToComplex_conj`: it commutes with lattice-induced conjugation.
* `TauCeti.Hodge.integralFormToComplex_nondegenerate`: it inherits nondegeneracy from a finite
  free lattice.
-/

public section

namespace TauCeti.Hodge

open scoped TensorProduct

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

/-- The complexification of an integral bilinear form, transported from Mathlib's base change
along the canonical tensor model to an abstract complexification. -/
noncomputable def integralFormToComplex (hℂ : IsBaseChange ℂ ιℂ)
    (Q : LinearMap.BilinForm ℤ V) : LinearMap.BilinForm ℂ Vℂ :=
  (Q.baseChange ℂ).compl₁₂ hℂ.equiv.symm.toLinearMap hℂ.equiv.symm.toLinearMap

/-- On integral vectors the complexified form is the integral form. -/
@[simp]
theorem integralFormToComplex_ι (hℂ : IsBaseChange ℂ ιℂ) (Q : LinearMap.BilinForm ℤ V)
    (x y : V) : integralFormToComplex hℂ Q (ιℂ x) (ιℂ y) = (Q x y : ℂ) := by
  simp [integralFormToComplex, hℂ.equiv_symm_apply]

/-- The complexified form is the unique complex bilinear form restricting to the integral one. -/
theorem integralFormToComplex_unique (hℂ : IsBaseChange ℂ ιℂ) (Q : LinearMap.BilinForm ℤ V)
    (B : LinearMap.BilinForm ℂ Vℂ) (hB : ∀ x y : V, B (ιℂ x) (ιℂ y) = (Q x y : ℂ)) :
    B = integralFormToComplex hℂ Q := by
  refine hℂ.algHom_ext _ _ fun x ↦ hℂ.algHom_ext _ _ fun y ↦ ?_
  simp [hB x y]

/-- Complexification turns the flip of an integral form into the flip of the complexified form. -/
theorem integralFormToComplex_flip (hℂ : IsBaseChange ℂ ιℂ) (Q : LinearMap.BilinForm ℤ V) :
    (integralFormToComplex hℂ Q).flip = integralFormToComplex hℂ Q.flip :=
  integralFormToComplex_unique hℂ _ _ fun x y ↦ by simp

/-- Complexification commutes with integer multiples of an integral form. -/
theorem integralFormToComplex_zsmul (hℂ : IsBaseChange ℂ ιℂ) (k : ℤ)
    (Q : LinearMap.BilinForm ℤ V) :
    integralFormToComplex hℂ (k • Q) = k • integralFormToComplex hℂ Q :=
  (integralFormToComplex_unique hℂ _ _ fun x y ↦ by simp).symm

/-- Conjugating the second argument of a complexified integral form against an integral first
argument conjugates its value. -/
theorem integralFormToComplex_conj_right (hℂ : IsBaseChange ℂ ιℂ) (Q : LinearMap.BilinForm ℤ V)
    (x : V) (y : Vℂ) :
    integralFormToComplex hℂ Q (ιℂ x) (latticeConj hℂ y) =
      starRingEnd ℂ (integralFormToComplex hℂ Q (ιℂ x) y) := by
  induction y using hℂ.inductionOn with
  | zero => simp
  | tmul w => simp
  | smul z y hy => simp [hy]
  | add y₁ y₂ hy₁ hy₂ => simp [hy₁, hy₂]

/-- Conjugating both arguments of a complexified integral form conjugates its value: the form
takes real values on the lattice. -/
@[simp]
theorem integralFormToComplex_conj (hℂ : IsBaseChange ℂ ιℂ) (Q : LinearMap.BilinForm ℤ V)
    (x y : Vℂ) :
    integralFormToComplex hℂ Q (latticeConj hℂ x) (latticeConj hℂ y) =
      starRingEnd ℂ (integralFormToComplex hℂ Q x y) := by
  induction x using hℂ.inductionOn generalizing y with
  | zero => simp
  | tmul v => simpa using integralFormToComplex_conj_right hℂ Q v y
  | smul z x hx => simp [hx]
  | add x₁ x₂ hx₁ hx₂ => simp [hx₁, hx₂]

/-- The complexification of a nondegenerate integral form on a finite free lattice is
nondegenerate.

Over a domain, nondegeneracy of a form on a finite free module is the nonvanishing of the
determinant of its Gram matrix, and the Gram matrix of the complexified form in the complexified
basis is the entrywise image of the integral Gram matrix. -/
theorem integralFormToComplex_nondegenerate [Module.Free ℤ V] [Module.Finite ℤ V]
    (hℂ : IsBaseChange ℂ ιℂ) {Q : LinearMap.BilinForm ℤ V}
    (hQ : LinearMap.BilinForm.Nondegenerate Q) :
    LinearMap.BilinForm.Nondegenerate (integralFormToComplex hℂ Q) := by
  classical
  set b := Module.Free.chooseBasis ℤ V
  set bℂ := (Algebra.TensorProduct.basis ℂ b).map hℂ.equiv with hbℂ
  have hbℂ_apply : ∀ i, bℂ i = ιℂ (b i) := by
    intro i
    simp [hbℂ, hℂ.equiv_tmul]
  have hmat : LinearMap.BilinForm.toMatrix bℂ (integralFormToComplex hℂ Q) =
      (LinearMap.BilinForm.toMatrix b Q).map (fun z : ℤ ↦ (z : ℂ)) := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply, hbℂ_apply]
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bℂ, hmat, ← Int.cast_det]
  simpa using (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hQ

end TauCeti.Hodge
