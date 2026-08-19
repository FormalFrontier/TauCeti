/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Localization.BaseChange
public import TauCeti.Geometry.Hodge.Conjugation

/-!
# Complexification of an integral bilinear form

An integral bilinear form on a lattice extends uniquely to a complex bilinear form on any
abstract complexification of that lattice. This file constructs that extension,
`TauCeti.Hodge.integralFormToComplex`, from Mathlib's base change of a bilinear form along the
canonical tensor model, and characterizes it by its values on integral vectors.

Two properties make the extension usable in Hodge theory. It is *real*: conjugating both arguments
conjugates the value, because lattice-induced conjugation fixes the integral vectors. And it is
nondegenerate as soon as the integral form is: nondegeneracy is preserved first by localization from
`ℤ` to `ℚ` and then by scalar extension from `ℚ` to `ℂ`.

## Main declarations

* `TauCeti.Hodge.integralFormToComplex`: the complex bilinear form extending an integral one.
* `TauCeti.Hodge.integralFormToComplex_ι`: its values on integral vectors.
* `TauCeti.Hodge.integralFormToComplex_unique`: it is the only such extension.
* `TauCeti.Hodge.integralFormToComplex_conj`: it commutes with lattice-induced conjugation.
* `TauCeti.Hodge.integralFormToComplex_nondegenerate`: it inherits nondegeneracy from the integral
  form.
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
@[simp]
theorem integralFormToComplex_flip (hℂ : IsBaseChange ℂ ιℂ) (Q : LinearMap.BilinForm ℤ V) :
    (integralFormToComplex hℂ Q).flip = integralFormToComplex hℂ Q.flip :=
  integralFormToComplex_unique hℂ _ _ fun x y ↦ by simp

/-- Complexification commutes with integer multiples of an integral form. -/
@[simp]
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

private theorem integralFormToRat_nondegenerate {Q : LinearMap.BilinForm ℤ V}
    (hQ : Q.Nondegenerate) : (Q.baseChange ℚ).Nondegenerate := by
  let f : V →ₗ[ℤ] ℚ ⊗[ℤ] V := TensorProduct.mk ℤ ℚ V 1
  have hf : IsLocalizedModule (nonZeroDivisors ℤ) f := by
    rw [isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ]
    exact TensorProduct.isBaseChange ℤ V ℚ
  constructor
  · intro x hx
    obtain ⟨⟨v, s⟩, hs⟩ := hf.surj x
    have hv : v = 0 := hQ.1 v fun w ↦ by
      have h : Q.baseChange ℚ (s • x) (1 ⊗ₜ[ℤ] w) = 0 := by simp [hx]
      rw [hs] at h
      change Q.baseChange ℚ (1 ⊗ₜ[ℤ] v) (1 ⊗ₜ[ℤ] w) = 0 at h
      have hc : (Q v w : ℚ) = 0 := by simpa using h
      exact_mod_cast hc
    rw [hv, map_zero] at hs
    exact (IsLocalizedModule.smul_injective f s) (by simpa using hs)
  · intro y hy
    obtain ⟨⟨v, s⟩, hs⟩ := hf.surj y
    have hv : v = 0 := hQ.2 v fun w ↦ by
      have h : Q.baseChange ℚ (1 ⊗ₜ[ℤ] w) (s • y) = 0 := by simp [hy]
      rw [hs] at h
      change Q.baseChange ℚ (1 ⊗ₜ[ℤ] w) (1 ⊗ₜ[ℤ] v) = 0 at h
      have hc : (Q w v : ℚ) = 0 := by simpa using h
      exact_mod_cast hc
    rw [hv, map_zero] at hs
    exact (IsLocalizedModule.smul_injective f s) (by simpa using hs)

private theorem rationalFormToComplex_nondegenerate {W : Type*} [AddCommGroup W] [Module ℚ W]
    {B : LinearMap.BilinForm ℚ W} (hB : B.Nondegenerate) :
    (B.baseChange ℂ).Nondegenerate := by
  classical
  let b := Module.Free.chooseBasis ℚ ℂ
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := W) b
  constructor
  · intro x hx
    let c := e x
    have hc : c = 0 := by
      ext i
      apply hB.1 (c i)
      intro w
      have h := hx (1 ⊗ₜ[ℚ] w)
      have hrepr : c.sum (fun i v ↦ b i ⊗ₜ[ℚ] v) = x := by
        calc
          c.sum (fun i v ↦ b i ⊗ₜ[ℚ] v) = e.symm c :=
            (TensorProduct.equivFinsuppOfBasisLeft_symm_apply b c).symm
          _ = x := by simp [c]
      rw [← hrepr] at h
      have hi := congrArg (fun z : ℂ ↦ b.repr z i) h
      have hi' : (∑ j ∈ c.support, Finsupp.single j (B (c j) w)) i = 0 := by
        simpa [Finsupp.sum] using hi
      by_cases hic : i ∈ c.support
      · have heval : (∑ j ∈ c.support, Finsupp.single j (B (c j) w)) i =
            B (c i) w := by
          simp [Finsupp.single_apply, hic]
        exact heval ▸ hi'
      · have hci : c i = 0 := Finsupp.notMem_support_iff.mp hic
        simp [hci]
    exact e.injective (by simpa [c] using hc)
  · intro y hy
    let c := e y
    have hc : c = 0 := by
      ext i
      apply hB.2 (c i)
      intro w
      have h := hy (1 ⊗ₜ[ℚ] w)
      have hrepr : c.sum (fun i v ↦ b i ⊗ₜ[ℚ] v) = y := by
        calc
          c.sum (fun i v ↦ b i ⊗ₜ[ℚ] v) = e.symm c :=
            (TensorProduct.equivFinsuppOfBasisLeft_symm_apply b c).symm
          _ = y := by simp [c]
      rw [← hrepr] at h
      have hi := congrArg (fun z : ℂ ↦ b.repr z i) h
      have hi' : (∑ j ∈ c.support, Finsupp.single j (B w (c j))) i = 0 := by
        simpa [Finsupp.sum] using hi
      by_cases hic : i ∈ c.support
      · have heval : (∑ j ∈ c.support, Finsupp.single j (B w (c j))) i =
            B w (c i) := by
          simp [Finsupp.single_apply, hic]
        exact heval ▸ hi'
      · have hci : c i = 0 := Finsupp.notMem_support_iff.mp hic
        simp [hci]
    exact e.injective (by simpa [c] using hc)

private theorem integralFormToCanonicalComplex_nondegenerate {Q : LinearMap.BilinForm ℤ V}
    (hQ : Q.Nondegenerate) : (Q.baseChange ℂ).Nondegenerate := by
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ V
  have hn : ((Q.baseChange ℚ).baseChange ℂ).Nondegenerate :=
    rationalFormToComplex_nondegenerate (integralFormToRat_nondegenerate hQ)
  have heq : Q.baseChange ℂ =
      LinearMap.BilinForm.congr e ((Q.baseChange ℚ).baseChange ℂ) := by
    ext z v
    simp [e]
  rw [heq]
  exact LinearMap.BilinForm.Nondegenerate.congr e hn

/-- Complexification preserves nondegeneracy of an integral bilinear form. -/
theorem integralFormToComplex_nondegenerate (hℂ : IsBaseChange ℂ ιℂ)
    {Q : LinearMap.BilinForm ℤ V} (hQ : Q.Nondegenerate) :
    (integralFormToComplex hℂ Q).Nondegenerate := by
  have hform : integralFormToComplex hℂ Q =
      LinearMap.BilinForm.congr hℂ.equiv (Q.baseChange ℂ) := by
    ext x y
    rfl
  rw [hform]
  exact LinearMap.BilinForm.Nondegenerate.congr hℂ.equiv
    (integralFormToCanonicalComplex_nondegenerate hQ)

end TauCeti.Hodge
