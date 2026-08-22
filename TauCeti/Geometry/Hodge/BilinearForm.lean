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
public import TauCeti.Geometry.Hodge.BaseChange

/-!
# Scalar extension of an integral bilinear form

An integral bilinear form on a lattice extends uniquely to a bilinear form on any abstract base
change of that lattice. This file constructs that extension,
`TauCeti.Hodge.integralFormBaseChange`, from Mathlib's base change of a bilinear form along the
canonical tensor model, and characterizes it by its values on integral vectors. The rational and
the complex extension are the two cases the Hodge theory uses, and they agree on the purely
rational vectors of the complexification.

Two properties make the complex extension usable in Hodge theory. It is *real*: conjugating both
arguments conjugates the value, because lattice-induced conjugation fixes the integral vectors. And
it is nondegenerate as soon as the integral form is: nondegeneracy is preserved first by
localization from `ℤ` to `ℚ` and then by scalar extension from `ℚ` to `ℂ`.

## Main declarations

* `TauCeti.Hodge.integralFormBaseChange`: the bilinear form extending an integral one along an
  abstract base change of its lattice.
* `TauCeti.Hodge.integralFormBaseChange_ι`: its values on integral vectors.
* `TauCeti.Hodge.integralFormBaseChange_unique`: it is the only such extension.
* `TauCeti.Hodge.integralFormBaseChange_conj`: the complex extension commutes with lattice-induced
  conjugation.
* `TauCeti.Hodge.integralFormBaseChange_nondegenerate`: the complex extension inherits
  nondegeneracy from the integral form.
* `TauCeti.Hodge.integralFormBaseChange_rationalToComplexLinearEquiv_one_tmul`: the complexified
  form computes the rationalified one on purely rational vectors.
-/

public section

namespace TauCeti.Hodge

open scoped TensorProduct

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

section BaseChange

variable {A : Type*} {V_A : Type*} [CommRing A] [AddCommGroup V_A] [Module A V_A]
variable {ι : V →ₗ[ℤ] V_A}

/-- The scalar extension of an integral bilinear form along an abstract base change of its
lattice, transported from Mathlib's base change along the canonical tensor model. -/
noncomputable def integralFormBaseChange (h : IsBaseChange A ι)
    (Q : LinearMap.BilinForm ℤ V) : LinearMap.BilinForm A V_A :=
  (Q.baseChange A).compl₁₂ h.equiv.symm.toLinearMap h.equiv.symm.toLinearMap

/-- On integral vectors the extended form is the integral form. -/
@[simp]
theorem integralFormBaseChange_ι (h : IsBaseChange A ι) (Q : LinearMap.BilinForm ℤ V)
    (x y : V) : integralFormBaseChange h Q (ι x) (ι y) = (Q x y : A) := by
  simp [integralFormBaseChange, h.equiv_symm_apply]

/-- The extended form is the unique bilinear form restricting to the integral one. -/
theorem integralFormBaseChange_unique (h : IsBaseChange A ι) (Q : LinearMap.BilinForm ℤ V)
    (B : LinearMap.BilinForm A V_A) (hB : ∀ x y : V, B (ι x) (ι y) = (Q x y : A)) :
    B = integralFormBaseChange h Q := by
  refine h.algHom_ext _ _ fun x ↦ h.algHom_ext _ _ fun y ↦ ?_
  simp [hB x y]

/-- Scalar extension turns the flip of an integral form into the flip of the extended form. -/
@[simp]
theorem integralFormBaseChange_flip (h : IsBaseChange A ι) (Q : LinearMap.BilinForm ℤ V) :
    (integralFormBaseChange h Q).flip = integralFormBaseChange h Q.flip :=
  integralFormBaseChange_unique h _ _ fun x y ↦ by simp

/-- Scalar extension commutes with integer multiples of an integral form. -/
@[simp]
theorem integralFormBaseChange_zsmul (h : IsBaseChange A ι) (k : ℤ)
    (Q : LinearMap.BilinForm ℤ V) :
    integralFormBaseChange h (k • Q) = k • integralFormBaseChange h Q :=
  (integralFormBaseChange_unique h _ _ fun x y ↦ by simp).symm

end BaseChange

/-- Conjugating the second argument of a complexified integral form against an integral first
argument conjugates its value. -/
theorem integralFormBaseChange_conj_right (hℂ : IsBaseChange ℂ ιℂ) (Q : LinearMap.BilinForm ℤ V)
    (x : V) (y : Vℂ) :
    integralFormBaseChange hℂ Q (ιℂ x) (latticeConj hℂ y) =
      starRingEnd ℂ (integralFormBaseChange hℂ Q (ιℂ x) y) := by
  induction y using hℂ.inductionOn with
  | zero => simp
  | tmul w => simp
  | smul z y hy => simp [hy]
  | add y₁ y₂ hy₁ hy₂ => simp [hy₁, hy₂]

/-- Conjugating both arguments of a complexified integral form conjugates its value: the form
takes real values on the lattice. -/
@[simp]
theorem integralFormBaseChange_conj (hℂ : IsBaseChange ℂ ιℂ) (Q : LinearMap.BilinForm ℤ V)
    (x y : Vℂ) :
    integralFormBaseChange hℂ Q (latticeConj hℂ x) (latticeConj hℂ y) =
      starRingEnd ℂ (integralFormBaseChange hℂ Q x y) := by
  induction x using hℂ.inductionOn generalizing y with
  | zero => simp
  | tmul v => simpa using integralFormBaseChange_conj_right hℂ Q v y
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
      have hfv : f v = 1 ⊗ₜ[ℤ] v := rfl
      rw [hfv] at h
      rw [LinearMap.BilinForm.baseChange_tmul] at h
      have hc : (Q v w : ℚ) = 0 := by simpa using h
      exact_mod_cast hc
    rw [hv, map_zero] at hs
    exact (IsLocalizedModule.smul_injective f s) (by simpa using hs)
  · intro y hy
    obtain ⟨⟨v, s⟩, hs⟩ := hf.surj y
    have hv : v = 0 := hQ.2 v fun w ↦ by
      have h : Q.baseChange ℚ (1 ⊗ₜ[ℤ] w) (s • y) = 0 := by simp [hy]
      rw [hs] at h
      have hfv : f v = 1 ⊗ₜ[ℤ] v := rfl
      rw [hfv] at h
      rw [LinearMap.BilinForm.baseChange_tmul] at h
      have hc : (Q w v : ℚ) = 0 := by simpa using h
      exact_mod_cast hc
    rw [hv, map_zero] at hs
    exact (IsLocalizedModule.smul_injective f s) (by simpa using hs)

private theorem rationalFormToComplex_separatingLeft {W : Type*} [AddCommGroup W] [Module ℚ W]
    {B : LinearMap.BilinForm ℚ W} (hB : B.SeparatingLeft) :
    (B.baseChange ℂ).SeparatingLeft := by
  classical
  let b := Module.Free.chooseBasis ℚ ℂ
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := W) b
  intro x hx
  let c := e x
  have hc : c = 0 := by
    ext i
    apply hB (c i)
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

private theorem rationalFormToComplex_baseChange_flip {W : Type*} [AddCommGroup W] [Module ℚ W]
    (B : LinearMap.BilinForm ℚ W) :
    B.flip.baseChange ℂ = (B.baseChange ℂ).flip := by
  ext z v
  simp

private theorem rationalFormToComplex_nondegenerate {W : Type*} [AddCommGroup W] [Module ℚ W]
    {B : LinearMap.BilinForm ℚ W} (hB : B.Nondegenerate) :
    (B.baseChange ℂ).Nondegenerate := by
  constructor
  · exact rationalFormToComplex_separatingLeft hB.1
  · have hBflip : B.flip.SeparatingLeft := fun y hy ↦ hB.2 y hy
    have h := rationalFormToComplex_separatingLeft hBflip
    rw [rationalFormToComplex_baseChange_flip] at h
    exact h

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
theorem integralFormBaseChange_nondegenerate (hℂ : IsBaseChange ℂ ιℂ)
    {Q : LinearMap.BilinForm ℤ V} (hQ : Q.Nondegenerate) :
    (integralFormBaseChange hℂ Q).Nondegenerate := by
  have hform : integralFormBaseChange hℂ Q =
      LinearMap.BilinForm.congr hℂ.equiv (Q.baseChange ℂ) := by
    ext x y
    simp only [integralFormBaseChange, LinearMap.compl₁₂_apply,
      LinearMap.BilinForm.congr_apply, LinearEquiv.coe_coe]
  rw [hform]
  exact LinearMap.BilinForm.Nondegenerate.congr hℂ.equiv
    (integralFormToCanonicalComplex_nondegenerate hQ)

/-! ### Comparing the rational and the complex extension -/

section Rational

variable {Vℚ : Type*} [AddCommGroup Vℚ] [Module ℚ Vℚ] {ιℚ : V →ₗ[ℤ] Vℚ}

/-- On an integral vector and a purely rational vector the complexified form takes the value of
the rationalified form. -/
private theorem integralFormBaseChange_rationalToComplexLinearEquiv_ι (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (Q : LinearMap.BilinForm ℤ V) (v : V) (y : Vℚ) :
    integralFormBaseChange hℂ Q (ιℂ v) (rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] y)) =
      ((integralFormBaseChange hℚ Q (ιℚ v) y : ℚ) : ℂ) := by
  induction y using hℚ.inductionOn with
  | zero => simp
  | tmul w => simp
  | smul q y hy =>
      simp [TensorProduct.tmul_smul, ← algebraMap_smul ℂ q, map_smul, hy]
  | add y₁ y₂ h₁ h₂ =>
      simp [TensorProduct.tmul_add, h₁, h₂]

/-- The two scalar extensions of an integral form agree: on purely rational vectors of the
complexification, the complexified form takes the values of the rationalified form. -/
theorem integralFormBaseChange_rationalToComplexLinearEquiv_one_tmul (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (Q : LinearMap.BilinForm ℤ V) (x y : Vℚ) :
    integralFormBaseChange hℂ Q (rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] x))
        (rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] y)) =
      ((integralFormBaseChange hℚ Q x y : ℚ) : ℂ) := by
  induction x using hℚ.inductionOn generalizing y with
  | zero => simp
  | tmul v => simpa using integralFormBaseChange_rationalToComplexLinearEquiv_ι hℚ hℂ Q v y
  | smul q x hx =>
      simp [TensorProduct.tmul_smul, ← algebraMap_smul ℂ q, map_smul, hx]
  | add x₁ x₂ h₁ h₂ =>
      simp [TensorProduct.tmul_add, h₁, h₂]

end Rational

end TauCeti.Hodge
