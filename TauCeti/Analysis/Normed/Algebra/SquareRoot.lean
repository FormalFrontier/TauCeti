/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import TauCeti.Analysis.Calculus.Bilinear

/-!
# Square roots near the identity in a Banach algebra

Squaring, `a ↦ a * a`, has derivative `x ↦ 2 * x` at the identity of a Banach algebra over `ℝ`,
and that derivative is invertible.  The inverse function theorem therefore produces a smooth
partial inverse near `1`: every element close enough to `1` has a square root close to `1`, the
square root depends smoothly on the element, and it is the *only* square root near `1`, because
squaring is injective there.

This file packages that partial inverse as `TauCeti.sqrtNearOne` together with the three facts
downstream arguments need: it fixes `1`, it is smooth at `1`, and it is a two-sided inverse of
squaring on a neighbourhood of `1`.  The two-sided statements are phrased as `Filter.Eventually`
assertions rather than by exhibiting a neighbourhood, since that is how they get used.

The motivating application is the Morse lemma, in
`TauCeti.Analysis.Calculus.Morse.NormalForm`: the operator `(D²f x)⁻¹ ∘ B v` comparing the
averaged Hessian along a segment with the Hessian at a nondegenerate critical point is close to
the identity, and the change of coordinates flattening `f` is built from its square root.  Nothing
here is a substitute for the continuous functional calculus: `CFC.sqrt` computes the *positive*
square root of a positive element of a C⋆-algebra, whereas what is needed here is a square root
near `1` in a bare Banach algebra, with smooth dependence on the element.

## Main declarations

* `TauCeti.sqrtNearOne`: the local inverse of squaring at the identity.
* `TauCeti.sqrtNearOne_one`, `TauCeti.contDiffAt_sqrtNearOne`: it fixes `1` and is smooth there.
* `TauCeti.eventually_mul_self_sqrtNearOne`: near `1` it is a right inverse of squaring, so its
  value really is a square root.
* `TauCeti.eventually_sqrtNearOne_mul_self`: near `1` it is a left inverse of squaring, which is
  the uniqueness statement: an element close to `1` is recovered from its square.

## References

The construction is the inverse function theorem in Banach spaces, as in
S. Lang, *Real and Functional Analysis*, Chapter XIV.
-/

public section

open Filter Topology

open scoped ContDiff

namespace TauCeti

variable (A : Type*) [NormedRing A] [NormedAlgebra ℝ A]

private theorem hasStrictFDerivAt_mul_self_one :
    HasStrictFDerivAt (fun a : A ↦ a * a)
      ((ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) two_ne_zero) : A ≃L[ℝ] A) :
        A →L[ℝ] A) 1 := by
  have h := TauCeti.ContinuousLinearMap.hasStrictFDerivAt_apply_self
    (ContinuousLinearMap.mul ℝ A) 1
  have he : (ContinuousLinearMap.mul ℝ A).flip 1 + ContinuousLinearMap.mul ℝ A 1 =
      ((ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) two_ne_zero) : A ≃L[ℝ] A) :
        A →L[ℝ] A) := by
    ext a
    simp [two_smul]
  rw [he] at h
  exact h

variable [CompleteSpace A]

/-- The **square root near the identity** of a Banach algebra: the local inverse of squaring
supplied by the inverse function theorem at `1`.  It is only meaningful near `1`; see
`TauCeti.eventually_mul_self_sqrtNearOne`. -/
noncomputable def sqrtNearOne : A → A :=
  (hasStrictFDerivAt_mul_self_one A).localInverse (fun a : A ↦ a * a)
    (ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) two_ne_zero) : A ≃L[ℝ] A) 1

variable {A}

/-- The square root near the identity is analytic at the identity.  This gives a single
neighborhood on which it is smooth to every finite order. -/
theorem analyticAt_sqrtNearOne : AnalyticAt ℝ (sqrtNearOne A) 1 := by
  let e : OpenPartialHomeomorph A A :=
    (hasStrictFDerivAt_mul_self_one A).toOpenPartialHomeomorph (fun a : A ↦ a * a)
  have he : AnalyticAt ℝ e.symm 1 := by
    have hsource : (1 : A) ∈ e.source :=
      (hasStrictFDerivAt_mul_self_one A).mem_toOpenPartialHomeomorph_source
    have hsquare : AnalyticAt ℝ (fun a : A ↦ a * a) 1 := analyticAt_id.mul analyticAt_id
    have hfderiv : fderiv ℝ (e : A → A) 1 =
        (ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) two_ne_zero) : A ≃L[ℝ] A) := by
      simp only [e, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
      rw [(hasStrictFDerivAt_mul_self_one A).hasFDerivAt.fderiv]
    simpa [e] using e.analyticAt_symm' hsource (by simpa [e] using hsquare) hfderiv
  have hlocalInverse : sqrtNearOne A = e.symm :=
    (hasStrictFDerivAt_mul_self_one A).localInverse_def
  rw [hlocalInverse]
  simpa [e] using he

/-- The square root near the identity fixes the identity. -/
@[simp]
theorem sqrtNearOne_one : sqrtNearOne A 1 = 1 := by
  simpa [sqrtNearOne] using (hasStrictFDerivAt_mul_self_one A).localInverse_apply_image
    (f := fun a : A ↦ a * a)
    (f' := (ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) two_ne_zero) : A ≃L[ℝ] A))
      (a := 1)

/-- Near the identity, `TauCeti.sqrtNearOne` really produces a square root. -/
theorem eventually_mul_self_sqrtNearOne :
    ∀ᶠ a in 𝓝 (1 : A), sqrtNearOne A a * sqrtNearOne A a = a := by
  simpa [sqrtNearOne] using (hasStrictFDerivAt_mul_self_one A).eventually_right_inverse
    (f := fun a : A ↦ a * a)
    (f' := (ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) two_ne_zero) : A ≃L[ℝ] A))
      (a := 1)

/-- Near the identity, an element is recovered from its square by `TauCeti.sqrtNearOne`.  This is
the uniqueness half: two elements close to `1` with the same square are equal. -/
theorem eventually_sqrtNearOne_mul_self :
    ∀ᶠ b in 𝓝 (1 : A), sqrtNearOne A (b * b) = b := by
  simpa [sqrtNearOne] using (hasStrictFDerivAt_mul_self_one A).eventually_left_inverse
    (f := fun a : A ↦ a * a)
    (f' := (ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) two_ne_zero) : A ≃L[ℝ] A))
      (a := 1)

/-- The square root near the identity is smooth at the identity. -/
theorem contDiffAt_sqrtNearOne : ContDiffAt ℝ ∞ (sqrtNearOne A) 1 :=
  analyticAt_sqrtNearOne.contDiffAt

/-- The square root near the identity is continuous at the identity. -/
theorem continuousAt_sqrtNearOne : ContinuousAt (sqrtNearOne A) 1 :=
  contDiffAt_sqrtNearOne.continuousAt

end TauCeti
