/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import TauCeti.Analysis.Bochner.CharFun.PositiveDefinite
public import TauCeti.Analysis.PositiveDefinite.FourierAtom
public import TauCeti.Analysis.PositiveDefinite.Pullback

/-!
# Fourier-convention characteristic functions

Mathlib's characteristic function of a finite measure is
`t ↦ ∫ x, exp (⟪x, t⟫ * I) ∂μ`, while the Fourier side of the Bochner roadmap uses the
`2π` convention `a ↦ ∫ q, exp (-2πi⟪a, q⟫) ∂μ`. This file records the conversion between these
normalizations and then reuses the existing characteristic-function API to show that the
Fourier-convention transform of a finite measure is continuous and positive definite.

The file also bridges Mathlib's Fourier transform `𝓕` to the Fourier atom, and it carries the
measure-uniqueness theorem — the uniqueness half of Bochner's theorem — consumed by
`BochnerTheorem.lean`. The convention-free continuity of `𝓕` and `𝓕⁻` lives in
`TauCeti.Analysis.Fourier.Continuous`.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, the positive-definite
function API item asking for "a stated Fourier-convention conversion lemma between Mathlib's
`2π` form and the characteristic-function form" before Bochner's theorem.

## Main declarations

* `TauCeti.integral_fourierAtom_eq_charFun_neg_two_pi_smul`: the Fourier-convention integral is
  `charFun μ ((-2π) • a)`.
* `TauCeti.fourier_eq_integral_fourierAtom_mul`: the Fourier transform `𝓕 F` is the
  integral of `F` against the Fourier atom.
* `TauCeti.posSemidef_fourierConventionCharFun_sub`: the Fourier-convention
  translation-invariant kernel of a finite measure is positive definite.
* `TauCeti.Measure.ext_of_forall_integral_fourierAtom_eq`: a finite measure is determined by its
  Fourier-convention transform — the uniqueness half of Bochner's theorem.

## References

* Mathlib's `MeasureTheory.charFun` and Fourier transform convention in
  `Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic` and
  `Mathlib.Analysis.Fourier.FourierTransform`.
-/

public section

open MeasureTheory Complex
open scoped ComplexOrder FourierTransform

namespace TauCeti

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] {μ : Measure V}

/-- The Fourier-convention integral of a finite measure, written in exponential normal form,
is Mathlib's characteristic function evaluated at `(-2π) • a`. -/
@[simp]
theorem integral_exp_neg_two_pi_inner_eq_charFun_neg_two_pi_smul (a : V) :
    ∫ q, Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ q a : ℝ))) ∂μ =
      MeasureTheory.charFun μ ((-2 * Real.pi) • a) := by
  rw [MeasureTheory.charFun_apply]
  refine integral_congr_ae (.of_forall fun q => ?_)
  simp only [inner_smul_right, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_neg]
  ring_nf

/-- The Fourier-convention integral of a finite measure, written with the atom
`exp (-2πi⟪a, q⟫)`, is Mathlib's characteristic function evaluated at `(-2π) • a`.

Not a `@[simp]` lemma: `simp` already proves it — `fourierAtom_apply` and `neg_mul` rewrite
the left-hand side into that of the simp lemma
`integral_exp_neg_two_pi_inner_eq_charFun_neg_two_pi_smul`, which the simpNF linter reports
as a duplicate if this statement is also tagged `@[simp]`. -/
theorem integral_fourierAtom_eq_charFun_neg_two_pi_smul (a : V) :
    ∫ q, fourierAtom a q ∂μ = MeasureTheory.charFun μ ((-2 * Real.pi) • a) := by
  simpa only [fourierAtom_apply, neg_mul] using
    integral_exp_neg_two_pi_inner_eq_charFun_neg_two_pi_smul (μ := μ) a

/-- The scaling constant `-2π` of the Fourier convention is nonzero. -/
theorem neg_two_pi_ne_zero : (-2 * Real.pi) ≠ 0 :=
  mul_ne_zero (by norm_num) Real.pi_ne_zero

section FourierIntegral

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]

/-- The Fourier transform written as the integral against the Fourier atom. -/
theorem fourier_eq_integral_fourierAtom_mul (F : U → ℂ) (ξ : U) :
    𝓕 F ξ = ∫ v, fourierAtom ξ v * F v := by
  rw [Real.fourier_eq]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only [Circle.smul_def, smul_eq_mul, fourierAtom_eq_fourierChar]

end FourierIntegral

variable {W : Type*} [SeminormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MeasurableSpace W] [OpensMeasurableSpace W] {ν : Measure W} [IsFiniteMeasure ν]

/-- The Fourier-convention transform of a finite measure is positive definite for any additive
group involution that is explicitly negation. This transports the positive-definiteness of
`charFun μ` through the `-2π` additive rescaling. -/
theorem fourierConventionCharFun_isPositiveDefinite_of_star_eq_neg [StarAddMonoid W]
    (hstar : ∀ x : W, star x = -x) :
    IsPositiveDefinite (fun a : W => ∫ q, fourierAtom a q ∂ν) := by
  have hchar : IsPositiveDefinite fun a : W => MeasureTheory.charFun ν ((-2 * Real.pi) • a) :=
    (charFun_isPositiveDefinite_of_star_eq_neg (μ := ν) hstar).comp_smul hstar (-2 * Real.pi)
  convert hchar using 1
  ext a
  exact integral_fourierAtom_eq_charFun_neg_two_pi_smul (μ := ν) a

/-- The translation-invariant kernel attached to the Fourier-convention transform of a finite
measure is positive definite. This is the kernel form of
`fourierConventionCharFun_isPositiveDefinite_of_star_eq_neg`, avoiding any explicit choice of
involution on the domain. -/
theorem posSemidef_fourierConventionCharFun_sub :
    Matrix.PosSemidef fun a b : W => ∫ q, fourierAtom (a - b) q ∂ν := by
  have h := (posSemidef_charFun (μ := ν)).submatrix (fun a : W => (-2 * Real.pi) • a)
  have heq : Matrix.submatrix
      (Matrix.of fun x y : W => MeasureTheory.charFun ν (x - y))
      (fun a : W => (-2 * Real.pi) • a) (fun a => (-2 * Real.pi) • a) =
      fun a b : W => ∫ q, fourierAtom (a - b) q ∂ν := by
    apply Matrix.ext
    intro a b
    rw [Matrix.submatrix_apply, Matrix.of_apply,
      integral_fourierAtom_eq_charFun_neg_two_pi_smul]
    congr 1
    simp [smul_sub]
  exact heq ▸ h

section Topology

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MeasurableSpace W] [BorelSpace W] {ν : Measure W} [IsFiniteMeasure ν]

/-- The Fourier-convention transform of a finite measure is continuous. This is just Mathlib's
continuity of `charFun`, transported through the `-2π` rescaling. -/
theorem continuous_fourierConventionCharFun [SecondCountableTopology W] :
    Continuous fun a : W => ∫ q, fourierAtom a q ∂ν := by
  have hchar :
      Continuous fun a : W => MeasureTheory.charFun ν ((-2 * Real.pi) • a) :=
    by
      simpa [Function.comp_def] using
        (MeasureTheory.continuous_charFun (μ := ν)).comp
          ((continuous_id : Continuous fun a : W => a).const_smul (-2 * Real.pi))
  convert hchar using 1
  ext a
  exact integral_fourierAtom_eq_charFun_neg_two_pi_smul (μ := ν) a

end Topology

section Uniqueness

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
  [BorelSpace W] [SecondCountableTopology W] [CompleteSpace W]

/-- **Uniqueness half of Bochner's theorem.** Two finite Borel measures with the same
Fourier-convention transform coincide; this is Mathlib's characteristic-function uniqueness
theorem, transported through the `-2π` rescaling. Stated on any complete second-countable real
inner-product space; no finite-dimensionality is needed. -/
theorem Measure.ext_of_forall_integral_fourierAtom_eq {μ ν : Measure W}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ v, ∫ q, fourierAtom v q ∂μ = ∫ q, fourierAtom v q ∂ν) : μ = ν := by
  refine MeasureTheory.Measure.ext_of_charFun (funext fun t => ?_)
  have h' := h ((-2 * Real.pi)⁻¹ • t)
  rwa [integral_fourierAtom_eq_charFun_neg_two_pi_smul,
    integral_fourierAtom_eq_charFun_neg_two_pi_smul, smul_smul,
    mul_inv_cancel₀ neg_two_pi_ne_zero, one_smul] at h'

end Uniqueness

end TauCeti
