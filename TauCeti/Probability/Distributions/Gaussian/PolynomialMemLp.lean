module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import Mathlib.Probability.Distributions.Gaussian.Real
public import TauCeti.MeasureTheory.Function.PolynomialMemLp

/-!
# Integrability and `L²` membership of polynomials against a Gaussian measure

This file collects the family-agnostic facts that a real polynomial, evaluated pointwise, is
integrable and square-integrable against a real Gaussian measure `gaussianReal μ v`, together with
the companion statement that a polynomial times a Gaussian *envelope* `exp (-(x - μ)²/(2v))` is
Lebesgue-integrable.  These hold for **any** `q : ℝ[X]` and feed the Hermite-specific `L²`
membership in `TauCeti.Probability.Distributions.Gaussian.HermiteMemLp` and the Hermite-function
integrability in `TauCeti.Analysis.SpecialFunctions.Hermite.Function.MemLp`.

The `L²` argument factors through the family-agnostic `memLp_two_eval_of_forall_integrable_pow`
(`TauCeti.MeasureTheory.Function.PolynomialMemLp`), which holds for any reference measure on `ℝ`
all of whose polynomial moments are finite.  The Gaussian instance supplies that moment hypothesis
`∀ k, Integrable (x ↦ xᵏ)` from Mathlib's `memLp_id_gaussianReal'` (all moments of a real Gaussian
are finite).  The envelope statement transports the polynomial's integrability against the Gaussian
measure across `gaussianReal μ v = volume.withDensity (gaussianPDF μ v)`.

Mathlib's `memLp_id_gaussianReal'` (Fernique) and Gaussian density API
(`gaussianReal_of_var_ne_zero`, `measurable_gaussianPDF`, `gaussianPDFReal_def`) are consumed, not
re-derived.
-/

public section

namespace TauCeti

open MeasureTheory ProbabilityTheory Polynomial

open scoped NNReal ENNReal

/-! ## The Gaussian instance -/

/-- Every polynomial moment of a real Gaussian measure is finite: `x ↦ xⁿ` is integrable against
`gaussianReal μ v`.  This is `memLp_id_gaussianReal'` (all moments finite) unwound to plain
integrability of the power. -/
theorem integrable_pow_gaussianReal (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal μ v) := by
  have h : Integrable (fun x : ℝ => ‖x‖ ^ n) (gaussianReal μ v) := by
    simpa using
      (memLp_id_gaussianReal' (μ := μ) (v := v) (n : ℝ≥0∞) (by simp)).integrable_norm_pow'
  rw [← integrable_norm_iff (continuous_pow n).aestronglyMeasurable]
  simpa only [norm_pow] using h

/-- A real polynomial is square-integrable against every real Gaussian measure. -/
theorem memLp_two_eval_gaussianReal (μ : ℝ) (v : ℝ≥0) (q : ℝ[X]) :
    MemLp (fun x : ℝ => q.eval x) 2 (gaussianReal μ v) :=
  memLp_two_eval_of_forall_integrable_pow (fun k => integrable_pow_gaussianReal μ v k) q

/-! ## Polynomial times a Gaussian envelope -/

/-- A real polynomial evaluated pointwise, times a Gaussian envelope
`exp (-(x - μ)²/(2v))` of positive variance `v` centered at `μ`, is Lebesgue-integrable.
Transported from the polynomial's integrability against the Gaussian measure `gaussianReal μ v`
across `gaussianReal μ v = volume.withDensity (gaussianPDF μ v)`. -/
theorem integrable_eval_mul_gaussianEnvelope (μ : ℝ) (q : ℝ[X]) {w : ℝ≥0} (hw : w ≠ 0) :
    Integrable (fun x : ℝ => q.eval x * Real.exp (-(x - μ) ^ 2 / (2 * (w : ℝ)))) volume := by
  have hint : Integrable (fun x : ℝ => q.eval x) (gaussianReal μ w) :=
    integrable_eval_of_forall_integrable_pow (fun k => integrable_pow_gaussianReal μ w k) q
  rw [gaussianReal_of_var_ne_zero μ hw,
    integrable_withDensity_iff (measurable_gaussianPDF μ w)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at hint
  simp only [toReal_gaussianPDF] at hint
  have hw' : (0 : ℝ) < (w : ℝ) := NNReal.coe_pos.mpr (zero_lt_iff.mpr hw)
  have hsqrt : Real.sqrt (2 * Real.pi * (w : ℝ)) ≠ 0 :=
    (Real.sqrt_pos.mpr (by positivity)).ne'
  refine (hint.const_mul (Real.sqrt (2 * Real.pi * (w : ℝ)))).congr (ae_of_all _ fun x => ?_)
  simp only [gaussianPDFReal_def]
  field_simp

/-- A real polynomial times the envelope `exp(-x²)` is Lebesgue-integrable — the centered
`v = ½` case of `integrable_eval_mul_gaussianEnvelope`. -/
theorem integrable_eval_mul_exp_neg_sq (q : ℝ[X]) :
    Integrable (fun x : ℝ => q.eval x * Real.exp (-x ^ 2)) volume := by
  have h := integrable_eval_mul_gaussianEnvelope 0 q (w := 2⁻¹) (by norm_num)
  have he : (2 : ℝ) * ((2⁻¹ : ℝ≥0) : ℝ) = 1 := by push_cast; norm_num
  simpa only [sub_zero, he, div_one] using h

end TauCeti
