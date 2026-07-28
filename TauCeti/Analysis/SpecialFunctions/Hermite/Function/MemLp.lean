module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Basic
public import TauCeti.Probability.Distributions.Gaussian.PolynomialMemLp

/-!
# Integrability, `L²` membership, and normalization of the Hermite functions

This file continues the object API for the Hermite functions
`ψₙ(x) = Hₙ(x√2) exp(-x²/2) / √(n!√π)` (`TauCeti.hermiteFunction`), adding the regularity facts
the `OrthogonalL2Bases` roadmap's **A2** milestone lists and its **A3** basis construction consumes:

* `TauCeti.integrable_hermiteFunction` — every `ψₙ` is integrable against Lebesgue measure;
* `TauCeti.memLp_two_hermiteFunction` — every `ψₙ` is in `L²(volume)`, the membership the
  `hermiteFunctionLp`/`hermiteHilbertBasis` layer needs to package `ψₙ` as an `Lp` element.
* `TauCeti.integral_hermiteFunction_zero_mul_self` — the zeroth Hermite function has square
  integral one.

The membership results use the reusable engine
`TauCeti.integrable_eval_mul_gaussianEnvelope`: a real polynomial evaluated pointwise, times a
Gaussian envelope `exp(-(x - μ)²/(2v))` of any center `μ` and positive variance `v`, is
Lebesgue-integrable. It is obtained by transporting the polynomial's integrability against the
Gaussian *measure* `gaussianReal μ v` (all of whose moments are finite,
`TauCeti.integrable_pow_gaussianReal`, so `TauCeti.integrable_eval_of_forall_integrable_pow`
applies) across the change of variables `gaussianReal μ v = volume.withDensity (gaussianPDF μ v)`
with `integrable_withDensity_iff`. Applied to the polynomial `Hₙ(·√2)` with `v = 1` this gives the
`L¹` membership, and to its square with `v = ½` (whose envelope `exp(-x²)` is `ψₙ²` up to the
constant) the `L²` membership. The zeroth-mode normalization additionally uses Mathlib's Gaussian
density normalization `integral_gaussianPDFReal_eq_one`.

Mathlib's Gaussian density API (`gaussianReal_of_var_ne_zero`, `measurable_gaussianPDF`,
`gaussianPDFReal_def`), `integrable_withDensity_iff`, `memLp_two_iff_integrable_sq`, and the
`Polynomial` evaluation API are consumed, not re-derived.
-/

public section

namespace TauCeti

open MeasureTheory ProbabilityTheory Polynomial

open scoped NNReal ENNReal

/-! ## `L¹` and `L²` membership of the Hermite functions -/

/-- The polynomial `Hₙ(·√2)`, real-evaluated, as a composition whose `eval` is `aeval (·√2)`. -/
private lemma eval_hermiteComp (n : ℕ) (x : ℝ) :
    (((hermite n).map (Int.castRingHom ℝ)).comp (X * Polynomial.C (Real.sqrt 2))).eval x
      = aeval (x * Real.sqrt 2) (hermite n) := by
  rw [eval_comp, eval_mul, eval_X, eval_C, aeval_def, algebraMap_int_eq, ← eval_map]

/-- **Target A2 (`L¹`).** Each Hermite function is integrable against Lebesgue measure: it is a
polynomial in `x` times the Gaussian envelope `exp(-x²/2)`, the `v = 1` case of
`integrable_eval_mul_gaussianEnvelope`. -/
theorem integrable_hermiteFunction (n : ℕ) : Integrable (hermiteFunction n) volume := by
  have h := integrable_eval_mul_gaussianEnvelope 0
    (((hermite n).map (Int.castRingHom ℝ)).comp (X * Polynomial.C (Real.sqrt 2))) (w := 1)
    one_ne_zero
  have exponent_one :
      ∀ x : ℝ, (-(x ^ 2 / 2) : ℝ) = -(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)) := by
    intro x
    push_cast
    ring
  have hfun : hermiteFunction n = fun x =>
      (((hermite n).map (Int.castRingHom ℝ)).comp (X * Polynomial.C (Real.sqrt 2))).eval x
        * Real.exp (-(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)))
        / Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) := by
    funext x
    rw [hermiteFunction_def, ← eval_hermiteComp, exponent_one x]
  rw [hfun]
  exact h.div_const _

/-- **Target A2 (`L²`).** Each Hermite function lies in `L²(volume)`. Its square is
`(Hₙ(x√2))² exp(-x²)` up to the constant `(n!√π)`, integrable by `integrable_eval_mul_exp_neg_sq`,
and `L²` membership is integrability of the square (`memLp_two_iff_integrable_sq`). This is the
membership `hermiteFunctionLp` needs to realize `ψₙ` as an element of `Lp ℝ 2 volume`. -/
theorem memLp_two_hermiteFunction (n : ℕ) : MemLp (hermiteFunction n) 2 volume := by
  rw [memLp_two_iff_integrable_sq (continuous_hermiteFunction n).aestronglyMeasurable]
  have hfun : (fun x => hermiteFunction n x ^ 2) = fun x =>
      ((((hermite n).map (Int.castRingHom ℝ)).comp (X * Polynomial.C (Real.sqrt 2))) ^ 2).eval x
        * Real.exp (-x ^ 2)
        / Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) ^ 2 := by
    funext x
    have henv : Real.exp (-(x ^ 2 / 2)) ^ 2 = Real.exp (-x ^ 2) := by
      rw [pow_two, ← Real.exp_add]; congr 1; ring
    rw [hermiteFunction_def, div_pow, mul_pow, henv, eval_pow, eval_hermiteComp]
  rw [hfun]
  exact (integrable_eval_mul_exp_neg_sq _).div_const _

/-! ## Zeroth-mode normalization -/

private lemma integral_hermiteFunction_zero_mul_self_expanded :
    ∫ x : ℝ, Real.exp (-(x ^ 2 / 2)) / Real.sqrt (Real.sqrt Real.pi) *
      (Real.exp (-(x ^ 2 / 2)) / Real.sqrt (Real.sqrt Real.pi)) = 1 := by
  -- The integrand is the normalized Gaussian density `gaussianPDFReal 0 (1/2)`, so this is the
  -- `μ = 0`, `v = 1/2` case of Mathlib's `integral_gaussianPDFReal_eq_one`.
  rw [← integral_gaussianPDFReal_eq_one 0 (v := (1 / 2 : ℝ≥0)) (by norm_num)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hden : Real.sqrt (Real.sqrt Real.pi) * Real.sqrt (Real.sqrt Real.pi) =
      Real.sqrt Real.pi := Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hexp : Real.exp (-(x ^ 2 / 2)) * Real.exp (-(x ^ 2 / 2)) = Real.exp (-x ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hv : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by push_cast; ring
  have hpi : (2 : ℝ) * Real.pi * (1 / 2) = Real.pi := by ring
  have htwo : (2 : ℝ) * (1 / 2) = 1 := by ring
  simp only [gaussianPDFReal]
  rw [div_mul_div_comm, hexp, hden, hv, sub_zero, hpi, htwo, div_one, div_eq_inv_mul]

/-- The zeroth Hermite function has square integral one. This is the `n = 0` boundary case of
the roadmap's Hermite-function orthonormality target. -/
lemma integral_hermiteFunction_zero_mul_self :
    ∫ x : ℝ, hermiteFunction 0 x * hermiteFunction 0 x = 1 := by
  simpa only [hermiteFunction_zero] using integral_hermiteFunction_zero_mul_self_expanded

end TauCeti
