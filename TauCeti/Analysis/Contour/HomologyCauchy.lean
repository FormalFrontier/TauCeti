/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.Dixon.Def
public import TauCeti.Analysis.Contour.PiecewiseC1On
import TauCeti.Analysis.Contour.Cauchy.IntegralFormula
import TauCeti.Analysis.Contour.Curve.Distance
import TauCeti.Analysis.Contour.Dixon.FunctionDiff
import TauCeti.Analysis.Contour.Dixon.Liouville

/-!
# The homology Cauchy theorem, via Dixon's argument

Dixon's argument in `DixonLiouville` proves that the glued Dixon function vanishes for a closed
null-homologous curve. `CauchyIntegralFormula` then extracts two algebraic consequences from
pointwise vanishing. This file packages the direct null-homologous forms and assembles the summit:

* `dixonH2_eq_windingNumber_mul_f_of_nullHomologous` — Cauchy's integral formula at an off-curve
  point of the domain.
* `homologyCauchyTheorem_of_point_off_curve` — the contour integral of a holomorphic function
  around such a closed null-homologous curve is zero, assuming an off-curve point in the domain is
  supplied.
* `homologyCauchyTheorem` — **the homology form of Cauchy's theorem** (roadmap
  `homologyCauchyTheorem`, `TauCetiRoadmap/ContourIntegration/Suggested.lean`, Layer 3): for a
  closed piecewise-`C¹` curve `γ`, null-homologous in an open `Ω`, and `f` holomorphic on `Ω`,
  the contour integral `∫ t in a..b, deriv γ t • f (γ t)` vanishes. The piecewise-`C¹` regularity
  discharges the integrand-level hypotheses via the `IsPiecewiseC1On` API, and the base point off
  the curve comes from `exists_mem_off_curve`.

## Provenance

These are the final assembly steps of Dixon's proof, migrated from the AINTLIB
`LeanModularForms` development (`DixonTheorem.lean`) and restated for the raw curve
`γ : ℝ → ℂ` used by the contour-integration roadmap. See J. D. Dixon, *A brief proof of Cauchy's
integral theorem*, Proc. Amer. Math. Soc. 29 (1971).
-/

public section

open Complex MeasureTheory Set

open scoped Real Interval

namespace TauCeti.Contour

/-- **Null-homologous Cauchy integral formula at an off-curve point.** Let `γ` be a closed curve in
an open set `U`, continuous on `uIcc a b`, differentiable off a countable set, with
interval-integrable derivative, and null-homologous in `U`. If `f` is holomorphic on `U` and
`w ∈ U` is not on the curve, then the Cauchy-type integral evaluates to
`2πi · windingNumber γ a b w · f w`.

This is the Cauchy-integral-formula output of Dixon's vanishing theorem. The off-curve point is
kept as an explicit hypothesis; proving that such a point exists in the ambient domain is a separate
geometric prerequisite for the full global homology Cauchy theorem. -/
theorem dixonH2_eq_windingNumber_mul_f_of_nullHomologous {f : ℂ → ℂ} {U : Set ℂ}
    {γ : ℝ → ℂ} {a b : ℝ} {P : Set ℝ} {w : ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) (hclosed : γ a = γ b)
    (hP : P.Countable) (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (h_null : IsNullHomologous γ a b U) (hwU : w ∈ U) (hoff : ∀ t ∈ uIcc a b, γ t ≠ w) :
    dixonH2 f γ a b w = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b w * f w :=
  dixonH2_eq_windingNumber_mul_f_of_dixonFunction_eq_zero hγ_cont hwU hoff
    (dixonFunction_eq_zero hU hf hγ_cont hγU hderiv_int hclosed hP hγ_diff h_null w)
    (cauchy_integrand_intervalIntegrable hf.continuousOn hγ_cont hγU hderiv_int hoff)
    (intervalIntegrable_inv_sub_mul_deriv hγ_cont hoff hderiv_int)

/-- **Homology Cauchy theorem with a supplied off-curve point.** Let `γ` be a closed curve in an
open set `U`, continuous on `uIcc a b`, differentiable off a countable set, with
interval-integrable derivative, and null-homologous in `U`. If `f` is holomorphic on `U` and `U`
contains a point `w₀` not lying on the curve, then
`∫ t in a..b, deriv γ t • f (γ t) = 0`. The integrand-level form of the homology Cauchy theorem;
`homologyCauchyTheorem` below supplies the off-curve point and discharges the regularity from
`IsPiecewiseC1On`. -/
theorem homologyCauchyTheorem_of_point_off_curve {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ}
    {a b : ℝ} {P : Set ℝ} {w₀ : ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) (hclosed : γ a = γ b)
    (hP : P.Countable) (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (h_null : IsNullHomologous γ a b U) (hw₀U : w₀ ∈ U) (hw₀off : ∀ t ∈ uIcc a b, γ t ≠ w₀) :
    ∫ t in a..b, deriv γ t • f (γ t) = 0 := by
  have hg : DifferentiableOn ℂ (fun z ↦ (z - w₀) * f z) U := by
    fun_prop
  have h_int_mul : IntervalIntegrable (fun t ↦ f (γ t) * deriv γ t) volume a b :=
    hderiv_int.continuousOn_mul (hf.continuousOn.comp hγ_cont hγU)
  have h_int : IntervalIntegrable (fun t ↦ deriv γ t • f (γ t)) volume a b := by
    rw [intervalIntegrable_iff] at h_int_mul ⊢
    exact h_int_mul.congr_fun (fun t _ ↦ by rw [smul_eq_mul, mul_comm]) measurableSet_uIoc
  exact intervalIntegral_deriv_smul_eq_zero_of_dixonFunction_eq_zero hγ_cont w₀ hw₀U hw₀off
    (dixonFunction_eq_zero hU hg hγ_cont hγU hderiv_int hclosed hP hγ_diff h_null w₀)
    h_int (intervalIntegrable_inv_sub_mul_deriv hγ_cont hw₀off hderiv_int)

/-- **The homology Cauchy theorem** (roadmap `homologyCauchyTheorem`, Layer 3). Let `γ` be a
closed piecewise-`C¹` curve on `[[a, b]]`, null-homologous in an open set `Ω` containing it, and
let `f` be holomorphic on `Ω`. Then the contour integral of `f` along `γ` vanishes:
`∫ t in a..b, deriv γ t • f (γ t) = 0`.

Dixon's argument: the piecewise-`C¹` regularity supplies continuity, differentiability off the
finitely many breakpoints, and interval-integrability of `deriv γ` (the `IsPiecewiseC1On` API);
the compact curve image cannot exhaust the open `Ω`, giving a base point `w₀ ∈ Ω` off the curve
(`exists_mem_off_curve`); and `homologyCauchyTheorem_of_point_off_curve` — vanishing of the glued
Dixon function by Liouville, then the Cauchy integral formula at `w₀` — concludes. -/
theorem homologyCauchyTheorem {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω) (γ : ℝ → ℂ) (a b : ℝ)
    (hγ_pc1 : IsPiecewiseC1On γ a b) (hγ : ∀ t ∈ uIcc a b, γ t ∈ Ω) (hclosed : γ a = γ b)
    (hf : DifferentiableOn ℂ f Ω) (hnull : IsNullHomologous γ a b Ω) :
    ∫ t in a..b, deriv γ t • f (γ t) = 0 := by
  obtain ⟨P, hP, hγ_diff⟩ := hγ_pc1.exists_countable_differentiableAt
  obtain ⟨w₀, hw₀Ω, hw₀off⟩ := exists_mem_off_curve hΩ hγ_pc1.continuousOn hγ
  exact homologyCauchyTheorem_of_point_off_curve hΩ hf hγ_pc1.continuousOn hγ
    hγ_pc1.intervalIntegrable_deriv hclosed hP hγ_diff hnull hw₀Ω hw₀off

end TauCeti.Contour

end
