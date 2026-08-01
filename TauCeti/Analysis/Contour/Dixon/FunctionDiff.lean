/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.Dixon.Def
import TauCeti.Analysis.Contour.Dixon.H1Diff
import TauCeti.Analysis.Contour.Dixon.H2.Diff
import TauCeti.Analysis.Contour.Winding.LocallyConstant

/-!
# The Dixon function is entire

Dixon's glued function `dixonFunction f U γ a b` — equal to `dixonH1` on `U` and `dixonH2` off `U`
— is complex-differentiable on all of `ℂ` when `f` is holomorphic on the open set `U` and the
curve `γ` lives in `U`, is null-homologous there, is closed, and is differentiable off a countable
set with interval-integrable derivative. On `U`
it agrees with the holomorphic `dixonH1`; off `U` (hence off the curve) it agrees with the
holomorphic `dixonH2`, and the two pieces match across `∂U` because the winding number vanishes
there, so the `h₁`/`h₂` identity collapses.

## Main results

* `TauCeti.Contour.differentiable_dixonFunction` — `dixonFunction f U γ a b` is entire for a
  null-homologous closed curve. It is built from a private gluing core that takes the off-`U`
  winding-vanishing hypothesis directly, which the null-homologous case then discharges.
* `TauCeti.Contour.dixonFunction_eq_dixonH2_of_windingNumber_zero` — off the curve with winding
  number `0` and the Cauchy integrand integrable, `dixonFunction` equals `dixonH2` (the pointwise
  gluing fact used here and downstream).
* `TauCeti.Contour.cauchy_integrand_intervalIntegrable` — the `dixonH2` integrand
  `f (γ ·) / (γ · - w) · deriv γ` is interval-integrable for `w` off the curve (discharges the
  integrand hypothesis above, needing only `f` continuous on `U`).

This is the analyticity input to the Liouville step of Dixon's proof of the homology form of
Cauchy's theorem (`homologyCauchyTheorem`, `TauCetiRoadmap/ContourIntegration/Suggested.lean`).

## Provenance

Adapted from `dixonFunction_differentiable` in `DixonDiff.lean` of the AINTLIB `LeanModularForms`
development, restated for a raw `γ : ℝ → ℂ` on an oriented interval. See J. D. Dixon, *A brief proof
of Cauchy's integral theorem* (1971).
-/

public section

open Complex MeasureTheory Set

open scoped Real Interval Topology

namespace TauCeti.Contour

section

variable {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ} {P : Set ℝ} {w : ℂ}

/-- **The Cauchy-type integrand is interval-integrable.** `f (γ ·) / (γ · - w) · deriv γ` is
interval-integrable for `w` off the curve: a continuous factor (using `f` continuous on `U ⊇ γ`,
`γ` continuous, and `γ` avoiding `w`) times the interval-integrable derivative. This is the
integrand of `dixonH2 f γ a b w`, and supplies the `h_cauchy_int` hypothesis of
`dixonH1_eq_dixonH2_sub_windingNumber_mul_f` and of
`dixonFunction_eq_dixonH2_of_windingNumber_zero`; in Dixon's application `f` is holomorphic on `U`,
but only continuity is used here. -/
theorem cauchy_integrand_intervalIntegrable (hf : ContinuousOn f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b)
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ w) :
    IntervalIntegrable (fun t ↦ f (γ t) / (γ t - w) * deriv γ t) volume a b :=
  hderiv_int.continuousOn_mul (((hf.comp hγ_cont hγU).div
    (hγ_cont.sub continuousOn_const) fun t ht ↦ sub_ne_zero.mpr (hoff t ht)))

/-- **Off the curve with vanishing winding number, `dixonFunction` equals `dixonH2`.** For `w` off
the curve with `windingNumber γ a b w = 0` and the Cauchy integrand `f (γ ·) / (γ · - w) · deriv γ`
interval-integrable, the two branches of `dixonFunction` agree: on `U` the `h₁`/`h₂` identity
collapses because the winding term vanishes, and off `U` it is `dixonH2` by definition. Only
integrability is needed, not holomorphy of `f`; when `f` is differentiable on `U ⊇ γ` the integrand
hypothesis is discharged by `cauchy_integrand_intervalIntegrable`. This is the pointwise gluing fact
shared by the analyticity of `dixonFunction` and its vanishing at infinity. -/
theorem dixonFunction_eq_dixonH2_of_windingNumber_zero (hγ_cont : ContinuousOn γ (uIcc a b))
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b)
    (h_cauchy_int : IntervalIntegrable (fun t ↦ f (γ t) / (γ t - w) * deriv γ t) volume a b)
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ w) (hwn : windingNumber γ a b w = 0) :
    dixonFunction f U γ a b w = dixonH2 f γ a b w := by
  by_cases hw : w ∈ U
  · rw [dixonFunction_eq_dixonH1 hw, dixonH1_eq_dixonH2_sub_windingNumber_mul_f hγ_cont hoff
      h_cauchy_int (intervalIntegrable_inv_sub_mul_deriv hγ_cont hoff hderiv_int), hwn]
    ring
  · rw [dixonFunction_eq_dixonH2 hw]

/-- **Analytic gluing of the Dixon function.** If `f` is differentiable on the open set `U`, the
curve `γ` is continuous on `uIcc a b` with image in `U` and interval-integrable derivative, and
around every point `w ∉ U` the winding number vanishes on an entire ball that stays off the curve,
then `dixonFunction f U γ a b` is complex-differentiable on all of `ℂ`. On `U` it agrees with the
holomorphic `dixonH1`; off `U` (hence off the curve) it agrees with the holomorphic `dixonH2`, and
the two pieces match across `∂U` because the local winding hypothesis collapses the `h₁`/`h₂`
identity. This is the gluing core; `differentiable_dixonFunction` discharges the local hypothesis
for a null-homologous closed curve. -/
private theorem differentiable_dixonFunction_of_windingNumber_zero_near (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b)
    (h_local : ∀ w ∉ U, ∃ ε > 0, ∀ w' ∈ Metric.ball w ε,
      (∀ t ∈ uIcc a b, γ t ≠ w') ∧ windingNumber γ a b w' = 0) :
    Differentiable ℂ (dixonFunction f U γ a b) := by
  intro w
  by_cases hw : w ∈ U
  · refine ((differentiableOn_dixonH1 hU hf hγ_cont hγU hderiv_int).differentiableAt
      (hU.mem_nhds hw)).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hw] with w' hw' using dixonFunction_eq_dixonH1 hw'
  · have hoff : ∀ t ∈ uIcc a b, γ t ≠ w := fun t ht heq ↦ hw (heq ▸ hγU t ht)
    obtain ⟨ε, hε_pos, h_ball⟩ := h_local w hw
    refine (differentiableAt_dixonH2 hγ_cont hoff
      (cauchy_integrand_intervalIntegrable hf.continuousOn hγ_cont hγU hderiv_int
        hoff)).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds w hε_pos] with w' hw'
    obtain ⟨hoff', hwz'⟩ := h_ball w' hw'
    exact dixonFunction_eq_dixonH2_of_windingNumber_zero hγ_cont hderiv_int
      (cauchy_integrand_intervalIntegrable hf.continuousOn hγ_cont hγU hderiv_int hoff') hoff' hwz'

/-- **The Dixon function is entire.** For `f` differentiable on the open set `U`, a closed curve `γ`
that is continuous on `uIcc a b`, differentiable off a countable subset, with interval-integrable
derivative, image in `U`, and null-homologous in `U`, the glued function `dixonFunction f U γ a b`
is complex-differentiable on all of `ℂ`. This specialises
`differentiable_dixonFunction_of_windingNumber_zero_near`, discharging its local winding hypothesis
via `exists_ball_windingNumber_zero`. -/
theorem differentiable_dixonFunction (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) (hclosed : γ a = γ b)
    (hP : P.Countable) (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (h_null : IsNullHomologous γ a b U) :
    Differentiable ℂ (dixonFunction f U γ a b) :=
  differentiable_dixonFunction_of_windingNumber_zero_near hU hf hγ_cont hγU hderiv_int
    fun w hw ↦ exists_ball_windingNumber_zero hclosed hP hγ_cont hγ_diff hderiv_int
      (fun t ht heq ↦ hw (heq ▸ hγU t ht)) ((isNullHomologous_iff.mp h_null) w hw)

end

end TauCeti.Contour
