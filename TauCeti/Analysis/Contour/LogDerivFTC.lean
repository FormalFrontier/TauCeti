/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.Contour.Curve.Integrability
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Fundamental theorem of calculus for a logarithmic-derivative integrand

For a function `f : ℝ → ℂ` continuous on `[a, b]`, differentiable off a countable set `P`, and
staying in `Complex.slitPlane` on `[a, b]`, the principal `Complex.log ∘ f` is a single-valued
antiderivative of the logarithmic-derivative integrand `f' t / f t`, so

`∫ t in a..b, f' t / f t = Complex.log (f b) - Complex.log (f a)`.

Specializing to `f t = (γ t - w) / (γ a - w)` for a curve `γ` avoiding `w` gives the contour form
used downstream, `∫ t in a..b, γ' t / (γ t - w) = Complex.log ((γ b - w) / (γ a - w))`, where the
normalization by `γ a - w` is what keeps the ratio in the slit plane and makes the value at the
basepoint `a` equal to `Complex.log 1 = 0`. The exceptional set `P` accommodates the finitely many
breakpoints of a piecewise-`C¹` contour, and the oriented interval `[a, b]` needs no `a ≤ b`
assumption.

Specializing the other way, to `f = h ∘ γ` for a piecewise-`C¹` curve `γ` and an analytic `h`,
gives the curve form of the same principle: if `h` takes its values along `γ` in
`Complex.slitPlane`, then `Complex.log ∘ h ∘ γ` is a single-valued primitive of the
argument-principle integrand `deriv γ • (logDeriv h ∘ γ)`, so that integral is an endpoint
difference — in particular it vanishes on a closed curve. This is the corner-tolerant replacement
for `circleIntegral.integral_eq_zero_of_hasDerivWithinAt`, which needs a genuinely differentiable
contour.

## Main results

* `TauCeti.Contour.analyticAt_logDeriv_of_analyticAt` — `logDeriv f` is analytic wherever `f` is
  analytic and nonzero; the regularity input shared by the results below and by the argument
  principle.
* `TauCeti.Contour.integral_deriv_div_eq_log_sub_log` — the slit-plane logarithmic-derivative FTC in
  general `f' / f` form.
* `TauCeti.Contour.integral_deriv_div_sub_eq_log` — its contour specialization to
  `f t = (γ t - w) / (γ a - w)`, the per-segment step for evaluating the winding-number integral as
  a sum of `Complex.log` argument increments.
* `TauCeti.Contour.integral_inv_sub_mul_deriv_eq_log` — the `deriv γ` form with the winding-integral
  integrand `(γ t - w)⁻¹ * deriv γ t`, ready for the downstream winding sum.
* `TauCeti.Contour.intervalIntegrable_deriv_smul_logDeriv` — interval-integrability of the
  argument-principle integrand `deriv γ • (logDeriv h ∘ γ)` along a piecewise-`C¹` curve.
* `TauCeti.Contour.integral_deriv_smul_logDeriv_eq_zero_of_mem_slitPlane` — that integral vanishes
  along a closed piecewise-`C¹` curve on which `h` is analytic and slit-plane-valued.

## Provenance

Adapted from `segment_log_FTC` in `WindingInteger.lean` of the AINTLIB `LeanModularForms`
development, split from the argument-lift PR (#759) as an independent contour prerequisite.
-/

public section

open Complex MeasureTheory Set intervalIntegral

open scoped Interval

namespace TauCeti.Contour

/-- **Logarithmic-derivative FTC on the slit plane.** For `f` continuous on `[a, b]`, differentiable
off a countable set `P`, taking values in `Complex.slitPlane` throughout `[a, b]`, and with `f' / f`
interval-integrable, the integral of `f' t / f t` over `a..b` telescopes through the single-valued
branch `Complex.log ∘ f`:
`∫ t in a..b, f' t / f t = Complex.log (f b) - Complex.log (f a)`. -/
theorem integral_deriv_div_eq_log_sub_log {f f' : ℝ → ℂ} {a b : ℝ} {P : Set ℝ}
    (hP : P.Countable) (hf_cont : ContinuousOn f (uIcc a b))
    (hf_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, HasDerivAt f (f' t) t)
    (h_slit : ∀ t ∈ uIcc a b, f t ∈ slitPlane)
    (h_int : IntervalIntegrable (fun t ↦ f' t / f t) volume a b) :
    ∫ t in a..b, f' t / f t = Complex.log (f b) - Complex.log (f a) :=
  integral_eq_of_hasDerivAt_off_countable (fun t ↦ Complex.log (f t)) (fun t ↦ f' t / f t) hP
    (hf_cont.clog h_slit)
    (fun t ht ↦ (hf_diff t ht).clog_real (h_slit t (Ioo_subset_Icc_self ht.1))) h_int

/-- **FTC for a contour logarithmic-derivative integrand.** The `f t = (γ t - w) / (γ a - w)`
specialization of `integral_deriv_div_eq_log_sub_log`: for `γ` continuous on `[a, b]` and
differentiable off a countable set `P`, with the normalized ratio in `Complex.slitPlane` throughout
`[a, b]` and `t ↦ γ' t / (γ t - w)` interval-integrable, the integral of that integrand over `a..b`
equals `Complex.log ((γ b - w) / (γ a - w))`. -/
theorem integral_deriv_div_sub_eq_log {γ γ' : ℝ → ℂ} {w : ℂ} {a b : ℝ} {P : Set ℝ}
    (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, HasDerivAt γ (γ' t) t)
    (h_slit : ∀ t ∈ uIcc a b, (γ t - w) / (γ a - w) ∈ slitPlane)
    (h_int : IntervalIntegrable (fun t ↦ γ' t / (γ t - w)) volume a b) :
    ∫ t in a..b, γ' t / (γ t - w) = Complex.log ((γ b - w) / (γ a - w)) := by
  have h_a_ne : γ a - w ≠ 0 := by
    intro h0
    have h1 := h_slit a left_mem_uIcc
    rw [h0, div_zero] at h1
    exact zero_notMem_slitPlane h1
  have hfun : (fun t ↦ γ' t / (γ a - w) / ((γ t - w) / (γ a - w)))
      = fun t ↦ γ' t / (γ t - w) := funext fun t ↦ div_div_div_cancel_right₀ h_a_ne _ _
  have hgen := integral_deriv_div_eq_log_sub_log (f := fun t ↦ (γ t - w) / (γ a - w))
    (f' := fun t ↦ γ' t / (γ a - w)) hP ((hγ_cont.sub continuousOn_const).div_const _)
    (fun t ht ↦ ((hγ_diff t ht).sub_const w).div_const _) h_slit (by rw [hfun]; exact h_int)
  rwa [hfun, div_self h_a_ne, Complex.log_one, sub_zero] at hgen

/-- **Winding-integrand form of the contour log-derivative FTC.** The `γ' = deriv γ` specialization
of `integral_deriv_div_sub_eq_log`, stated with the winding-integral integrand
`(γ t - w)⁻¹ * deriv γ t` in both the integrability hypothesis and the conclusion (matching the
`g (γ t) * deriv γ t` shape of `integral_comp_mul_deriv_eq_sub_of_hasDerivAt` and the winding API),
so a downstream winding sum can apply it per segment without rearranging the integrand. -/
theorem integral_inv_sub_mul_deriv_eq_log {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ} {P : Set ℝ}
    (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (h_slit : ∀ t ∈ uIcc a b, (γ t - w) / (γ a - w) ∈ slitPlane)
    (h_int : IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b) :
    ∫ t in a..b, (γ t - w)⁻¹ * deriv γ t = Complex.log ((γ b - w) / (γ a - w)) := by
  simp only [inv_mul_eq_div]
  exact integral_deriv_div_sub_eq_log (γ' := deriv γ) hP hγ_cont
    (fun t ht ↦ (hγ_diff t ht).hasDerivAt) h_slit (by simpa only [inv_mul_eq_div] using h_int)

/-- At a point where a function is analytic and non-vanishing, its logarithmic derivative
`logDeriv f = deriv f / f` is analytic. This is the regularity input for every integrability and
residue statement about a logarithmic-derivative integrand, from the interval-integrability lemma
below to the residue form of the argument principle
(`TauCeti.Contour.residue_logDeriv_eq_meromorphicOrderAt`). -/
lemma analyticAt_logDeriv_of_analyticAt {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hz : f z ≠ 0) : AnalyticAt ℂ (logDeriv f) z := by
  rw [logDeriv]
  exact hf.deriv.div hf hz

/-- The argument-principle integrand `deriv γ • (logDeriv h ∘ γ)` is interval-integrable along a
piecewise-`C¹` curve `γ` on which `h` is analytic and zero-free. This supplies the integrability
hypothesis of the logarithmic-derivative contour results — `IntervalIntegrable` is what
`integral_deriv_div_eq_log_sub_log` and its specializations ask of the integrand. -/
theorem intervalIntegrable_deriv_smul_logDeriv {γ : ℝ → ℂ} {h : ℂ → ℂ} {a b : ℝ}
    (hγ : IsPiecewiseC1On γ a b) (hh : ∀ t ∈ uIcc a b, AnalyticAt ℂ h (γ t))
    (hne : ∀ t ∈ uIcc a b, h (γ t) ≠ 0) :
    IntervalIntegrable (fun t ↦ deriv γ t • logDeriv h (γ t)) volume a b := by
  refine hγ.intervalIntegrable_deriv_smul_comp ?_
  rintro _ ⟨t, ht, rfl⟩
  exact (analyticAt_logDeriv_of_analyticAt (hh t ht) (hne t ht)).continuousAt.continuousWithinAt

/-- **A slit-plane-valued function has a single-valued logarithm along a closed curve.** If `h` is
analytic along a closed piecewise-`C¹` curve `γ` and takes its values there in
`Complex.slitPlane`, then `Complex.log ∘ h` is a primitive of `logDeriv h` along `γ`, so the
contour integral of `logDeriv h` vanishes.

This is the corner-tolerant replacement for `circleIntegral.integral_eq_zero_of_hasDerivWithinAt`:
`γ` need only be differentiable off the countably many breakpoints, which is what
`integral_deriv_div_eq_log_sub_log` asks for. Nothing is required of `h` off the curve — in the
Rouché application `h = g / f` has both zeros and poles inside. -/
theorem integral_deriv_smul_logDeriv_eq_zero_of_mem_slitPlane {γ : ℝ → ℂ} {h : ℂ → ℂ} {a b : ℝ}
    (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b)
    (hh : ∀ t ∈ uIcc a b, AnalyticAt ℂ h (γ t))
    (hslit : ∀ t ∈ uIcc a b, h (γ t) ∈ slitPlane) :
    ∫ t in a..b, deriv γ t • logDeriv h (γ t) = 0 := by
  obtain ⟨P, hPc, hPd⟩ := hγ.exists_countable_differentiableAt
  have hne : ∀ t ∈ uIcc a b, h (γ t) ≠ 0 := fun t ht ↦ slitPlane_ne_zero (hslit t ht)
  have hint := intervalIntegrable_deriv_smul_logDeriv hγ hh hne
  -- The integrand is the logarithmic-derivative integrand of `t ↦ h (γ t)`.
  simp only [smul_eq_mul, logDeriv_apply, ← mul_div_assoc] at hint ⊢
  rw [integral_deriv_div_eq_log_sub_log (f := fun t ↦ h (γ t))
    (f' := fun t ↦ deriv γ t * deriv h (γ t)) hPc
    (fun t ht ↦ ((hh t ht).continuousAt).comp_continuousWithinAt (hγ.continuousOn t ht))
    (fun t ht ↦ ?_) hslit hint, hclosed, sub_self]
  have hmem : t ∈ uIcc a b := Ioo_subset_Icc_self ht.1
  simpa only [Function.comp_def, smul_eq_mul] using
    ((hh t hmem).differentiableAt.hasDerivAt).scomp t ((hPd t ht).hasDerivAt)

end TauCeti.Contour
