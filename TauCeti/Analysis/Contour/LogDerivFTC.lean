/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
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

## Main results

* `TauCeti.Contour.integral_deriv_div_eq_log_sub_log` — the slit-plane logarithmic-derivative FTC in
  general `f' / f` form.
* `TauCeti.Contour.integral_deriv_div_sub_eq_log` — its contour specialization to
  `f t = (γ t - w) / (γ a - w)`, the per-segment step for evaluating the winding-number integral as
  a sum of `Complex.log` argument increments.
* `TauCeti.Contour.integral_inv_sub_mul_deriv_eq_log` — the `deriv γ` form with the winding-integral
  integrand `(γ t - w)⁻¹ * deriv γ t`, ready for the downstream winding sum.

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

end TauCeti.Contour
