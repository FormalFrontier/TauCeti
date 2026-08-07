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
public import TauCeti.Analysis.Complex.UpperLogContinuity
public import TauCeti.Analysis.Contour.Curve.Integrability

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import TauCeti.Analysis.Contour.Winding.Number.Basic
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

That same integrand is what the winding number of the *image* curve computes: if `h` is moreover
zero-free along `γ`, then `h ∘ γ` misses the origin and its index integral
`(2πi)⁻¹ ∮_{h ∘ γ} dw / w` is, after the substitution `w = h z`, exactly
`(2πi)⁻¹ ∫_a^b γ' • (logDeriv h ∘ γ)`. Formally the substitution is the chain rule
`(h ∘ γ)' = γ' · h'(γ)`, available off the breakpoints of `γ` and so almost everywhere, which is all
an integral sees. This bridge is what turns every logarithmic-derivative integral identity — the
argument principle above all — into a statement about how often an image curve winds.

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
* `TauCeti.Contour.windingNumber_comp_eq_integral_logDeriv` — the bridge to the image curve: the
  winding number of `h ∘ γ` about the origin is `(2πi)⁻¹ ∫_a^b γ' • (logDeriv h ∘ γ)`.

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

/-- **The winding number of the image curve is the logarithmic-derivative integral.** If `h` is
analytic and zero-free along a piecewise-`C¹` curve `γ`, the composite `h ∘ γ` avoids the origin
and

`n_0(h ∘ γ) = (2πi)⁻¹ ∫_a^b γ' t · (logDeriv h) (γ t)`.

This is the substitution `w = h z` in the index integral `(2πi)⁻¹ ∮_{h ∘ γ} dw / w`, carried out by
the chain rule. The chain rule is available only off the breakpoints of `γ`, a finite set, so the
two integrands agree merely almost everywhere — enough for both the integrals and the
interval-integrability to transfer. No regularity of `h ∘ γ` beyond continuity and this
almost-everywhere derivative is needed, so nothing has to be said about `h ∘ γ` being
piecewise `C¹` (it is, but `windingNumber` does not ask).

The analyticity hypothesis is local: `AnalyticAt ℂ h (γ t)` asks only for *some* neighbourhood of
each point of the curve on which `h` is analytic, never for one ambient open set carrying the whole
curve, and imposes no condition beyond those neighbourhoods. So the lemma applies verbatim to a
function with zeros and poles inside the region the curve encloses; that is what the argument
principle then counts. -/
theorem windingNumber_comp_eq_integral_logDeriv {γ : ℝ → ℂ} {h : ℂ → ℂ} {a b : ℝ}
    (hγ : IsPiecewiseC1On γ a b) (hh : ∀ t ∈ uIcc a b, AnalyticAt ℂ h (γ t))
    (hne : ∀ t ∈ uIcc a b, h (γ t) ≠ 0) :
    windingNumber (h ∘ γ) a b 0
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∫ t in a..b, deriv γ t • logDeriv h (γ t) := by
  obtain ⟨p, hp⟩ := hγ.exists_finset_differentiableAt
  have hcont : ContinuousOn (h ∘ γ) (uIcc a b) := fun t ht =>
    (hh t ht).continuousAt.comp_continuousWithinAt (hγ.continuousOn t ht)
  -- Off the finitely many breakpoints of `γ` — and off the right endpoint, which `Ι a b` contains
  -- but `Set.Ioo (min a b) (max a b)` does not — the chain rule identifies the two integrands.
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι a b →
      deriv γ t • logDeriv h (γ t) = ((h ∘ γ) t - 0)⁻¹ * deriv (h ∘ γ) t := by
    have hnull : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ insert (max a b) (↑p : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.mp ((p.finite_toSet.insert (max a b)).measure_zero volume)
    filter_upwards [hnull] with t hts ht
    have ht' : t ∈ Ioc (min a b) (max a b) := ht
    have htIoo : t ∈ Ioo (min a b) (max a b) \ (↑p : Set ℝ) :=
      ⟨⟨ht'.1, lt_of_le_of_ne ht'.2 fun hmax => hts (by simp [hmax])⟩,
        fun hmem => hts (Set.mem_insert_of_mem _ hmem)⟩
    have htu : t ∈ uIcc a b := by
      rw [← Set.Icc_min_max]
      exact Ioo_subset_Icc_self htIoo.1
    have hcomp : logDeriv (h ∘ γ) t = logDeriv h (γ t) * deriv γ t :=
      logDeriv_comp (hh t htu).differentiableAt (hp t htIoo)
    rw [sub_zero, ← div_eq_inv_mul, ← logDeriv_apply, hcomp, smul_eq_mul, mul_comm]
  have hint : IntervalIntegrable (fun t => deriv γ t • logDeriv h (γ t)) volume a b :=
    intervalIntegrable_deriv_smul_logDeriv hγ hh hne
  rw [windingNumber_eq_integral_of_avoidance hcont
      (fun t ht => hne t ht) (hint.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr hae))]
  exact congrArg _ (intervalIntegral.integral_congr_ae hae).symm

section BoundaryTolerant

open MeasureTheory

/-- Transport of the logarithmic integrand across an interior agreement: if `g = h` with
equal derivatives on the open interval, the integrands agree almost everywhere on the
interval and integrability transports. -/
private lemma aeEq_and_intervalIntegrable_of_eqOn_Ioo {g h : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (heq : ∀ t ∈ Set.Ioo a b, g t = h t ∧ deriv g t = deriv h t)
    (hint_h : IntervalIntegrable (fun t ↦ deriv h t / h t) volume a b) :
    (∀ᵐ t ∂volume, t ∈ Set.uIoc a b → deriv g t / g t = deriv h t / h t) ∧
    IntervalIntegrable (fun t ↦ deriv g t / g t) volume a b := by
  have hb_ae : ({b} : Set ℝ)ᶜ ∈ ae volume := by
    simp [MeasureTheory.mem_ae_iff]
  have h_congr : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → deriv g t / g t = deriv h t / h t := by
    filter_upwards [hb_ae] with t ht_ne_b ht_mem
    rw [Set.uIoc_of_le hab] at ht_mem
    obtain ⟨hval, hderiv⟩ := heq t
      ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 fun h ↦ ht_ne_b (Set.mem_singleton_iff.mpr h)⟩
    rw [hval, hderiv]
  refine ⟨h_congr, hint_h.congr_ae ?_⟩
  exact (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr
    (h_congr.mono fun t ht hm ↦ (ht hm).symm)

/-- **The boundary-tolerant logarithmic FTC, upper form**: for a comparison function `h`
confined to the closed upper half-plane, nonvanishing, and slit-plane-valued on the
interior, the logarithmic integral of `g` evaluates to the difference of logarithms —
even when the endpoint values sit on the slit-plane boundary. -/
theorem integral_deriv_div_eq_log_of_im_nonneg {g h : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hh_cont : ContinuousOn h (Set.Icc a b))
    (hh_diff : ∀ t ∈ Set.Ioo a b, DifferentiableAt ℝ h t)
    (hh_deriv_cont : ContinuousOn (deriv h) (Set.Icc a b))
    (hh_im_nn : ∀ t ∈ Set.Icc a b, 0 ≤ (h t).im)
    (hh_ne : ∀ t ∈ Set.Icc a b, h t ≠ 0)
    (hh_slit : ∀ t ∈ Set.Ioo a b, h t ∈ Complex.slitPlane)
    (heq : ∀ t ∈ Set.Ioo a b, g t = h t ∧ deriv g t = deriv h t)
    (heq_a : g a = h a) (heq_b : g b = h b) :
    IntervalIntegrable (fun t ↦ deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) := by
  have hh_log_cont : ContinuousOn (fun t ↦ Complex.log (h t)) (Set.Icc a b) :=
    TauCeti.continuousOn_log_im_nonneg_ne_zero.comp hh_cont
      fun t ht ↦ ⟨hh_im_nn t ht, hh_ne t ht⟩
  have hint_h : IntervalIntegrable (fun t ↦ deriv h t / h t) volume a b :=
    ((hh_deriv_cont.div hh_cont hh_ne).mono
      (Set.uIcc_of_le hab ▸ Set.Subset.rfl)).intervalIntegrable
  obtain ⟨h_congr, hint_g⟩ :=
    aeEq_and_intervalIntegrable_of_eqOn_Ioo hab heq hint_h
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hh_log_cont
    (fun t ht ↦ (hh_diff t ht).hasDerivAt.clog_real (hh_slit t ht)) hint_h
  refine ⟨hint_g, ?_⟩
  calc ∫ t in a..b, deriv g t / g t
      = ∫ t in a..b, deriv h t / h t := intervalIntegral.integral_congr_ae h_congr
    _ = Complex.log (h b) - Complex.log (h a) := h_ftc
    _ = Complex.log (g b) - Complex.log (g a) := by rw [heq_a, heq_b]

/-- **The boundary-tolerant logarithmic FTC, lower form**: for a comparison function
confined to the closed lower half-plane with strictly negative interior imaginary part,
the logarithmic integral evaluates against the negated arguments. -/
theorem integral_deriv_div_eq_log_neg_of_im_nonpos {g h : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hh_cont : ContinuousOn h (Set.Icc a b))
    (hh_diff : ∀ t ∈ Set.Ioo a b, DifferentiableAt ℝ h t)
    (hh_deriv_cont : ContinuousOn (deriv h) (Set.Icc a b))
    (hh_im_np : ∀ t ∈ Set.Icc a b, (h t).im ≤ 0)
    (hh_ne : ∀ t ∈ Set.Icc a b, h t ≠ 0)
    (hh_im_neg : ∀ t ∈ Set.Ioo a b, (h t).im < 0)
    (heq : ∀ t ∈ Set.Ioo a b, g t = h t ∧ deriv g t = deriv h t)
    (heq_a : g a = h a) (heq_b : g b = h b) :
    IntervalIntegrable (fun t ↦ deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t =
      Complex.log (-(g b)) - Complex.log (-(g a)) := by
  have hnh_log_cont : ContinuousOn (fun t ↦ Complex.log (-(h t))) (Set.Icc a b) :=
    TauCeti.continuousOn_log_im_nonneg_ne_zero.comp hh_cont.neg fun t ht ↦
      ⟨by simpa using hh_im_np t ht, neg_ne_zero.mpr (hh_ne t ht)⟩
  have hint_h : IntervalIntegrable (fun t ↦ deriv h t / h t) volume a b :=
    ((hh_deriv_cont.div hh_cont hh_ne).mono
      (Set.uIcc_of_le hab ▸ Set.Subset.rfl)).intervalIntegrable
  obtain ⟨h_congr, hint_g⟩ :=
    aeEq_and_intervalIntegrable_of_eqOn_Ioo hab heq hint_h
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hnh_log_cont
    (fun t ht ↦ by
      have hslit : -(h t) ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr
        (Or.inr (by simpa using ne_of_lt (hh_im_neg t ht)))
      have := (hh_diff t ht).hasDerivAt.neg.clog_real hslit
      exact (show -deriv h t / -h t = deriv h t / h t by rw [neg_div_neg_eq]) ▸ this)
    hint_h
  refine ⟨hint_g, ?_⟩
  calc ∫ t in a..b, deriv g t / g t
      = ∫ t in a..b, deriv h t / h t := intervalIntegral.integral_congr_ae h_congr
    _ = Complex.log (-(h b)) - Complex.log (-(h a)) := h_ftc
    _ = Complex.log (-(g b)) - Complex.log (-(g a)) := by rw [heq_a, heq_b]


/-- **The comparison logarithmic FTC on the slit plane**: for a comparison function `h`
slit-plane-valued on the closed interval, the logarithmic integral of `g` evaluates to
the difference of endpoint logarithms. -/
theorem integral_deriv_div_eq_log_of_slitPlane {g h : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hh_cont : ContinuousOn h (Set.Icc a b))
    (hh_diff : ∀ t ∈ Set.Ioo a b, DifferentiableAt ℝ h t)
    (hh_deriv_cont : ContinuousOn (deriv h) (Set.Icc a b))
    (hh_slit : ∀ t ∈ Set.Icc a b, h t ∈ Complex.slitPlane)
    (heq : ∀ t ∈ Set.Ioo a b, g t = h t ∧ deriv g t = deriv h t)
    (heq_a : g a = h a) (heq_b : g b = h b) :
    IntervalIntegrable (fun t ↦ deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) := by
  have hh_ne : ∀ t ∈ Set.Icc a b, h t ≠ 0 := fun t ht ↦
    Complex.slitPlane_ne_zero (hh_slit t ht)
  have hh_log_cont : ContinuousOn (fun t ↦ Complex.log (h t)) (Set.Icc a b) := fun t ht ↦
    (continuousAt_clog (hh_slit t ht)).comp_continuousWithinAt (hh_cont t ht)
  have hint_h : IntervalIntegrable (fun t ↦ deriv h t / h t) volume a b :=
    ((hh_deriv_cont.div hh_cont hh_ne).mono
      (Set.uIcc_of_le hab ▸ Set.Subset.rfl)).intervalIntegrable
  obtain ⟨h_congr, hint_g⟩ :=
    aeEq_and_intervalIntegrable_of_eqOn_Ioo hab heq hint_h
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hh_log_cont
    (fun t ht ↦ (hh_diff t ht).hasDerivAt.clog_real (hh_slit t ⟨ht.1.le, ht.2.le⟩)) hint_h
  refine ⟨hint_g, ?_⟩
  calc ∫ t in a..b, deriv g t / g t
      = ∫ t in a..b, deriv h t / h t := intervalIntegral.integral_congr_ae h_congr
    _ = Complex.log (h b) - Complex.log (h a) := h_ftc
    _ = Complex.log (g b) - Complex.log (g a) := by rw [heq_a, heq_b]

end BoundaryTolerant


end TauCeti.Contour
