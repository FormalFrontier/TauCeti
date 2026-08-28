/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The truncated Perron kernel and Perron's formula

Perron's formula recovers a summatory function from a Dirichlet series by integrating `x ^ s / s`
up a vertical line.  At finite height the integral is not the sharp step function it approximates,
and this file makes the finite-height object visible before the sharp smoothed-step estimate is
applied to it.  The only estimates proved here are the crude modulus bounds
`TauCeti.norm_perronIntegrand_le` and `TauCeti.norm_truncatedPerronKernel_le`, which are what the
interchange below needs.

`TauCeti.truncatedPerronKernel x c T` is the value of `(2πi)⁻¹ ∫ x ^ s / s ds` over the segment
from `c - iT` to `c + iT`.  Parameterizing that segment by `s = c + i t` with `t` real turns
`ds` into `i dt`, so the `i` in `(2πi)⁻¹` cancels and the visible prefactor is `(2π)⁻¹`; the
integrand along the segment is `TauCeti.perronIntegrand`.

Once the same segment is used against an absolutely convergent Dirichlet series `LSeries a`, the
integral and the series may be interchanged, and each coefficient `a n` picks up the kernel at the
rescaled point `x / n`.  That is `TauCeti.perronIntegral_eq_tsum_truncatedPerronKernel`.

## Main results

* `TauCeti.truncatedPerronKernel_one`: at `x = 1` the kernel is exactly
  `π⁻¹ * Real.arctan (T / c)`.
* `TauCeti.truncatedPerronKernel_one_ne_half`: consequently it is never `1 / 2`, at any finite
  height.  The value `1 / 2` conventionally attached to the endpoint `x = 1` is only a limit.
* `TauCeti.tendsto_truncatedPerronKernel_one`: that limit, as the height tends to infinity.
* `TauCeti.truncatedPerronKernel_im`: the kernel is real, because the integrand takes conjugate
  values at opposite heights.
* `TauCeti.norm_perronIntegrand_le`, `TauCeti.norm_truncatedPerronKernel_le`: the crude modulus
  bounds `x ^ c / c` and `T * x ^ c / (π * c)`, for `0 ≤ x` and `0 < c`.
* `TauCeti.perronIntegral_eq_tsum_truncatedPerronKernel`: for `0 < c` with `LSeries a` absolutely
  convergent at `c`, and `0 ≤ x`, `0 ≤ T`, the truncated Perron integral of `LSeries a` is
  `∑' n, a n * truncatedPerronKernel (x / n) c T`.
* `TauCeti.summable_mul_truncatedPerronKernel`: under the same hypotheses that series converges
  absolutely.

## Roadmap role

This file carries the definitional half of Layer **6.3** of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`, together with the endpoint computation the
roadmap lists as its fourth rejection test, and the interchange of Layer **6.4**.  The remaining
half of 6.3 — the estimate exhibiting the kernel as a smoothed step function with an explicit
universal constant, for `x ≠ 1` — is not proved here, and neither is the sharp summatory form of
6.4, which turns `TauCeti.perronIntegral_eq_tsum_truncatedPerronKernel` into a statement about
`∑ n < x, a n` by feeding that estimate into each summand.

## References

* E. C. Titchmarsh, revised by D. R. Heath-Brown, *The Theory of the Riemann Zeta-Function*,
  Lemma 3.12.
* H. Davenport, *Multiplicative Number Theory*, Chapter 17.
-/

public section

namespace TauCeti

open Complex Filter MeasureTheory Topology

open scoped Real

variable {x c : ℝ}

/-- The integrand of the truncated Perron integral: the value of `s ↦ x ^ s / s` at the point
`s = c + i t` of the vertical line `Re s = c`. -/
noncomputable def perronIntegrand (x c t : ℝ) : ℂ :=
  (x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)

/-- The defining formula for the Perron integrand. -/
theorem perronIntegrand_def (x c t : ℝ) :
    perronIntegrand x c t = (x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) := (rfl)

/-- A point of the vertical line `Re s = c` is nonzero as soon as `c` is.  Mathlib's
`Complex.ne_zero_of_re_pos` covers only the positive-real-part case. -/
private theorem ofReal_add_mul_I_ne_zero (hc : c ≠ 0) (t : ℝ) : (c : ℂ) + t * I ≠ 0 := fun h =>
  hc (by simpa using congrArg Complex.re h)

/-- The vertical line `Re s = c`, parameterized by the height, is continuous. -/
private theorem continuous_ofReal_add_mul_I (c : ℝ) : Continuous fun t : ℝ => (c : ℂ) + t * I :=
  continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

/-- At the endpoint `x = 1` the Perron integrand is the reciprocal of the point of the line. -/
@[simp]
theorem perronIntegrand_one (c t : ℝ) : perronIntegrand 1 c t = ((c : ℂ) + t * I)⁻¹ := by
  rw [perronIntegrand, Complex.ofReal_one, Complex.one_cpow, inv_eq_one_div]

/-- The Perron integrand vanishes at the degenerate base `x = 0`; that is the base produced by the
rescaling `x / n` at `n = 0`, in `TauCeti.perronIntegral_eq_tsum_truncatedPerronKernel`. -/
@[simp]
theorem perronIntegrand_zero (c t : ℝ) : perronIntegrand 0 c t = 0 := by
  rcases eq_or_ne ((c : ℂ) + t * I) 0 with h | h
  · rw [perronIntegrand, h, div_zero]
  · rw [perronIntegrand, Complex.ofReal_zero, Complex.zero_cpow h, zero_div]

/-- The modulus of the Perron integrand: the numerator contributes `x ^ c`, independently of the
height, and the denominator the distance from the origin to `c + i t`. -/
theorem norm_perronIntegrand (hx : 0 < x) (c t : ℝ) :
    ‖perronIntegrand x c t‖ = x ^ c / Real.sqrt (c ^ 2 + t ^ 2) := by
  rw [perronIntegrand, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_add_mul_I]
  simp

/-- The Perron integrand is continuous in the height along any vertical line off the imaginary
axis.  No hypothesis on the base is needed: only the exponent has to avoid the origin, and at
`x = 0` the integrand vanishes identically. -/
theorem continuous_perronIntegrand (hc : c ≠ 0) : Continuous (perronIntegrand x c) := by
  rcases eq_or_ne x 0 with rfl | hx
  · have hzero : perronIntegrand 0 c = fun _ : ℝ => (0 : ℂ) := funext (perronIntegrand_zero c)
    rw [hzero]
    exact continuous_const
  · have hcpow : Continuous fun s : ℂ => (x : ℂ) ^ s :=
      continuous_iff_continuousAt.2 fun _ => continuousAt_const_cpow (mod_cast hx)
    exact (hcpow.comp (continuous_ofReal_add_mul_I c)).div (continuous_ofReal_add_mul_I c)
      fun t => ofReal_add_mul_I_ne_zero hc t

/-- The Perron integrand is integrable over every bounded piece of a vertical line off the
imaginary axis. -/
theorem intervalIntegrable_perronIntegrand (hc : c ≠ 0) (a b : ℝ) :
    IntervalIntegrable (perronIntegrand x c) volume a b :=
  (continuous_perronIntegrand hc).intervalIntegrable a b

/-- The Perron integrand takes complex conjugate values at opposite heights. -/
theorem conj_perronIntegrand (hx : 0 ≤ x) (c t : ℝ) :
    (starRingEnd ℂ) (perronIntegrand x c t) = perronIntegrand x c (-t) := by
  have harg : ((x : ℂ)).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg hx]
    exact fun h => Real.pi_ne_zero h.symm
  have hline : ((c : ℂ) + (-t : ℝ) * I) = (starRingEnd ℂ) ((c : ℂ) + t * I) := by
    simp
  rw [perronIntegrand, perronIntegrand, map_div₀, hline, Complex.cpow_conj _ _ harg,
    Complex.conj_ofReal]

/-- The **truncated Perron kernel** of height `T` on the vertical line `Re s = c`: the value of
`(2πi)⁻¹ ∫ x ^ s / s ds` over the segment from `c - iT` to `c + iT`.

The segment is parameterized by `s = c + i t` for `t` in `[-T, T]`, so `ds = i dt` and the
visible prefactor is `(2π)⁻¹` rather than `(2πi)⁻¹`. -/
noncomputable def truncatedPerronKernel (x c T : ℝ) : ℂ :=
  ((2 * π : ℝ) : ℂ)⁻¹ * ∫ t in -T..T, perronIntegrand x c t

/-- The defining formula for the truncated Perron kernel. -/
theorem truncatedPerronKernel_def (x c T : ℝ) :
    truncatedPerronKernel x c T = ((2 * π : ℝ) : ℂ)⁻¹ * ∫ t in -T..T, perronIntegrand x c t :=
  (rfl)

/-- At zero height the truncated Perron kernel vanishes: the segment of integration is a point. -/
@[simp]
theorem truncatedPerronKernel_height_zero (x c : ℝ) : truncatedPerronKernel x c 0 = 0 := by
  simp [truncatedPerronKernel]

/-- The truncated Perron kernel vanishes at the degenerate base `x = 0`; this is the value taken by
the `n = 0` summand of `TauCeti.perronIntegral_eq_tsum_truncatedPerronKernel`. -/
@[simp]
theorem truncatedPerronKernel_zero (c T : ℝ) : truncatedPerronKernel 0 c T = 0 := by
  simp [truncatedPerronKernel]

/-- The truncated Perron kernel is real: the two halves of the segment contribute conjugate
values. -/
@[simp]
theorem truncatedPerronKernel_im (hx : 0 ≤ x) (c T : ℝ) :
    (truncatedPerronKernel x c T).im = 0 := by
  rw [← Complex.conj_eq_iff_im, truncatedPerronKernel, map_mul]
  refine congrArg₂ _ (by rw [map_inv₀, Complex.conj_ofReal]) ?_
  rw [← intervalIntegral.intervalIntegral_conj]
  simp_rw [conj_perronIntegrand hx]
  simp

/-- On the line `Re s = c` with `c > 0`, the map
`t ↦ arctan (t / c) - (i / 2) * log (c ^ 2 + t ^ 2)` is a primitive of the Perron integrand at
`x = 1`; its real part contributes the arctangent and its imaginary part cancels over a symmetric
interval. -/
private theorem hasDerivAt_perronPrimitive (hc : 0 < c) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ => (Real.arctan (u / c) : ℂ) - I / 2 * (Real.log (c ^ 2 + u ^ 2) : ℂ))
      (perronIntegrand 1 c t) t := by
  have hpos : (0 : ℝ) < c ^ 2 + t ^ 2 := by positivity
  have harctan : HasDerivAt (fun u : ℝ => Real.arctan (u / c)) (c / (c ^ 2 + t ^ 2)) t := by
    have h := ((hasDerivAt_id t).div_const c).arctan
    simp only [id_eq] at h
    convert h using 1
    field_simp
  have hlog : HasDerivAt (fun u : ℝ => Real.log (c ^ 2 + u ^ 2)) (2 * t / (c ^ 2 + t ^ 2)) t := by
    have hsq : HasDerivAt (fun u : ℝ => c ^ 2 + u ^ 2) (2 * t) t :=
      ((hasDerivAt_pow 2 t).const_add (c ^ 2)).congr_deriv (by norm_num)
    exact hsq.log hpos.ne'
  have h := harctan.ofReal_comp.sub (hlog.ofReal_comp.const_mul (I / 2))
  refine h.congr_deriv ?_
  have hne : ((c : ℂ) + t * I) ≠ 0 := ofReal_add_mul_I_ne_zero hc.ne' t
  have hposC : ((c : ℂ) ^ 2 + (t : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (by exact_mod_cast hpos.ne' : ((c ^ 2 + t ^ 2 : ℝ) : ℂ) ≠ 0)
  rw [perronIntegrand_one]
  refine eq_inv_of_mul_eq_one_left ?_
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The exact value of the truncated Perron kernel at the endpoint `x = 1`. -/
theorem truncatedPerronKernel_one (hc : 0 < c) (T : ℝ) :
    truncatedPerronKernel 1 c T = (π⁻¹ * Real.arctan (T / c) : ℝ) := by
  have hint : (∫ t in -T..T, perronIntegrand 1 c t)
      = ((Real.arctan (T / c) : ℂ) - I / 2 * (Real.log (c ^ 2 + T ^ 2) : ℂ))
        - ((Real.arctan (-T / c) : ℂ) - I / 2 * (Real.log (c ^ 2 + (-T) ^ 2) : ℂ)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hasDerivAt_perronPrimitive hc u)
      (intervalIntegrable_perronIntegrand (x := 1) hc.ne' _ _)
  rw [truncatedPerronKernel, hint, neg_div, Real.arctan_neg, neg_sq]
  have hpi : (π : ℂ) ≠ 0 := mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-- At any finite height the Perron kernel at the endpoint `x = 1` is not `1 / 2`; the customary
half-weight there is only the limit `TauCeti.tendsto_truncatedPerronKernel_one`. -/
theorem truncatedPerronKernel_one_ne_half (hc : 0 < c) (T : ℝ) :
    truncatedPerronKernel 1 c T ≠ 1 / 2 := by
  rw [truncatedPerronKernel_one hc]
  intro h
  have h' : π⁻¹ * Real.arctan (T / c) = 1 / 2 := by simpa using congrArg Complex.re h
  have hlt : π⁻¹ * Real.arctan (T / c) < π⁻¹ * (π / 2) :=
    mul_lt_mul_of_pos_left (Real.arctan_lt_pi_div_two (T / c)) (by positivity)
  rw [h'] at hlt
  have : π⁻¹ * (π / 2) = 1 / 2 := by field_simp
  simp [this] at hlt

/-- As the height tends to infinity the Perron kernel at the endpoint `x = 1` tends to `1 / 2`. -/
theorem tendsto_truncatedPerronKernel_one (hc : 0 < c) :
    Tendsto (truncatedPerronKernel 1 c) atTop (𝓝 (1 / 2)) := by
  have harctan : Tendsto (fun T : ℝ => Real.arctan (T / c)) atTop (𝓝 (π / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
      (tendsto_id.atTop_div_const hc)
  have hhalf : π⁻¹ * (π / 2) = 1 / 2 := by field_simp
  have hreal : Tendsto (fun T : ℝ => π⁻¹ * Real.arctan (T / c)) atTop (𝓝 (1 / 2)) := by
    rw [← hhalf]
    exact harctan.const_mul _
  have hcplx : Tendsto (fun T : ℝ => ((π⁻¹ * Real.arctan (T / c) : ℝ) : ℂ)) atTop (𝓝 (1 / 2)) := by
    simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto ((1 : ℝ) / 2)).comp hreal
  exact hcplx.congr fun T => (truncatedPerronKernel_one hc T).symm

/-!
### Perron's formula

Against an absolutely convergent Dirichlet series the truncated Perron integral splits into one
kernel per coefficient.  The `n = 0` slot of a Dirichlet series carries no information, and it
carries no weight here either: the rescaled base is `x / (0 : ℕ) = 0`, where both
`TauCeti.perronIntegrand_zero` and `TauCeti.truncatedPerronKernel_zero` apply.
-/

variable {a : ℕ → ℂ}

/-- On the whole line `Re s = c` the Perron integrand is bounded by `x ^ c / c`: the numerator is
constant along the line and the denominator is at least `c`. -/
theorem norm_perronIntegrand_le (hx : 0 ≤ x) (hc : 0 < c) (t : ℝ) :
    ‖perronIntegrand x c t‖ ≤ x ^ c / c := by
  rcases hx.eq_or_lt with rfl | hx'
  · rw [perronIntegrand_zero, Real.zero_rpow hc.ne', norm_zero, zero_div]
  · have hle : c ≤ Real.sqrt (c ^ 2 + t ^ 2) := by
      have h := Real.sqrt_le_sqrt (show c ^ 2 ≤ c ^ 2 + t ^ 2 by nlinarith [sq_nonneg t])
      rwa [Real.sqrt_sq hc.le] at h
    rw [norm_perronIntegrand hx']
    gcongr

variable {T : ℝ}

/-- A crude bound on the truncated Perron kernel, linear in the height.  It is what makes the
series of `TauCeti.perronIntegral_eq_tsum_truncatedPerronKernel` absolutely convergent; the sharp
bound, which is uniform in the height away from `x = 1`, is a separate estimate. -/
theorem norm_truncatedPerronKernel_le (hx : 0 ≤ x) (hc : 0 < c) (hT : 0 ≤ T) :
    ‖truncatedPerronKernel x c T‖ ≤ T * x ^ c / (π * c) := by
  rcases hx.eq_or_lt with rfl | hx'
  · rw [truncatedPerronKernel_zero, Real.zero_rpow hc.ne', norm_zero, mul_zero, zero_div]
  · have hint : ‖∫ t in -T..T, perronIntegrand x c t‖ ≤ x ^ c / c * (2 * T) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T)
        (f := perronIntegrand x c) fun t _ => norm_perronIntegrand_le hx'.le hc t
      rwa [show |T - -T| = 2 * T by
        rw [sub_neg_eq_add, ← two_mul, abs_of_nonneg (by linarith)]] at h
    have hnorm : ‖((2 * π : ℝ) : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [truncatedPerronKernel, norm_mul, hnorm]
    calc (2 * π)⁻¹ * ‖∫ t in -T..T, perronIntegrand x c t‖
        ≤ (2 * π)⁻¹ * (x ^ c / c * (2 * T)) :=
          mul_le_mul_of_nonneg_left hint (by positivity)
      _ = T * x ^ c / (π * c) := by
          field_simp

/-- Dividing the base of the Perron integrand by `n` is the same as multiplying it by the `n`-th
Dirichlet term: this is the identity `n ^ (-s) * x ^ s = (x / n) ^ s` that turns the truncated
Perron integral of a Dirichlet series into a series of kernels. -/
theorem term_mul_perronIntegrand (a : ℕ → ℂ) (hx : 0 ≤ x) (hc : c ≠ 0) (n : ℕ) (t : ℝ) :
    LSeries.term a ((c : ℂ) + t * I) n * perronIntegrand x c t
      = a n * perronIntegrand (x / n) c t := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hne : ((n : ℂ)) ^ ((c : ℂ) + t * I) ≠ 0 :=
      (Complex.cpow_ne_zero_iff).2 (Or.inl (Nat.cast_ne_zero.2 hn))
    have hline : (c : ℂ) + t * I ≠ 0 := ofReal_add_mul_I_ne_zero hc t
    rw [LSeries.term_of_ne_zero hn, perronIntegrand, perronIntegrand, Complex.ofReal_div,
      Complex.div_cpow_ofReal_nonneg hx n.cast_nonneg, Complex.ofReal_natCast]
    field_simp

/-- The modulus of the `n`-th coefficient, weighted by the rescaled base `x / n`, is the modulus
of the `n`-th Dirichlet term at `c` weighted by `x ^ c`. -/
private theorem norm_mul_rpow_div_natCast (a : ℕ → ℂ) (hx : 0 ≤ x) (hc : c ≠ 0) (n : ℕ) :
    ‖a n‖ * (x / n) ^ c = x ^ c * ‖LSeries.term a (c : ℂ) n‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.zero_rpow hc]
  · rw [LSeries.norm_term_eq, ite_eq_right hn, Complex.ofReal_re, Real.div_rpow hx n.cast_nonneg]
    ring

/-- On a vertical line strictly inside the half-plane of absolute convergence, a Dirichlet series
is continuous in the height. -/
theorem continuous_LSeries_ofReal_add_mul_I (habs : LSeries.abscissaOfAbsConv a < (c : EReal)) :
    Continuous fun t : ℝ => LSeries a ((c : ℂ) + t * I) := by
  refine continuous_iff_continuousAt.2 fun t =>
    ContinuousAt.comp (g := LSeries a) ?_ (continuous_ofReal_add_mul_I c).continuousAt
  exact (LSeries_analyticOnNhd a _ (by simpa using habs)).continuousAt

/-- The integrand of the truncated Perron integral of a Dirichlet series is interval integrable on
every vertical segment strictly inside the half-plane of absolute convergence. -/
theorem intervalIntegrable_LSeries_mul_perronIntegrand
    (habs : LSeries.abscissaOfAbsConv a < (c : EReal)) (hc : c ≠ 0) (T₁ T₂ : ℝ) :
    IntervalIntegrable
      (fun t => LSeries a ((c : ℂ) + t * I) * perronIntegrand x c t) volume T₁ T₂ :=
  ((continuous_LSeries_ofReal_add_mul_I habs).mul
    (continuous_perronIntegrand hc)).intervalIntegrable _ _

/-- The series of kernels appearing in Perron's formula converges absolutely. -/
theorem summable_mul_truncatedPerronKernel (hs : LSeriesSummable a (c : ℂ))
    (hc : 0 < c) (hx : 0 ≤ x) (hT : 0 ≤ T) :
    Summable fun n : ℕ => a n * truncatedPerronKernel (x / n) c T := by
  have hterm : Summable fun n : ℕ => ‖LSeries.term a (c : ℂ) n‖ := summable_norm_iff.2 hs
  refine Summable.of_norm <| Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (((hterm.mul_left (x ^ c)).mul_left T).div_const (π * c))
  rw [norm_mul]
  calc ‖a n‖ * ‖truncatedPerronKernel (x / n) c T‖
      ≤ ‖a n‖ * (T * (x / n) ^ c / (π * c)) :=
        mul_le_mul_of_nonneg_left
          (norm_truncatedPerronKernel_le (div_nonneg hx n.cast_nonneg) hc hT) (norm_nonneg _)
    _ = T * (x ^ c * ‖LSeries.term a (c : ℂ) n‖) / (π * c) := by
        rw [← norm_mul_rpow_div_natCast a hx hc.ne']
        ring

/-- The truncated Perron integral of a Dirichlet series absolutely convergent at `c > 0`, for
`0 ≤ x` and `0 ≤ T`: the integral and the series may be interchanged, so that the integral is the
sum, over the coefficients, of the truncated Perron kernels at the rescaled bases `x / n`.

Turning the right-hand side into the sharp summatory function `∑ n < x, a n` — the classical
Perron formula — is a separate step, which needs the estimate exhibiting the kernel as a smoothed
step. -/
theorem perronIntegral_eq_tsum_truncatedPerronKernel (hs : LSeriesSummable a (c : ℂ)) (hc : 0 < c)
    (hx : 0 ≤ x) (hT : 0 ≤ T) :
    ((2 * π : ℝ) : ℂ)⁻¹ * ∫ t in -T..T, LSeries a ((c : ℂ) + t * I) * perronIntegrand x c t
      = ∑' n : ℕ, a n * truncatedPerronKernel (x / n) c T := by
  have hTT : -T ≤ T := by linarith
  have hterm : Summable fun n : ℕ => ‖LSeries.term a (c : ℂ) n‖ := summable_norm_iff.2 hs
  -- Each summand is continuous, hence integrable on the segment.
  have hint : ∀ n : ℕ, IntegrableOn (fun t => a n * perronIntegrand (x / n) c t)
      (Set.Ioc (-T) T) :=
    fun n => (continuous_const.mul (continuous_perronIntegrand hc.ne')).integrableOn_Ioc
  -- The integrals of the moduli are dominated by a convergent series of constants.
  have hdom : Summable fun n : ℕ =>
      ∫ t in Set.Ioc (-T) T, ‖a n * perronIntegrand (x / n) c t‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _)
      (fun n => ?_) (((hterm.mul_left (x ^ c)).div_const c).mul_left (2 * T))
    calc ∫ t in Set.Ioc (-T) T, ‖a n * perronIntegrand (x / n) c t‖
        ≤ ∫ _ in Set.Ioc (-T) T, x ^ c * ‖LSeries.term a (c : ℂ) n‖ / c := by
          refine MeasureTheory.setIntegral_mono_on (hint n).norm
            (integrableOn_const (by simp)) measurableSet_Ioc fun t _ => ?_
          rw [norm_mul, ← norm_mul_rpow_div_natCast a hx hc.ne', mul_div_assoc]
          exact mul_le_mul_of_nonneg_left
            (norm_perronIntegrand_le (div_nonneg hx n.cast_nonneg) hc t) (norm_nonneg _)
      _ = 2 * T * (x ^ c * ‖LSeries.term a (c : ℂ) n‖ / c) := by
          rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hTT, smul_eq_mul]
          ring
  -- Interchange the integral with the series.
  rw [intervalIntegral.integral_of_le hTT]
  have hpt : ∀ t : ℝ, LSeries a ((c : ℂ) + t * I) * perronIntegrand x c t
      = ∑' n : ℕ, a n * perronIntegrand (x / n) c t := by
    intro t
    rw [LSeries, ← tsum_mul_right]
    exact tsum_congr fun n => term_mul_perronIntegrand a hx hc.ne' n t
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t _ => hpt t),
    ← MeasureTheory.integral_tsum_of_summable_integral_norm hint hdom, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [MeasureTheory.integral_const_mul, truncatedPerronKernel,
    intervalIntegral.integral_of_le hTT]
  ring

end TauCeti
