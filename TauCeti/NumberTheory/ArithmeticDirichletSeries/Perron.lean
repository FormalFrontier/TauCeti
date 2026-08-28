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

/-!
# The truncated Perron kernel

Perron's formula recovers a summatory function from a Dirichlet series by integrating `x ^ s / s`
up a vertical line.  At finite height the integral is not the sharp step function it approximates,
and this file makes the finite-height object visible before any estimate is applied to it.

`TauCeti.truncatedPerronKernel x c T` is the value of `(2πi)⁻¹ ∫ x ^ s / s ds` over the segment
from `c - iT` to `c + iT`.  Parameterizing that segment by `s = c + i t` with `t` real turns
`ds` into `i dt`, so the `i` in `(2πi)⁻¹` cancels and the visible prefactor is `(2π)⁻¹`; the
integrand along the segment is `TauCeti.perronIntegrand`.

## Main results

* `TauCeti.truncatedPerronKernel_one`: at `x = 1` the kernel is exactly
  `π⁻¹ * Real.arctan (T / c)`.
* `TauCeti.truncatedPerronKernel_one_ne_half`: consequently it is never `1 / 2`, at any finite
  height.  The value `1 / 2` conventionally attached to the endpoint `x = 1` is only a limit.
* `TauCeti.tendsto_truncatedPerronKernel_one`: that limit, as the height tends to infinity.
* `TauCeti.truncatedPerronKernel_im`: the kernel is real, because the integrand takes conjugate
  values at opposite heights.

## Roadmap role

This is the definitional half of Layer **6.3** of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`, together with the endpoint computation the
roadmap lists as its fourth rejection test.  The other half of 6.3 — the estimate exhibiting the
kernel as a smoothed step function with an explicit universal constant, for `x ≠ 1` — and the
arithmetic summatory form of Layer 6.4 are not proved here.

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

/-- A point of the vertical line `Re s = c` is nonzero as soon as `c` is.  Mathlib's
`Complex.ne_zero_of_re_pos` covers only the positive-real-part case. -/
private theorem ofReal_add_mul_I_ne_zero (hc : c ≠ 0) (t : ℝ) : (c : ℂ) + t * I ≠ 0 := fun h =>
  hc (by simpa using congrArg Complex.re h)

/-- At the endpoint `x = 1` the Perron integrand is the reciprocal of the point of the line. -/
@[simp]
theorem perronIntegrand_one (c t : ℝ) : perronIntegrand 1 c t = ((c : ℂ) + t * I)⁻¹ := by
  rw [perronIntegrand, Complex.ofReal_one, Complex.one_cpow, inv_eq_one_div]

/-- The modulus of the Perron integrand: the numerator contributes `x ^ c`, independently of the
height, and the denominator the distance from the origin to `c + i t`. -/
theorem norm_perronIntegrand (hx : 0 < x) (c t : ℝ) :
    ‖perronIntegrand x c t‖ = x ^ c / Real.sqrt (c ^ 2 + t ^ 2) := by
  rw [perronIntegrand, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_add_mul_I]
  simp

/-- The Perron integrand is continuous in the height along any vertical line off the imaginary
axis. -/
theorem continuous_perronIntegrand (hx : x ≠ 0) (hc : c ≠ 0) :
    Continuous (perronIntegrand x c) := by
  have hline : Continuous fun t : ℝ => (c : ℂ) + t * I :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hcpow : Continuous fun s : ℂ => (x : ℂ) ^ s :=
    continuous_iff_continuousAt.2 fun _ => continuousAt_const_cpow (mod_cast hx)
  exact (hcpow.comp hline).div hline fun t => ofReal_add_mul_I_ne_zero hc t

/-- The Perron integrand is integrable over every bounded piece of a vertical line off the
imaginary axis. -/
theorem intervalIntegrable_perronIntegrand (hx : x ≠ 0) (hc : c ≠ 0) (a b : ℝ) :
    IntervalIntegrable (perronIntegrand x c) volume a b :=
  (continuous_perronIntegrand hx hc).intervalIntegrable a b

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

/-- At zero height the truncated Perron kernel vanishes: the segment of integration is a point. -/
@[simp]
theorem truncatedPerronKernel_height_zero (x c : ℝ) : truncatedPerronKernel x c 0 = 0 := by
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
      (intervalIntegrable_perronIntegrand one_ne_zero hc.ne' _ _)
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

end TauCeti
