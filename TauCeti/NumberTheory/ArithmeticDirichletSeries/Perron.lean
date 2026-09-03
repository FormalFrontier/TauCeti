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
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The truncated Perron kernel

Perron's formula recovers a summatory function from a Dirichlet series by integrating `x ^ s / s`
up a vertical line.  At finite height the integral is not the sharp step function it approximates,
and this file makes the finite-height object visible before any estimate is applied to it.

`TauCeti.truncatedPerronKernel x c T` is the value of `(2πi)⁻¹ ∫ x ^ s / s ds` over the segment
from `c - iT` to `c + iT`.  Parameterizing that segment by `s = c + i t` with `t` real turns
`ds` into `i dt`, so the `i` in `(2πi)⁻¹` cancels and the visible prefactor is `(2π)⁻¹`; the
integrand along the segment is `TauCeti.perronIntegrand`.

Away from the endpoint the kernel is a smoothed step: it is close to `1` for `x > 1` and close to
`0` for `x < 1`, with an error that is proved here with the explicit constant `π⁻¹`.  Both
estimates come from moving the segment of integration horizontally, towards the side on which
`x ^ s` decays; for `x > 1` that move crosses the pole of `x ^ s / s` at the origin, and the
residue is what produces the step.

## Main results

* `TauCeti.truncatedPerronKernel_one`: at `x = 1` the kernel is exactly
  `π⁻¹ * Real.arctan (T / c)`.
* `TauCeti.truncatedPerronKernel_one_ne_half`: consequently it is never `1 / 2`, at any finite
  height.  The value `1 / 2` conventionally attached to the endpoint `x = 1` is only a limit.
* `TauCeti.tendsto_truncatedPerronKernel_one`: that limit, as the height tends to infinity.
* `TauCeti.truncatedPerronKernel_im`: the kernel is real, because the integrand takes conjugate
  values at opposite heights.
* `TauCeti.norm_truncatedPerronKernel_sub_step_le`: the smoothed-step estimate
  `‖K x c T - perronStep x‖ ≤ x ^ c / (π * T * |log x|)` for `x ≠ 1`, together with its two halves
  `TauCeti.norm_truncatedPerronKernel_le_of_lt_one` and
  `TauCeti.norm_truncatedPerronKernel_sub_one_le_of_one_lt`.
* `TauCeti.tendsto_truncatedPerronKernel`: consequently the kernel tends to the sharp step
  `TauCeti.perronStep`, which carries the customary half-weight at the endpoint, as the height
  tends to infinity, at every positive `x`.

## Roadmap role

This is Layer **6.3** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`: the finite-height
kernel, the endpoint computation the roadmap lists as its fourth rejection test, and the
smoothed-step estimate with a proved universal constant.  The arithmetic summatory form of Layer
6.4, which interchanges this integral with an absolutely convergent `LSeries`, is not proved here.

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
private theorem ofReal_add_mul_I_ne_zero_of_re (hc : c ≠ 0) (t : ℝ) : (c : ℂ) + t * I ≠ 0 :=
  fun h => hc (by simpa using congrArg Complex.re h)

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
  exact (hcpow.comp hline).div hline fun t => ofReal_add_mul_I_ne_zero_of_re hc t

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

/-- On the line `Re s = c` off the imaginary axis, the map
`t ↦ arctan (t / c) - (i / 2) * log (c ^ 2 + t ^ 2)` is a primitive of the Perron integrand at
`x = 1`; its real part contributes the arctangent and its imaginary part cancels over a symmetric
interval. -/
private theorem hasDerivAt_perronPrimitive (hc : c ≠ 0) (t : ℝ) :
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
  have hne : ((c : ℂ) + t * I) ≠ 0 := ofReal_add_mul_I_ne_zero_of_re hc t
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
theorem truncatedPerronKernel_one (hc : c ≠ 0) (T : ℝ) :
    truncatedPerronKernel 1 c T = (π⁻¹ * Real.arctan (T / c) : ℝ) := by
  have hint : (∫ t in -T..T, perronIntegrand 1 c t)
      = ((Real.arctan (T / c) : ℂ) - I / 2 * (Real.log (c ^ 2 + T ^ 2) : ℂ))
        - ((Real.arctan (-T / c) : ℂ) - I / 2 * (Real.log (c ^ 2 + (-T) ^ 2) : ℂ)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hasDerivAt_perronPrimitive hc u)
      (intervalIntegrable_perronIntegrand one_ne_zero hc _ _)
  rw [truncatedPerronKernel, hint, neg_div, Real.arctan_neg, neg_sq]
  have hpi : (π : ℂ) ≠ 0 := mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-- At any finite height the Perron kernel at the endpoint `x = 1` is not `1 / 2`; the customary
half-weight there is only the limit `TauCeti.tendsto_truncatedPerronKernel_one`. -/
theorem truncatedPerronKernel_one_ne_half (hc : 0 < c) (T : ℝ) :
    truncatedPerronKernel 1 c T ≠ 1 / 2 := by
  rw [truncatedPerronKernel_one hc.ne']
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
  exact hcplx.congr fun T => (truncatedPerronKernel_one hc.ne' T).symm

/-!
### Moving the segment sideways

The estimates below all rest on the same device: the integral of `x ^ s / s` over the boundary of
a rectangle vanishes when the origin is outside it, so the segment of integration may be pushed
horizontally at the cost of the two horizontal sides.  The material of this section is the book
keeping that device needs: the integrand as a function of `s`, its size on horizontal and
vertical sides, and the integral of `x ^ σ` that bounds a horizontal side.
-/

variable {T a b : ℝ}

/-- The Perron integrand as a function of the complex variable: `s ↦ x ^ s / s`, of which
`TauCeti.perronIntegrand` is the restriction to a vertical line. -/
private noncomputable def perronFn (x : ℝ) (s : ℂ) : ℂ := (x : ℂ) ^ s / s

private theorem perronIntegrand_eq_perronFn (x c t : ℝ) :
    perronIntegrand x c t = perronFn x ((c : ℂ) + t * I) := rfl

private theorem perronFn_one (s : ℂ) : perronFn 1 s = s⁻¹ := by
  rw [perronFn, Complex.ofReal_one, Complex.one_cpow, inv_eq_one_div]

/-- A point of the horizontal line `Im s = T` is nonzero as soon as `T` is. -/
private theorem ofReal_add_mul_I_ne_zero_of_im (hT : T ≠ 0) (σ : ℝ) : (σ : ℂ) + T * I ≠ 0 :=
  fun h => hT (by simpa using congrArg Complex.im h)

private theorem norm_perronFn (hx : 0 < x) (s : ℂ) : ‖perronFn x s‖ = x ^ s.re / ‖s‖ := by
  rw [perronFn, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]

private theorem norm_perronFn_le_re (hx : 0 < x) {s : ℂ} (hs : s.re ≠ 0) :
    ‖perronFn x s‖ ≤ x ^ s.re / |s.re| := by
  rw [norm_perronFn hx]
  gcongr
  exact Complex.abs_re_le_norm s

private theorem norm_perronFn_le_im (hx : 0 < x) {s : ℂ} (hs : s.im ≠ 0) :
    ‖perronFn x s‖ ≤ x ^ s.re / |s.im| := by
  rw [norm_perronFn hx]
  gcongr
  exact Complex.abs_im_le_norm s

private theorem differentiable_ofReal_cpow (hx : x ≠ 0) :
    Differentiable ℂ fun s : ℂ => (x : ℂ) ^ s :=
  differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.2 hx))

private theorem differentiableAt_perronFn (hx : x ≠ 0) {s : ℂ} (hs : s ≠ 0) :
    DifferentiableAt ℂ (perronFn x) s :=
  ((differentiable_ofReal_cpow hx) s).div differentiableAt_id hs

private theorem continuous_perronFn_comp (hx : x ≠ 0) {g : ℝ → ℂ} (hg : Continuous g)
    (hg0 : ∀ t, g t ≠ 0) : Continuous fun t => perronFn x (g t) :=
  (((differentiable_ofReal_cpow hx).continuous).comp hg).div hg hg0

private theorem intervalIntegrable_perronFn_comp (hx : x ≠ 0) {g : ℝ → ℂ} (hg : Continuous g)
    (hg0 : ∀ t, g t ≠ 0) (u v : ℝ) :
    IntervalIntegrable (fun t => perronFn x (g t)) volume u v :=
  (continuous_perronFn_comp hx hg hg0).intervalIntegrable u v

private theorem continuous_horizontalLine (T : ℝ) : Continuous fun σ : ℝ => (σ : ℂ) + T * I :=
  Complex.continuous_ofReal.add continuous_const

private theorem continuous_verticalLine (c : ℝ) : Continuous fun t : ℝ => (c : ℂ) + t * I :=
  continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

/-- The integral of `σ ↦ x ^ σ` along a horizontal side, in closed form. -/
private theorem integral_rpow_const_base (hx : 0 < x) (hx1 : x ≠ 1) (a b : ℝ) :
    (∫ σ in a..b, x ^ σ) = (x ^ b - x ^ a) / Real.log x := by
  have hlog : Real.log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hx hx1
  have hderiv : ∀ σ : ℝ, HasDerivAt (fun u : ℝ => x ^ u / Real.log x) (x ^ σ) σ := fun σ => by
    refine (((hasDerivAt_id σ).const_rpow hx).div_const (Real.log x)).congr_deriv ?_
    simp only [id_eq]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun σ _ => hderiv σ)
    ((Real.continuous_const_rpow hx.ne').intervalIntegrable a b), sub_div]

/-- A horizontal side of the rectangle contributes at most `|T|⁻¹` times the integral of
`x ^ σ`. -/
private theorem norm_integral_perronFn_horizontal_le (hx : 0 < x) (hT : T ≠ 0) (hab : a ≤ b) :
    ‖∫ σ in a..b, perronFn x ((σ : ℂ) + T * I)‖ ≤ (∫ σ in a..b, x ^ σ) / |T| := by
  rw [← intervalIntegral.integral_div]
  refine intervalIntegral.norm_integral_le_of_norm_le hab (.of_forall fun σ _ => ?_)
    (((Real.continuous_const_rpow hx.ne').div_const _).intervalIntegrable a b)
  simpa using norm_perronFn_le_im hx (s := (σ : ℂ) + T * I) (by simpa using hT)

/-- A vertical side of the rectangle contributes at most its length times `x ^ c / |c|`. -/
private theorem norm_integral_perronFn_vertical_le (hx : 0 < x) (hc : c ≠ 0) (hT : 0 ≤ T) :
    ‖∫ t in (-T)..T, perronFn x ((c : ℂ) + t * I)‖ ≤ x ^ c / |c| * (2 * T) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ => perronFn x ((c : ℂ) + t * I)) (C := x ^ c / |c|) (a := -T) (b := T)
    fun t _ => by simpa using norm_perronFn_le_re hx (s := (c : ℂ) + t * I) (by simpa using hc)
  -- `norm_integral_le_of_norm_le_const` measures the segment by `|b - a|`; here that is `2 * T`.
  have hlen : |T - -T| = 2 * T := by
    rw [sub_neg_eq_add, abs_of_nonneg (by linarith : (0 : ℝ) ≤ T + T)]
    ring
  rwa [hlen] at h

/-- The Cauchy–Goursat theorem for the rectangle with horizontal sides at heights `±T` and
vertical sides at abscissae `a` and `b`, in the parameterization used throughout this file. -/
private theorem integral_perronRectangle_eq_zero (f : ℂ → ℂ) (a b T : ℝ)
    (hf : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc (-T) T)) :
    ((∫ σ in a..b, f ((σ : ℂ) + (-T : ℝ) * I)) - ∫ σ in a..b, f ((σ : ℂ) + (T : ℝ) * I))
        + I * (∫ t in (-T)..T, f ((b : ℂ) + t * I)) - I * ∫ t in (-T)..T, f ((a : ℂ) + t * I)
      = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨a, -T⟩ ⟨b, T⟩
    (by simpa using hf)
  simpa [smul_eq_mul] using h

private theorem norm_I_mul (z : ℂ) : ‖I * z‖ = ‖z‖ := by
  rw [norm_mul, Complex.norm_I, one_mul]

/-- The triangle inequality in the shape in which the three surviving sides of the rectangle are
combined: two horizontal sides and one vertical one. -/
private theorem norm_sub_add_I_mul_le (u v w : ℂ) : ‖u - v + I * w‖ ≤ ‖u‖ + ‖v‖ + ‖w‖ := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_I_mul]
  gcongr
  exact norm_sub_le u v

/-!
### Below the endpoint

For `x < 1` the function `x ^ s` decays as `Re s` grows, so the segment may be pushed to the line
`Re s = B` with `B → ∞`.  The far side then vanishes in the limit and only the two horizontal
sides survive; each of them is at most `x ^ c / (T * |log x|)`.
-/

private theorem norm_integral_perronFn_le_of_lt_one (hx : 0 < x) (hx1 : x < 1) (hc : 0 < c)
    (hT : 0 < T) :
    ‖∫ t in (-T)..T, perronFn x ((c : ℂ) + t * I)‖ ≤ 2 * (x ^ c / (T * |Real.log x|)) := by
  have hlogneg : Real.log x < 0 := Real.log_neg hx hx1
  have hL : 0 < |Real.log x| := abs_pos.2 hlogneg.ne
  have key : ∀ B, c ≤ B → ‖∫ t in (-T)..T, perronFn x ((c : ℂ) + t * I)‖
      ≤ 2 * (x ^ c / (T * |Real.log x|)) + x ^ B / c * (2 * T) := by
    intro B hcB
    have hB0 : 0 < B := lt_of_lt_of_le hc hcB
    have hdiff : DifferentiableOn ℂ (perronFn x) (Set.uIcc c B ×ℂ Set.uIcc (-T) T) := by
      intro s hs
      refine (differentiableAt_perronFn hx.ne' ?_).differentiableWithinAt
      have hre : s.re ∈ Set.uIcc c B := hs.1
      rw [Set.uIcc_of_le hcB] at hre
      have hpos : 0 < s.re := lt_of_lt_of_le hc hre.1
      exact fun h0 => by simp [h0] at hpos
    have hcauchy := integral_perronRectangle_eq_zero (perronFn x) c B T hdiff
    -- Cauchy's theorem rewrites the segment as the far side plus the two horizontal sides.
    have hsplit : I * ∫ t in (-T)..T, perronFn x ((c : ℂ) + t * I)
        = ((∫ σ in c..B, perronFn x ((σ : ℂ) + (-T : ℝ) * I))
            - ∫ σ in c..B, perronFn x ((σ : ℂ) + (T : ℝ) * I))
          + I * ∫ t in (-T)..T, perronFn x ((B : ℂ) + t * I) := by
      linear_combination -hcauchy
    have hhoriz : ∀ u : ℝ, u ≠ 0 → |u| = T →
        ‖∫ σ in c..B, perronFn x ((σ : ℂ) + u * I)‖ ≤ x ^ c / (T * |Real.log x|) := by
      intro u hu habs
      refine (norm_integral_perronFn_horizontal_le hx hu hcB).trans ?_
      -- `log x` is negative here, so moving to `|log x|` also swaps the two powers.
      have hflip : (x ^ B - x ^ c) / Real.log x = (x ^ c - x ^ B) / |Real.log x| := by
        rw [abs_of_neg hlogneg]
        ring
      rw [habs, integral_rpow_const_base hx hx1.ne, hflip]
      have hxB : 0 ≤ x ^ B := Real.rpow_nonneg hx.le B
      calc (x ^ c - x ^ B) / |Real.log x| / T ≤ x ^ c / |Real.log x| / T := by
            gcongr
            linarith
        _ = x ^ c / (T * |Real.log x|) := by ring
    have hfar : ‖∫ t in (-T)..T, perronFn x ((B : ℂ) + t * I)‖ ≤ x ^ B / c * (2 * T) := by
      refine (norm_integral_perronFn_vertical_le hx hB0.ne' hT.le).trans ?_
      rw [abs_of_pos hB0]
      gcongr
    rw [← norm_I_mul (∫ t in (-T)..T, perronFn x ((c : ℂ) + t * I)), hsplit]
    refine (norm_sub_add_I_mul_le _ _ _).trans ?_
    have h₁ := hhoriz (-T) (neg_ne_zero.2 hT.ne') (by rw [abs_neg, abs_of_pos hT])
    have h₂ := hhoriz T hT.ne' (abs_of_pos hT)
    linarith
  have hlim : Tendsto (fun B : ℝ => 2 * (x ^ c / (T * |Real.log x|)) + x ^ B / c * (2 * T)) atTop
      (𝓝 (2 * (x ^ c / (T * |Real.log x|)))) := by
    have h0 : Tendsto (fun B : ℝ => x ^ B) atTop (𝓝 0) :=
      tendsto_rpow_atTop_of_base_lt_one x (by linarith) hx1
    simpa using tendsto_const_nhds.add ((h0.div_const c).mul tendsto_const_nhds)
  exact ge_of_tendsto hlim (eventually_atTop.2 ⟨c, key⟩)

/-- **Below the endpoint the truncated Perron kernel is small.**  For `0 < x < 1` it differs from
`0` by at most `x ^ c / (π * T * |log x|)`. -/
theorem norm_truncatedPerronKernel_le_of_lt_one (hx : 0 < x) (hx1 : x < 1) (hc : 0 < c)
    (hT : 0 < T) : ‖truncatedPerronKernel x c T‖ ≤ x ^ c / (π * T * |Real.log x|) := by
  have hL : 0 < |Real.log x| := abs_pos.2 (Real.log_neg hx hx1).ne
  have hnorm : ‖((2 * π : ℝ) : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [truncatedPerronKernel, norm_mul, hnorm]
  simp only [perronIntegrand_eq_perronFn]
  calc (2 * π)⁻¹ * ‖∫ t in (-T)..T, perronFn x ((c : ℂ) + t * I)‖
      ≤ (2 * π)⁻¹ * (2 * (x ^ c / (T * |Real.log x|))) := by
        gcongr
        exact norm_integral_perronFn_le_of_lt_one hx hx1 hc hT
    _ = x ^ c / (π * T * |Real.log x|) := by
        have hπ : π ≠ 0 := Real.pi_ne_zero
        have hT' : T ≠ 0 := hT.ne'
        have hL' : |Real.log x| ≠ 0 := hL.ne'
        field_simp

/-!
### Above the endpoint

For `x > 1` the function `x ^ s` decays as `Re s` decreases, so the segment is pushed to the left
instead.  That move crosses the pole of `x ^ s / s` at the origin.  Rather than invoke a residue
theorem, the integrand is split as `(x ^ s - 1) / s + 1 / s`: the first summand extends across the
origin as `dslope`, so Cauchy's theorem applies to it verbatim, and the second is integrated in
closed form, its four sides contributing the four arctangents that add up to `2 π i`.
-/

private theorem arctan_div_add_arctan_div (ha : 0 < a) (hb : 0 < b) :
    Real.arctan (a / b) + Real.arctan (b / a) = π / 2 := by
  rw [← inv_div a b, Real.arctan_inv_of_pos (by positivity)]
  ring

/-- The Perron integrand with its pole removed: `s ↦ (x ^ s - 1) / s`, given the value `log x` at
the origin.  Off the origin it is the difference of the integrands at `x` and at `1`. -/
private noncomputable def perronDslope (x : ℝ) : ℂ → ℂ := dslope (fun s : ℂ => (x : ℂ) ^ s) 0

private theorem perronDslope_eq_sub {s : ℂ} (hs : s ≠ 0) :
    perronDslope x s = perronFn x s - perronFn 1 s := by
  rw [perronDslope, dslope_of_ne _ hs, slope_def_field, perronFn_one, perronFn, Complex.cpow_zero,
    sub_zero, sub_div, one_div]

private theorem differentiable_perronDslope (hx : x ≠ 0) : Differentiable ℂ (perronDslope x) := by
  rw [perronDslope, ← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope Filter.univ_mem).2
    (differentiable_ofReal_cpow hx).differentiableOn

private theorem integral_perronDslope_comp (hx : 0 < x) {g : ℝ → ℂ} (hg : Continuous g)
    (hg0 : ∀ t, g t ≠ 0) (u v : ℝ) :
    (∫ t in u..v, perronDslope x (g t))
      = (∫ t in u..v, perronFn x (g t)) - ∫ t in u..v, perronFn 1 (g t) := by
  rw [← intervalIntegral.integral_sub (intervalIntegrable_perronFn_comp hx.ne' hg hg0 u v)
    (intervalIntegrable_perronFn_comp one_ne_zero hg hg0 u v)]
  exact intervalIntegral.integral_congr fun t _ => perronDslope_eq_sub (hg0 t)

/-- A vertical side contributes `2 arctan (T / c)` to the integral of `1 / s`. -/
private theorem integral_perronFn_one_vertical (hc : c ≠ 0) (T : ℝ) :
    (∫ t in (-T)..T, perronFn 1 ((c : ℂ) + t * I)) = 2 * Real.arctan (T / c) := by
  have h := truncatedPerronKernel_one hc T
  rw [truncatedPerronKernel] at h
  simp only [perronIntegrand_eq_perronFn] at h
  have hpi : ((2 * π : ℝ) : ℂ) ≠ 0 := by simp
  have h' := congrArg (fun z : ℂ => ((2 * π : ℝ) : ℂ) * z) h
  simp only [← mul_assoc, mul_inv_cancel₀ hpi, one_mul] at h'
  rw [h']
  have hπ : (π : ℂ) ≠ 0 := mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- The two horizontal sides contribute the two remaining arctangents to the integral of
`1 / s`. -/
private theorem integral_perronFn_one_horizontal_diff (hT : T ≠ 0) (a b : ℝ) :
    ((∫ σ in a..b, perronFn 1 ((σ : ℂ) + (-T : ℝ) * I))
        - ∫ σ in a..b, perronFn 1 ((σ : ℂ) + (T : ℝ) * I))
      = 2 * I * ((Real.arctan (b / T) : ℂ) - (Real.arctan (a / T) : ℂ)) := by
  have hcont : ∀ u : ℝ, u ≠ 0 →
      IntervalIntegrable (fun σ : ℝ => perronFn 1 ((σ : ℂ) + u * I)) volume a b := fun u hu =>
    intervalIntegrable_perronFn_comp one_ne_zero (continuous_horizontalLine u)
      (ofReal_add_mul_I_ne_zero_of_im hu) a b
  rw [← intervalIntegral.integral_sub (hcont _ (neg_ne_zero.2 hT)) (hcont _ hT)]
  have hderiv : ∀ σ : ℝ, HasDerivAt (fun u : ℝ => 2 * I * (Real.arctan (u / T) : ℂ))
      (perronFn 1 ((σ : ℂ) + (-T : ℝ) * I) - perronFn 1 ((σ : ℂ) + (T : ℝ) * I)) σ := by
    intro σ
    have harctan : HasDerivAt (fun u : ℝ => Real.arctan (u / T)) (T / (T ^ 2 + σ ^ 2)) σ := by
      have h := ((hasDerivAt_id σ).div_const T).arctan
      simp only [id_eq] at h
      refine h.congr_deriv ?_
      field_simp
    refine (harctan.ofReal_comp.const_mul (2 * I)).congr_deriv ?_
    have hne₁ : ((σ : ℂ) + -(T : ℂ) * I) ≠ 0 := by
      simpa using ofReal_add_mul_I_ne_zero_of_im (neg_ne_zero.2 hT) σ
    have hne₂ : ((σ : ℂ) + (T : ℂ) * I) ≠ 0 := ofReal_add_mul_I_ne_zero_of_im hT σ
    have hsq : ((T : ℂ) ^ 2 + (σ : ℂ) ^ 2) ≠ 0 := by
      have h : (0 : ℝ) < T ^ 2 + σ ^ 2 := by positivity
      simpa using Complex.ofReal_ne_zero.2 h.ne'
    have key : ((σ : ℂ) + -(T : ℂ) * I) * ((σ : ℂ) + (T : ℂ) * I) = (T : ℂ) ^ 2 + (σ : ℂ) ^ 2 := by
      linear_combination (-(T : ℂ) ^ 2) * Complex.I_sq
    rw [perronFn_one, perronFn_one]
    push_cast
    rw [inv_sub_inv hne₁ hne₂, key]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun σ _ => hderiv σ)
    (((hcont _ (neg_ne_zero.2 hT)).sub (hcont _ hT)))]
  ring

private theorem norm_integral_perronFn_sub_two_pi_le_of_one_lt (hx1 : 1 < x) (hc : 0 < c)
    (hT : 0 < T) :
    ‖(∫ t in (-T)..T, perronFn x ((c : ℂ) + t * I)) - 2 * π‖
      ≤ 2 * (x ^ c / (T * |Real.log x|)) := by
  have hx : 0 < x := lt_trans zero_lt_one hx1
  have hL : |Real.log x| = Real.log x := abs_of_pos (Real.log_pos hx1)
  have key : ∀ B, c ≤ B → ‖(∫ t in (-T)..T, perronFn x ((c : ℂ) + t * I)) - 2 * π‖
      ≤ 2 * (x ^ c / (T * |Real.log x|)) + x ^ (-B) / c * (2 * T) := by
    intro B hcB
    have hB0 : 0 < B := lt_of_lt_of_le hc hcB
    have hab : (-B : ℝ) ≤ c := by linarith
    have hcauchy := integral_perronRectangle_eq_zero (perronDslope x) (-B) c T
      (differentiable_perronDslope hx.ne').differentiableOn
    -- Split the entire integrand into the integrand at `x` and the integrand at `1`.
    rw [integral_perronDslope_comp hx (continuous_horizontalLine (-T))
        (ofReal_add_mul_I_ne_zero_of_im (neg_ne_zero.2 hT.ne')),
      integral_perronDslope_comp hx (continuous_horizontalLine T)
        (ofReal_add_mul_I_ne_zero_of_im hT.ne'),
      integral_perronDslope_comp hx (continuous_verticalLine c)
        (ofReal_add_mul_I_ne_zero_of_re hc.ne'),
      integral_perronDslope_comp hx (continuous_verticalLine (-B))
        (ofReal_add_mul_I_ne_zero_of_re (neg_ne_zero.2 hB0.ne'))] at hcauchy
    -- The four sides of the integrand at `1` contribute the residue `2 π i`.
    have e₁ := integral_perronFn_one_horizontal_diff hT.ne' (-B) c
    have e₂ := integral_perronFn_one_vertical hc.ne' T
    have e₃ := integral_perronFn_one_vertical (neg_ne_zero.2 hB0.ne') T
    have hres : 2 * I * ((Real.arctan (c / T) : ℂ) - (Real.arctan (-B / T) : ℂ))
        + I * (2 * (Real.arctan (T / c) : ℂ)) - I * (2 * (Real.arctan (T / -B) : ℂ))
        = 2 * π * I := by
      have hA : ((Real.arctan (c / T) : ℝ) : ℂ) + ((Real.arctan (T / c) : ℝ) : ℂ)
          = (π : ℂ) / 2 := by
        rw [← Complex.ofReal_add, arctan_div_add_arctan_div hc hT]
        push_cast
        ring
      have hB : ((Real.arctan (B / T) : ℝ) : ℂ) + ((Real.arctan (T / B) : ℝ) : ℂ)
          = (π : ℂ) / 2 := by
        rw [← Complex.ofReal_add, arctan_div_add_arctan_div hB0 hT]
        push_cast
        ring
      rw [neg_div, Real.arctan_neg, div_neg, Real.arctan_neg]
      push_cast
      linear_combination (2 * I) * hA + (2 * I) * hB
    have hmain : I * ((∫ t in (-T)..T, perronFn x ((c : ℂ) + t * I)) - 2 * π)
        = (∫ σ in (-B)..c, perronFn x ((σ : ℂ) + (T : ℝ) * I))
          - (∫ σ in (-B)..c, perronFn x ((σ : ℂ) + (-T : ℝ) * I))
          + I * ∫ t in (-T)..T, perronFn x (((-B : ℝ) : ℂ) + t * I) := by
      linear_combination hcauchy + e₁ + I * e₂ - I * e₃ + hres
    have hhoriz : ∀ u : ℝ, u ≠ 0 → |u| = T →
        ‖∫ σ in (-B)..c, perronFn x ((σ : ℂ) + u * I)‖ ≤ x ^ c / (T * |Real.log x|) := by
      intro u hu habs
      refine (norm_integral_perronFn_horizontal_le hx hu hab).trans ?_
      rw [habs, hL, integral_rpow_const_base hx hx1.ne']
      have hxB : 0 < x ^ (-B) := Real.rpow_pos_of_pos hx _
      have hlog : 0 < Real.log x := Real.log_pos hx1
      calc (x ^ c - x ^ (-B)) / Real.log x / T ≤ x ^ c / Real.log x / T := by
            gcongr
            linarith
        _ = x ^ c / (T * Real.log x) := by ring
    have hfar : ‖∫ t in (-T)..T, perronFn x (((-B : ℝ) : ℂ) + t * I)‖
        ≤ x ^ (-B) / c * (2 * T) := by
      refine (norm_integral_perronFn_vertical_le hx (neg_ne_zero.2 hB0.ne') hT.le).trans ?_
      rw [abs_neg, abs_of_pos hB0]
      gcongr
    rw [← norm_I_mul ((∫ t in (-T)..T, perronFn x ((c : ℂ) + t * I)) - 2 * π), hmain]
    refine (norm_sub_add_I_mul_le _ _ _).trans ?_
    have h₁ := hhoriz (-T) (neg_ne_zero.2 hT.ne') (by rw [abs_neg, abs_of_pos hT])
    have h₂ := hhoriz T hT.ne' (abs_of_pos hT)
    linarith
  have hlim : Tendsto (fun B : ℝ => 2 * (x ^ c / (T * |Real.log x|)) + x ^ (-B) / c * (2 * T))
      atTop (𝓝 (2 * (x ^ c / (T * |Real.log x|)))) := by
    have h0 : Tendsto (fun B : ℝ => x ^ (-B)) atTop (𝓝 0) := by
      refine (tendsto_rpow_atTop_of_base_gt_one x hx1).inv_tendsto_atTop.congr fun B => ?_
      rw [Pi.inv_apply, ← Real.rpow_neg hx.le]
    simpa using tendsto_const_nhds.add ((h0.div_const c).mul tendsto_const_nhds)
  exact ge_of_tendsto hlim (eventually_atTop.2 ⟨c, key⟩)

/-- **Above the endpoint the truncated Perron kernel is close to one.**  For `1 < x` it differs
from `1` by at most `x ^ c / (π * T * |log x|)`. -/
theorem norm_truncatedPerronKernel_sub_one_le_of_one_lt (hx1 : 1 < x) (hc : 0 < c) (hT : 0 < T) :
    ‖truncatedPerronKernel x c T - 1‖ ≤ x ^ c / (π * T * |Real.log x|) := by
  have hL : 0 < |Real.log x| := abs_pos.2 (Real.log_pos hx1).ne'
  have hpi : ((2 * π : ℝ) : ℂ) ≠ 0 := by simp
  have hnorm : ‖((2 * π : ℝ) : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hrw : truncatedPerronKernel x c T - 1
      = ((2 * π : ℝ) : ℂ)⁻¹ * ((∫ t in (-T)..T, perronFn x ((c : ℂ) + t * I)) - 2 * π) := by
    have hcancel : ((2 * π : ℝ) : ℂ)⁻¹ * (2 * (π : ℂ)) = 1 := by
      -- The factor `2 * π` reaches the goal built up in `ℂ`, not pushed through the coercion.
      have hcast : (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, inv_mul_cancel₀ hpi]
    rw [truncatedPerronKernel]
    simp only [perronIntegrand_eq_perronFn]
    rw [mul_sub, hcancel]
  rw [hrw, norm_mul, hnorm]
  calc (2 * π)⁻¹ * ‖(∫ t in (-T)..T, perronFn x ((c : ℂ) + t * I)) - 2 * π‖
      ≤ (2 * π)⁻¹ * (2 * (x ^ c / (T * |Real.log x|))) := by
        gcongr
        exact norm_integral_perronFn_sub_two_pi_le_of_one_lt hx1 hc hT
    _ = x ^ c / (π * T * |Real.log x|) := by
        have hπ : π ≠ 0 := Real.pi_ne_zero
        have hT' : T ≠ 0 := hT.ne'
        have hL' : |Real.log x| ≠ 0 := hL.ne'
        field_simp

/-- The sharp step that the truncated Perron kernel approximates: `1` above the endpoint, `0`
below it, and the customary Perron half-weight `1 / 2` at the endpoint `x = 1`, which is the
value the kernel tends to there (`TauCeti.tendsto_truncatedPerronKernel_one`) even though it
never attains it at finite height (`TauCeti.truncatedPerronKernel_one_ne_half`). -/
noncomputable def perronStep (x : ℝ) : ℂ := if 1 < x then 1 else if x = 1 then 1 / 2 else 0

@[simp]
theorem perronStep_of_one_lt (hx : 1 < x) : perronStep x = 1 := by
  simp [perronStep, hx]

@[simp]
theorem perronStep_one : perronStep 1 = 1 / 2 := by
  simp [perronStep]

@[simp]
theorem perronStep_of_lt_one (hx : x < 1) : perronStep x = 0 := by
  simp [perronStep, not_lt.2 hx.le, hx.ne]

/-- **The truncated Perron kernel is a smoothed step.**  Away from the endpoint `x = 1` it differs
from `TauCeti.perronStep` by at most `x ^ c / (π * T * |log x|)`.

The endpoint `x = 1` is genuinely excluded: there the error is `|π⁻¹ arctan (T / c) - 1 / 2|`,
which no bound of this shape controls, and the kernel never attains the half-weight
(`TauCeti.truncatedPerronKernel_one_ne_half`). -/
theorem norm_truncatedPerronKernel_sub_step_le (hx : 0 < x) (hx1 : x ≠ 1) (hc : 0 < c)
    (hT : 0 < T) :
    ‖truncatedPerronKernel x c T - perronStep x‖ ≤ x ^ c / (π * T * |Real.log x|) := by
  rcases hx1.lt_or_gt with h | h
  · simpa [perronStep_of_lt_one h] using norm_truncatedPerronKernel_le_of_lt_one hx h hc hT
  · simpa [perronStep_of_one_lt h] using norm_truncatedPerronKernel_sub_one_le_of_one_lt h hc hT

/-- As the height tends to infinity the truncated Perron kernel tends to the sharp step, at every
positive `x`; at the endpoint `x = 1` this is the half-weight limit
`TauCeti.tendsto_truncatedPerronKernel_one`. -/
theorem tendsto_truncatedPerronKernel (hx : 0 < x) (hc : 0 < c) :
    Tendsto (truncatedPerronKernel x c) atTop (𝓝 (perronStep x)) := by
  rcases eq_or_ne x 1 with rfl | hx1
  · rw [perronStep_one]
    exact tendsto_truncatedPerronKernel_one hc
  have hL : 0 < |Real.log x| := abs_pos.2 (Real.log_ne_zero_of_pos_of_ne_one hx hx1)
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' (eventually_atTop.2 ⟨1, fun T hT =>
    norm_truncatedPerronKernel_sub_step_le hx hx1 hc (lt_of_lt_of_le zero_lt_one hT)⟩) ?_
  have hbig : Tendsto (fun T : ℝ => π * T * |Real.log x|) atTop atTop :=
    Filter.Tendsto.atTop_mul_const hL (Filter.Tendsto.const_mul_atTop Real.pi_pos tendsto_id)
  simpa [div_eq_mul_inv] using hbig.inv_tendsto_atTop.const_mul (x ^ c)

end TauCeti
