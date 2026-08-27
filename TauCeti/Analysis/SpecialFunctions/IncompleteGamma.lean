/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import TauCeti.Analysis.SpecialFunctions.Erf

/-!
# The lower incomplete gamma function

For a positive shape parameter `s` this file introduces

* `TauCeti.lowerIncompleteGamma s x = ∫ t in 0..x, t ^ (s - 1) * exp (-t)`, the truncation of
  Euler's integral at `x`, extended by `0` for `x ≤ 0` and for `s ≤ 0`; and
* `TauCeti.regularizedGamma s x = lowerIncompleteGamma s x / Real.Gamma s`, its normalization,
  again extended by `0` for `s ≤ 0`.

Classically these are `γ(s, x)` and `P(s, x)`. The regularized function is the cumulative
distribution function of a Gamma law, which is where this file is headed; the two totalizations
above make that cdf agree with the clamping conventions a cdf needs, below the support and outside
the parameter range.

## Main definitions

* `TauCeti.lowerIncompleteGamma` — the lower incomplete gamma function `γ(s, x)`;
* `TauCeti.regularizedGamma` — the regularized lower incomplete gamma function `P(s, x)`.

## Main results

* `TauCeti.lowerIncompleteGamma_eq_integral` and `TauCeti.regularizedGamma_eq_div` — the
  characteristic descriptions replacing the clamped definitions;
* `TauCeti.intervalIntegrable_rpow_mul_exp_neg` — convergence of Euler's integrand on an interval,
  including at the singularity `0` for `s < 1`;
* `TauCeti.continuous_lowerIncompleteGamma`, `TauCeti.continuous_regularizedGamma` — continuity on
  all of `ℝ`, in particular at `x = 0`, where for `s < 1` the integrand blows up;
* `TauCeti.lowerIncompleteGamma_monotone`, `TauCeti.regularizedGamma_monotone` — monotonicity,
  and `TauCeti.lowerIncompleteGamma_nonneg`, `TauCeti.regularizedGamma_nonneg`,
  `TauCeti.regularizedGamma_le_one` — the range;
* `TauCeti.hasDerivAt_lowerIncompleteGamma`, `TauCeti.hasDerivAt_regularizedGamma` and the
  companion `deriv` lemmas — differentiability, for `0 < x` only;
* `TauCeti.lowerIncompleteGamma_add_one` and `TauCeti.regularizedGamma_add_one` — the recurrence
  `γ(s + 1, x) = s * γ(s, x) - x ^ s * exp (-x)` and its regularized form
  `P(s + 1, x) = P(s, x) - x ^ s * exp (-x) / Γ(s + 1)`, both for `0 < s` and `0 ≤ x`;
* `TauCeti.tendsto_lowerIncompleteGamma_atTop`, `TauCeti.tendsto_regularizedGamma_atTop` — the
  limits `Real.Gamma s` and `1` as `x → ∞`, with the resulting bounds
  `TauCeti.lowerIncompleteGamma_le_Gamma` and `TauCeti.regularizedGamma_le_one`;
* `TauCeti.regularizedGamma_one` — `P(1, x) = 1 - e ^ (-x)` for `0 ≤ x`, the exponential cdf.
* `TauCeti.Real.erf_eq_regularizedGamma_half_sq` — the error function is the regularized
  incomplete gamma function of shape `1 / 2` after squaring, on the nonnegative half-line.

## Implementation

The guard `0 < s` in the definition of `regularizedGamma` mirrors the one built into
`TauCeti.lowerIncompleteGamma`, which is the definition shape the roadmap prescribes. It changes no
value: `γ(s, x)` already vanishes for `s ≤ 0`, so dividing unconditionally would give the same
function, and `TauCeti.regularizedGamma_eq_div` accordingly needs no hypothesis on `s`.

The limit at infinity is Mathlib's `Real.GammaIntegral_convergent` together with
`Real.Gamma_eq_integral`, which state Euler's integrand as `exp (-t) * t ^ (s - 1)`; this file uses
the opposite factor order throughout, so both are applied up to `mul_comm` at their point of use.

The recurrence is obtained from Mathlib's `Complex.partialGamma_add_one`, whose proof performs the
integration by parts on `Set.Ioo 0 x` — the endpoint `0` has to be avoided because `t ^ s` is not
differentiable there for `s < 1`. The bridge is
`TauCeti.ofReal_lowerIncompleteGamma_eq_partialGamma`, which identifies `γ(s, x)` with
`Complex.partialGamma s x` for real `s`.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 2, the "Lower incomplete gamma"
  target.
* *NIST Digital Library of Mathematical Functions*, [ch. 8](https://dlmf.nist.gov/8),
  especially [§8.2](https://dlmf.nist.gov/8.2) for incomplete gamma functions and
  [Eq. 8.4.1](https://dlmf.nist.gov/8.4.E1) for their relation with the error function.
-/

public section

noncomputable section

open Filter MeasureTheory Set

open scoped Interval Topology

namespace TauCeti

variable {s x : ℝ}

/-! ### Convergence of the truncated Euler integral -/

/-- Euler's integrand `t ^ p * exp (-t)` is interval integrable, for `-1 < p`.

This composes Mathlib's `intervalIntegral.intervalIntegrable_rpow'`, which carries the singularity
at `0` for `p < 0`, with the continuous factor. The shape parameter `s` of
`TauCeti.lowerIncompleteGamma` enters as `p = s - 1`. -/
theorem intervalIntegrable_rpow_mul_exp_neg {p : ℝ} (hp : -1 < p) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => t ^ p * Real.exp (-t)) volume a b :=
  (intervalIntegral.intervalIntegrable_rpow' hp).mul_continuousOn
    (Real.continuous_exp.comp continuous_neg).continuousOn

/-! ### The definitions -/

/-- The lower incomplete gamma function `γ(s, x) = ∫ t in 0..x, t ^ (s - 1) * exp (-t)`.

It is `0` for `x ≤ 0`, where the truncated integral is empty, and `0` for `s ≤ 0`, where Euler's
integral diverges at the origin. -/
def lowerIncompleteGamma (s x : ℝ) : ℝ :=
  if 0 < s then ∫ t in (0 : ℝ)..max x 0, t ^ (s - 1) * Real.exp (-t) else 0

/-- The regularized lower incomplete gamma function `P(s, x) = γ(s, x) / Γ(s)`, extended by `0`
outside the valid range `0 < s` of the shape parameter. -/
def regularizedGamma (s x : ℝ) : ℝ :=
  if 0 < s then lowerIncompleteGamma s x / Real.Gamma s else 0

/-- In the valid range, `γ(s, x)` is the truncated Euler integral. -/
theorem lowerIncompleteGamma_eq_integral (hs : 0 < s) (hx : 0 ≤ x) :
    lowerIncompleteGamma s x = ∫ t in (0 : ℝ)..x, t ^ (s - 1) * Real.exp (-t) := by
  rw [lowerIncompleteGamma, ite_eq_left hs, max_eq_left hx]

/-- Outside the valid range of the shape parameter, `γ(s, x)` is `0`. -/
@[simp]
theorem lowerIncompleteGamma_eq_zero_of_nonpos_left (hs : s ≤ 0) (x : ℝ) :
    lowerIncompleteGamma s x = 0 :=
  ite_eq_right (not_lt.2 hs)

/-- Below the support, `γ(s, x)` is `0`. -/
@[simp]
theorem lowerIncompleteGamma_eq_zero_of_nonpos_right (s : ℝ) (hx : x ≤ 0) :
    lowerIncompleteGamma s x = 0 := by
  rw [lowerIncompleteGamma, max_eq_right hx]
  simp

/-- Outside the valid range of the shape parameter, `P(s, x)` is `0`. -/
@[simp]
theorem regularizedGamma_eq_zero_of_nonpos_left (hs : s ≤ 0) (x : ℝ) : regularizedGamma s x = 0 :=
  ite_eq_right (not_lt.2 hs)

/-- `P(s, x)` is `γ(s, x)` normalized by `Γ(s)`.

No hypothesis on the shape parameter is needed: for `s ≤ 0` both sides are `0`, since `γ(s, ·)`
is. -/
theorem regularizedGamma_eq_div (s x : ℝ) :
    regularizedGamma s x = lowerIncompleteGamma s x / Real.Gamma s := by
  rcases le_or_gt s 0 with hs | hs
  · rw [regularizedGamma_eq_zero_of_nonpos_left hs, lowerIncompleteGamma_eq_zero_of_nonpos_left hs,
      zero_div]
  · rw [regularizedGamma, ite_eq_left hs]

/-- Below the support, `P(s, x)` is `0`. -/
@[simp]
theorem regularizedGamma_eq_zero_of_nonpos_right (s : ℝ) (hx : x ≤ 0) :
    regularizedGamma s x = 0 := by
  rw [regularizedGamma_eq_div, lowerIncompleteGamma_eq_zero_of_nonpos_right s hx, zero_div]

/-- `γ(s, ·)` is the truncated Euler integral read at `max x 0`.

This is the form in which the global regularity statements below are proved: the clamping is a
continuous reparametrization, and the primitive itself is only well behaved on `[0, ∞)`. -/
private theorem lowerIncompleteGamma_eq_comp (hs : 0 < s) :
    lowerIncompleteGamma s =
      (fun y : ℝ => ∫ t in (0 : ℝ)..y, t ^ (s - 1) * Real.exp (-t)) ∘ fun x : ℝ => max x 0 := by
  funext y
  rw [Function.comp_apply, lowerIncompleteGamma, ite_eq_left hs]

/-! ### Positivity, monotonicity and regularity -/

/-- `γ(s, x)` is nonnegative, for every parameter value. -/
theorem lowerIncompleteGamma_nonneg (s x : ℝ) : 0 ≤ lowerIncompleteGamma s x := by
  rcases le_or_gt s 0 with hs | hs
  · rw [lowerIncompleteGamma_eq_zero_of_nonpos_left hs]
  rcases le_or_gt x 0 with hx | hx
  · rw [lowerIncompleteGamma_eq_zero_of_nonpos_right _ hx]
  · rw [lowerIncompleteGamma_eq_integral hs hx.le]
    exact intervalIntegral.integral_nonneg hx.le fun t ht =>
      mul_nonneg (Real.rpow_nonneg ht.1 _) (Real.exp_pos _).le

/-- `P(s, x)` is nonnegative, for every parameter value. -/
theorem regularizedGamma_nonneg (s x : ℝ) : 0 ≤ regularizedGamma s x := by
  rcases le_or_gt s 0 with hs | hs
  · rw [regularizedGamma_eq_zero_of_nonpos_left hs]
  · rw [regularizedGamma_eq_div]
    exact div_nonneg (lowerIncompleteGamma_nonneg s x) (Real.Gamma_nonneg_of_nonneg hs.le)

/-- `γ(s, ·)` is monotone: it accumulates a nonnegative integrand. -/
theorem lowerIncompleteGamma_monotone (s : ℝ) : Monotone (lowerIncompleteGamma s) := by
  rcases le_or_gt s 0 with hs | hs
  · rw [funext (lowerIncompleteGamma_eq_zero_of_nonpos_left hs)]
    exact monotone_const
  intro u v huv
  rcases le_or_gt v 0 with hv | hv
  · rw [lowerIncompleteGamma_eq_zero_of_nonpos_right _ (huv.trans hv),
      lowerIncompleteGamma_eq_zero_of_nonpos_right _ hv]
  rcases le_or_gt u 0 with hu | hu
  · rw [lowerIncompleteGamma_eq_zero_of_nonpos_right _ hu]
    exact lowerIncompleteGamma_nonneg _ _
  · rw [lowerIncompleteGamma_eq_integral hs hu.le, lowerIncompleteGamma_eq_integral hs hv.le]
    refine intervalIntegral.integral_mono_interval le_rfl hu.le huv ?_
      (intervalIntegrable_rpow_mul_exp_neg (by linarith : (-1 : ℝ) < s - 1) 0 v)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.exp_pos _).le

/-- `P(s, ·)` is monotone. For `0 < s`, this together with `TauCeti.regularizedGamma_nonneg`,
`TauCeti.regularizedGamma_le_one`, `TauCeti.regularizedGamma_eq_zero_of_nonpos_right`,
`TauCeti.continuous_regularizedGamma` and `TauCeti.tendsto_regularizedGamma_atTop` is everything a
cumulative distribution function must satisfy. -/
theorem regularizedGamma_monotone (s : ℝ) : Monotone (regularizedGamma s) := by
  rcases le_or_gt s 0 with hs | hs
  · rw [funext (regularizedGamma_eq_zero_of_nonpos_left hs)]
    exact monotone_const
  intro u v huv
  rw [regularizedGamma_eq_div, regularizedGamma_eq_div]
  gcongr
  exact lowerIncompleteGamma_monotone s huv

/-- `γ(s, ·)` is continuous on all of `ℝ`.

For `s < 1` this includes the point `x = 0`, where the integrand is unbounded; the integral is
nevertheless convergent there, by `TauCeti.intervalIntegrable_rpow_mul_exp_neg`. -/
@[fun_prop]
theorem continuous_lowerIncompleteGamma (s : ℝ) : Continuous (lowerIncompleteGamma s) := by
  rcases le_or_gt s 0 with hs | hs
  · rw [funext (lowerIncompleteGamma_eq_zero_of_nonpos_left hs)]
    exact continuous_const
  rw [lowerIncompleteGamma_eq_comp hs]
  exact (intervalIntegral.continuous_primitive
    (intervalIntegrable_rpow_mul_exp_neg (by linarith : (-1 : ℝ) < s - 1)) 0).comp
      (continuous_id.max continuous_const)

/-- `P(s, ·)` is continuous on all of `ℝ`. -/
@[fun_prop]
theorem continuous_regularizedGamma (s : ℝ) : Continuous (regularizedGamma s) := by
  rw [funext fun x => regularizedGamma_eq_div s x]
  exact (continuous_lowerIncompleteGamma s).div_const _

/-- `γ(s, ·)` is differentiable at every positive `x`, with the expected derivative.

The hypothesis `0 < x` cannot be weakened to `0 ≤ x`: among the positive shapes this theorem is
stated for, differentiability at `0` holds exactly for `1 < s`. For `s < 1` the integrand is
unbounded at `0`, and at `s = 1` the clamped function is `x ↦ 1 - exp (-max x 0)`, whose one-sided
derivatives at `0` are `0` and `1`. (For `s ≤ 0` the function is identically `0`, hence trivially
differentiable everywhere.) -/
theorem hasDerivAt_lowerIncompleteGamma (hs : 0 < s) (hx : 0 < x) :
    HasDerivAt (lowerIncompleteGamma s) (x ^ (s - 1) * Real.exp (-x)) x := by
  have hcont : ContinuousOn (fun t : ℝ => t ^ (s - 1) * Real.exp (-t)) (Ioi 0) := fun t ht =>
    ((Real.continuousAt_rpow_const t (s - 1) (Or.inl (ne_of_gt ht))).mul
      (Real.continuous_exp.comp continuous_neg).continuousAt).continuousWithinAt
  have hderiv : HasDerivAt (fun y : ℝ => ∫ t in (0 : ℝ)..y, t ^ (s - 1) * Real.exp (-t))
      (x ^ (s - 1) * Real.exp (-x)) x :=
    intervalIntegral.integral_hasDerivAt_right
      (intervalIntegrable_rpow_mul_exp_neg (by linarith : (-1 : ℝ) < s - 1) 0 x)
      (hcont.stronglyMeasurableAtFilter isOpen_Ioi x hx)
      ((Real.continuousAt_rpow_const x (s - 1) (Or.inl (ne_of_gt hx))).mul
        (Real.continuous_exp.comp continuous_neg).continuousAt)
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards [eventually_gt_nhds hx] with y hy
  rw [lowerIncompleteGamma_eq_integral hs hy.le]

/-- The derivative of `γ(s, ·)` at a positive point is the integrand. -/
theorem deriv_lowerIncompleteGamma (hs : 0 < s) (hx : 0 < x) :
    deriv (lowerIncompleteGamma s) x = x ^ (s - 1) * Real.exp (-x) :=
  (hasDerivAt_lowerIncompleteGamma hs hx).deriv

/-- `P(s, ·)` is differentiable at every positive `x`, with the expected derivative. As for
`TauCeti.hasDerivAt_lowerIncompleteGamma`, the hypothesis `0 < x` is needed at every shape
`0 < s ≤ 1`. -/
theorem hasDerivAt_regularizedGamma (hs : 0 < s) (hx : 0 < x) :
    HasDerivAt (regularizedGamma s) (x ^ (s - 1) * Real.exp (-x) / Real.Gamma s) x := by
  rw [funext fun y => regularizedGamma_eq_div s y]
  exact (hasDerivAt_lowerIncompleteGamma hs hx).div_const _

/-- The derivative of `P(s, ·)` at a positive point is the normalized integrand. -/
theorem deriv_regularizedGamma (hs : 0 < s) (hx : 0 < x) :
    deriv (regularizedGamma s) x = x ^ (s - 1) * Real.exp (-x) / Real.Gamma s :=
  (hasDerivAt_regularizedGamma hs hx).deriv

/-! ### The recurrence in the shape parameter -/

/-- For a positive real shape parameter `s` and `0 ≤ x`, `γ(s, x)` is Mathlib's
`Complex.partialGamma` at `(s : ℂ)`.

The complex partial gamma function carries the integration by parts behind
`TauCeti.lowerIncompleteGamma_add_one`, so this identification is what lets that recurrence be
imported rather than reproved. -/
theorem ofReal_lowerIncompleteGamma_eq_partialGamma (hs : 0 < s) (hx : 0 ≤ x) :
    ((lowerIncompleteGamma s x : ℝ) : ℂ) = Complex.partialGamma (s : ℂ) x := by
  rw [lowerIncompleteGamma_eq_integral hs hx, Complex.partialGamma,
    ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun t ht => ?_
  have ht0 : (0 : ℝ) ≤ t := (Set.uIcc_of_le hx ▸ ht : t ∈ Icc (0 : ℝ) x).1
  have hcast : ((t ^ (s - 1) : ℝ) : ℂ) = (t : ℂ) ^ ((s : ℂ) - 1) := by
    rw [Complex.ofReal_cpow ht0]
    push_cast
    ring_nf
  rw [Complex.ofReal_mul, hcast]
  ring

/-- The recurrence `γ(s + 1, x) = s * γ(s, x) - x ^ s * exp (-x)`, for `0 < s` and `0 ≤ x`. -/
theorem lowerIncompleteGamma_add_one (hs : 0 < s) (hx : 0 ≤ x) :
    lowerIncompleteGamma (s + 1) x = s * lowerIncompleteGamma s x - x ^ s * Real.exp (-x) := by
  have hs1 : (0 : ℝ) < s + 1 := by linarith
  have key := Complex.partialGamma_add_one (s := (s : ℂ)) (by simpa using hs) hx
  -- `Complex.partialGamma_add_one` shifts the shape inside `ℂ`, as `(s : ℂ) + 1`, whereas
  -- `TauCeti.ofReal_lowerIncompleteGamma_eq_partialGamma` only matches a shape of the form
  -- `((· : ℝ) : ℂ)`; so the cast is pulled outwards first, and likewise for the products, the
  -- difference and the power `(x : ℂ) ^ (s : ℂ)` on the right-hand side.
  have hshift : (s : ℂ) + 1 = ((s + 1 : ℝ) : ℂ) := by rw [Complex.ofReal_add, Complex.ofReal_one]
  rw [hshift,
    ← ofReal_lowerIncompleteGamma_eq_partialGamma hs1 hx,
    ← ofReal_lowerIncompleteGamma_eq_partialGamma hs hx, ← Complex.ofReal_cpow hx s,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.ofReal_inj] at key
  rw [key]
  ring

/-- The regularized form of the recurrence, `P(s + 1, x) = P(s, x) - x ^ s * exp (-x) / Γ(s + 1)`,
for `0 < s` and `0 ≤ x`. The factor `s` of `TauCeti.lowerIncompleteGamma_add_one` is absorbed by
`Real.Gamma_add_one`. -/
theorem regularizedGamma_add_one (hs : 0 < s) (hx : 0 ≤ x) :
    regularizedGamma (s + 1) x =
      regularizedGamma s x - x ^ s * Real.exp (-x) / Real.Gamma (s + 1) := by
  rw [regularizedGamma_eq_div, regularizedGamma_eq_div, lowerIncompleteGamma_add_one hs hx,
    Real.Gamma_add_one hs.ne', sub_div, mul_div_mul_left _ _ hs.ne']

/-! ### The limit at infinity -/

/-- `γ(s, x)` increases to the complete Euler integral `Real.Gamma s` as `x → ∞`. -/
theorem tendsto_lowerIncompleteGamma_atTop (hs : 0 < s) :
    Tendsto (lowerIncompleteGamma s) atTop (𝓝 (Real.Gamma s)) := by
  have hmax : Tendsto (fun x : ℝ => max x 0) atTop atTop :=
    tendsto_atTop_mono (fun x => le_max_left x 0) tendsto_id
  -- Mathlib's `Real.GammaIntegral_convergent` and `Real.Gamma_eq_integral` write Euler's integrand
  -- as `exp (-t) * t ^ (s - 1)`; both are used here in this file's factor order.
  have hint : IntegrableOn (fun t : ℝ => t ^ (s - 1) * Real.exp (-t)) (Ioi 0) :=
    (Real.GammaIntegral_convergent hs).congr_fun (fun t _ => mul_comm _ _) measurableSet_Ioi
  have hGamma : ∫ t in Ioi (0 : ℝ), t ^ (s - 1) * Real.exp (-t) = Real.Gamma s := by
    rw [Real.Gamma_eq_integral hs]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => mul_comm _ _
  rw [lowerIncompleteGamma_eq_comp hs, ← hGamma]
  exact (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id).comp hmax

/-- A truncated Euler integral is at most the complete one. -/
theorem lowerIncompleteGamma_le_Gamma (hs : 0 < s) (x : ℝ) :
    lowerIncompleteGamma s x ≤ Real.Gamma s :=
  (lowerIncompleteGamma_monotone s).ge_of_tendsto (tendsto_lowerIncompleteGamma_atTop hs) x

/-- `P(s, x)` increases to `1` as `x → ∞`: it is the cumulative distribution function of a
probability law. -/
theorem tendsto_regularizedGamma_atTop (hs : 0 < s) :
    Tendsto (regularizedGamma s) atTop (𝓝 1) := by
  rw [funext fun x => regularizedGamma_eq_div s x]
  have := (tendsto_lowerIncompleteGamma_atTop hs).div_const (Real.Gamma s)
  rwa [div_self (Real.Gamma_pos_of_pos hs).ne'] at this

/-- `P(s, x)` is at most `1`, for every parameter value. -/
theorem regularizedGamma_le_one (s x : ℝ) : regularizedGamma s x ≤ 1 := by
  rcases le_or_gt s 0 with hs | hs
  · rw [regularizedGamma_eq_zero_of_nonpos_left hs]
    exact zero_le_one
  · rw [regularizedGamma_eq_div]
    exact (div_le_one (Real.Gamma_pos_of_pos hs)).2 (lowerIncompleteGamma_le_Gamma hs x)

/-! ### The exponential case `s = 1` -/

/-- `γ(1, x) = 1 - exp (-x)` for `0 ≤ x`. -/
@[simp]
theorem lowerIncompleteGamma_one (hx : 0 ≤ x) :
    lowerIncompleteGamma 1 x = 1 - Real.exp (-x) := by
  rw [lowerIncompleteGamma_eq_integral one_pos hx]
  simp only [sub_self, Real.rpow_zero, one_mul]
  rw [intervalIntegral.integral_comp_neg fun t => Real.exp t, integral_exp]
  simp

/-- `P(1, x) = 1 - exp (-x)` for `0 ≤ x`: the regularized lower incomplete gamma function at shape
`1` is the cumulative distribution function of the standard exponential law. -/
@[simp]
theorem regularizedGamma_one (hx : 0 ≤ x) : regularizedGamma 1 x = 1 - Real.exp (-x) := by
  rw [regularizedGamma_eq_div, lowerIncompleteGamma_one hx, Real.Gamma_one, div_one]

/-! ### Relation with the error function -/

/-- On the positive half-line, the regularized incomplete gamma function of shape `1 / 2`,
composed with squaring, has the Gaussian derivative which defines the error function. -/
theorem hasDerivAt_regularizedGamma_half_sq {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => regularizedGamma (1 / 2) (y ^ 2))
      (2 / Real.sqrt Real.pi * Real.exp (-x ^ 2)) x := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hpow : (x ^ 2) ^ ((1 : ℝ) / 2 - 1) = x⁻¹ := by
    rw [← Real.rpow_two x, ← Real.rpow_mul hx.le]
    norm_num
    rw [Real.rpow_neg hx.le, Real.rpow_one]
  have hgamma : HasDerivAt (fun y : ℝ => regularizedGamma (1 / 2) (y ^ 2))
      (((x ^ 2) ^ ((1 : ℝ) / 2 - 1) * Real.exp (-x ^ 2) / Real.Gamma (1 / 2)) *
        (2 * x)) x := by
    have houter := hasDerivAt_regularizedGamma (s := (1 : ℝ) / 2) (x := x ^ 2)
      hhalf (sq_pos_of_pos hx)
    have hinner := hasDerivAt_pow 2 x
    simpa only [Function.comp_apply, Nat.reduceSub, pow_one] using!
      houter.comp_of_eq x hinner rfl
  convert hgamma using 1
  rw [hpow, Real.Gamma_one_half_eq]
  field_simp [hx.ne', Real.sqrt_ne_zero'.mpr Real.pi_pos]

/-- For `0 ≤ x`, the error function is the regularized lower incomplete gamma function of shape
`1 / 2` evaluated at `x²`. The restriction is necessary because the right-hand side is even,
whereas the error function is odd. -/
theorem Real.erf_eq_regularizedGamma_half_sq {x : ℝ} (hx : 0 ≤ x) :
    Real.erf x = regularizedGamma (1 / 2) (x ^ 2) := by
  let g : ℝ → ℝ := Real.erf - fun y => regularizedGamma (1 / 2) (y ^ 2)
  have hgdiff : DifferentiableOn ℝ g (Set.Ioi 0) := fun y hy =>
    ((Real.hasDerivAt_erf y).sub (hasDerivAt_regularizedGamma_half_sq hy)).differentiableAt
      |>.differentiableWithinAt
  have hgderiv : Set.EqOn (deriv g) 0 (Set.Ioi 0) := fun y hy => by
    simpa [g] using
      ((Real.hasDerivAt_erf y).sub (hasDerivAt_regularizedGamma_half_sq hy)).deriv
  obtain ⟨c, hc⟩ :=
    isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi hgdiff hgderiv
  have hgcont : Continuous g :=
    Real.continuous_erf.sub ((continuous_regularizedGamma _).comp (continuous_id.pow 2))
  have hlim : Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have hg0 : g 0 = 0 := by simp [g]
    have ht : Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (g 0)) :=
      hgcont.continuousAt.mono_left inf_le_left
    simpa only [hg0] using ht
  have heq : g =ᶠ[nhdsWithin 0 (Set.Ioi 0)] fun _ => c := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hc y hy
  have hc0 : c = 0 :=
    tendsto_nhds_unique (Tendsto.congr' heq.symm tendsto_const_nhds) hlim
  rcases hx.eq_or_lt with rfl | hx
  · simp
  · exact sub_eq_zero.mp (by simpa [g] using (hc x hx).trans hc0)

end TauCeti

end
