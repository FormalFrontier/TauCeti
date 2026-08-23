/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

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
  characteristic descriptions in the valid range, replacing the clamped definitions;
* `TauCeti.intervalIntegrable_rpow_mul_exp_neg` — convergence: the integrand is interval
  integrable on every interval in `[0, ∞)`, including at the singularity `0` for `s < 1`;
* `TauCeti.continuous_lowerIncompleteGamma`, `TauCeti.continuous_regularizedGamma` — continuity on
  all of `ℝ`, in particular at `x = 0`, where for `s < 1` the integrand blows up;
* `TauCeti.monotone_lowerIncompleteGamma`, `TauCeti.monotone_regularizedGamma` — monotonicity,
  and `TauCeti.lowerIncompleteGamma_nonneg`, `TauCeti.regularizedGamma_nonneg`,
  `TauCeti.regularizedGamma_le_one` — the range;
* `TauCeti.hasDerivAt_lowerIncompleteGamma`, `TauCeti.hasDerivAt_regularizedGamma` and the
  companion `deriv` lemmas — differentiability, for `0 < x` only;
* `TauCeti.lowerIncompleteGamma_add_one` — the recurrence
  `γ(s + 1, x) = s * γ(s, x) - x ^ s * exp (-x)`;
* `TauCeti.tendsto_lowerIncompleteGamma_atTop`, `TauCeti.tendsto_regularizedGamma_atTop` — the
  limits `Real.Gamma s` and `1` as `x → ∞`, with the resulting bounds
  `TauCeti.lowerIncompleteGamma_le_Gamma` and `TauCeti.regularizedGamma_le_one`;
* `TauCeti.regularizedGamma_one` — `P(1, x) = 1 - e ^ (-x)` for `0 ≤ x`, the exponential cdf.

## Implementation

`Real.Gamma` is *not* the value of Euler's integral outside `0 < s`, so the definition of
`regularizedGamma` guards on `0 < s` rather than dividing by `Real.Gamma s` unconditionally.

The recurrence is obtained from Mathlib's `Complex.partialGamma_add_one`, whose proof performs the
integration by parts on `Set.Ioo 0 x` — the endpoint `0` has to be avoided because `t ^ s` is not
differentiable there for `s < 1`. The bridge is `TauCeti.ofReal_lowerIncompleteGamma`, which
identifies `γ(s, x)` with `Complex.partialGamma s x` for real `s`.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 2, the "Lower incomplete gamma"
  target.
* *NIST Digital Library of Mathematical Functions*, [ch. 8](https://dlmf.nist.gov/8),
  especially [§8.2](https://dlmf.nist.gov/8.2).
-/

public section

noncomputable section

open Filter MeasureTheory Set

open scoped Interval Topology

namespace TauCeti

variable {s x : ℝ}

/-! ### Convergence of the truncated Euler integral -/

/-- Euler's integrand `t ^ p * exp (-t)` is interval integrable on any interval contained in
`[0, ∞)`, for `-1 < p`.

This is the interval form of Mathlib's `Real.GammaIntegral_convergent`; for `p < 0` the integrand
is unbounded at `0`, so the statement is not a mere continuity argument. The shape parameter `s` of
`TauCeti.lowerIncompleteGamma` enters as `p = s - 1`. -/
theorem intervalIntegrable_rpow_mul_exp_neg {p : ℝ} (hp : -1 < p) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    IntervalIntegrable (fun t : ℝ => t ^ p * Real.exp (-t)) volume a b := by
  have hsub : Ι a b ⊆ Ioi (0 : ℝ) := by
    intro t ht
    rw [Set.uIoc_eq_union] at ht
    rcases ht with ht | ht
    · exact lt_of_le_of_lt ha ht.1
    · exact lt_of_le_of_lt hb ht.1
  have h := Real.GammaIntegral_convergent (s := p + 1) (by linarith)
  rw [add_sub_cancel_right] at h
  rw [intervalIntegrable_iff]
  exact (h.mono_set hsub).congr_fun (fun t _ => mul_comm _ _) measurableSet_uIoc

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

/-- In the valid range of the shape parameter, `P(s, x)` is `γ(s, x)` normalized by `Γ(s)`. -/
theorem regularizedGamma_eq_div (hs : 0 < s) (x : ℝ) :
    regularizedGamma s x = lowerIncompleteGamma s x / Real.Gamma s := by
  rw [regularizedGamma, ite_eq_left hs]

/-- Outside the valid range of the shape parameter, `γ(s, x)` is `0`. -/
theorem lowerIncompleteGamma_of_nonpos_left (hs : s ≤ 0) (x : ℝ) :
    lowerIncompleteGamma s x = 0 :=
  ite_eq_right (not_lt.2 hs)

/-- Outside the valid range of the shape parameter, `P(s, x)` is `0`. -/
theorem regularizedGamma_of_nonpos_left (hs : s ≤ 0) (x : ℝ) : regularizedGamma s x = 0 :=
  ite_eq_right (not_lt.2 hs)

/-- Below the support, `γ(s, x)` is `0`. -/
theorem lowerIncompleteGamma_of_nonpos_right (s : ℝ) (hx : x ≤ 0) :
    lowerIncompleteGamma s x = 0 := by
  rw [lowerIncompleteGamma, max_eq_right hx]
  simp

/-- Below the support, `P(s, x)` is `0`. -/
theorem regularizedGamma_of_nonpos_right (s : ℝ) (hx : x ≤ 0) : regularizedGamma s x = 0 := by
  rw [regularizedGamma, lowerIncompleteGamma_of_nonpos_right s hx]
  simp

@[simp]
theorem lowerIncompleteGamma_zero_right (s : ℝ) : lowerIncompleteGamma s 0 = 0 :=
  lowerIncompleteGamma_of_nonpos_right s le_rfl

@[simp]
theorem regularizedGamma_zero_right (s : ℝ) : regularizedGamma s 0 = 0 :=
  regularizedGamma_of_nonpos_right s le_rfl

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
  rw [lowerIncompleteGamma]
  split
  · exact intervalIntegral.integral_nonneg (le_max_right x 0) fun t ht =>
      mul_nonneg (Real.rpow_nonneg ht.1 _) (Real.exp_pos _).le
  · exact le_rfl

/-- `P(s, x)` is nonnegative, for every parameter value. -/
theorem regularizedGamma_nonneg (s x : ℝ) : 0 ≤ regularizedGamma s x := by
  rw [regularizedGamma]
  split
  · exact div_nonneg (lowerIncompleteGamma_nonneg s x) (Real.Gamma_nonneg_of_nonneg (by linarith))
  · exact le_rfl

/-- `γ(s, ·)` is monotone: it accumulates a nonnegative integrand. -/
theorem monotone_lowerIncompleteGamma (s : ℝ) : Monotone (lowerIncompleteGamma s) := by
  rcases le_or_gt s 0 with hs | hs
  · rw [funext (lowerIncompleteGamma_of_nonpos_left hs)]
    exact monotone_const
  intro u v huv
  rcases le_or_gt v 0 with hv | hv
  · rw [lowerIncompleteGamma_of_nonpos_right _ (huv.trans hv),
      lowerIncompleteGamma_of_nonpos_right _ hv]
  rcases le_or_gt u 0 with hu | hu
  · rw [lowerIncompleteGamma_of_nonpos_right _ hu]
    exact lowerIncompleteGamma_nonneg _ _
  · rw [lowerIncompleteGamma_eq_integral hs hu.le, lowerIncompleteGamma_eq_integral hs hv.le,
      ← intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_rpow_mul_exp_neg (by linarith : (-1 : ℝ) < s - 1) le_rfl hu.le)
        (intervalIntegrable_rpow_mul_exp_neg (by linarith : (-1 : ℝ) < s - 1) hu.le hv.le)]
    refine le_add_of_nonneg_right (intervalIntegral.integral_nonneg huv fun t ht => ?_)
    exact mul_nonneg (Real.rpow_nonneg (hu.le.trans ht.1) _) (Real.exp_pos _).le

/-- `P(s, ·)` is monotone. Together with `TauCeti.regularizedGamma_nonneg`,
`TauCeti.regularizedGamma_le_one`, `TauCeti.continuous_regularizedGamma` and
`TauCeti.tendsto_regularizedGamma_atTop` this is everything a cumulative distribution function
must satisfy. -/
theorem monotone_regularizedGamma (s : ℝ) : Monotone (regularizedGamma s) := by
  rcases le_or_gt s 0 with hs | hs
  · rw [funext (regularizedGamma_of_nonpos_left hs)]
    exact monotone_const
  intro u v huv
  rw [regularizedGamma_eq_div hs, regularizedGamma_eq_div hs]
  gcongr
  exact monotone_lowerIncompleteGamma s huv

/-- The truncated Euler integral is continuous in its upper limit on `[0, ∞)`. -/
private theorem continuousOn_intervalIntegral_rpow_mul_exp_neg (hs : 0 < s) :
    ContinuousOn (fun y : ℝ => ∫ t in (0 : ℝ)..y, t ^ (s - 1) * Real.exp (-t)) (Ici 0) := by
  intro y hy
  have hy' : (0 : ℝ) ≤ y := hy
  have hmem : Icc (0 : ℝ) (y + 1) ∈ 𝓝[Ici (0 : ℝ)] y := by
    rw [← Set.Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
  refine ContinuousWithinAt.mono_of_mem_nhdsWithin ?_ hmem
  have huIcc : Set.uIcc (0 : ℝ) (y + 1) = Icc 0 (y + 1) := Set.uIcc_of_le (by linarith)
  have := intervalIntegral.continuousOn_primitive_interval' (a := (0 : ℝ)) (b₁ := (0 : ℝ))
    (b₂ := y + 1) (intervalIntegrable_rpow_mul_exp_neg (by linarith : (-1 : ℝ) < s - 1) le_rfl
      (by linarith))
    (by rw [huIcc]; exact ⟨le_rfl, by linarith⟩)
  rw [huIcc] at this
  exact this y ⟨hy', by linarith⟩

/-- `γ(s, ·)` is continuous on all of `ℝ`.

For `s < 1` this includes the point `x = 0`, where the integrand is unbounded; the integral is
nevertheless convergent there, by `TauCeti.intervalIntegrable_rpow_mul_exp_neg`. -/
theorem continuous_lowerIncompleteGamma (s : ℝ) : Continuous (lowerIncompleteGamma s) := by
  rcases le_or_gt s 0 with hs | hs
  · rw [funext (lowerIncompleteGamma_of_nonpos_left hs)]
    exact continuous_const
  rw [lowerIncompleteGamma_eq_comp hs]
  exact (continuousOn_intervalIntegral_rpow_mul_exp_neg hs).comp_continuous
    (continuous_id.max continuous_const) fun x => le_max_right x 0

/-- `P(s, ·)` is continuous on all of `ℝ`. -/
theorem continuous_regularizedGamma (s : ℝ) : Continuous (regularizedGamma s) := by
  rcases le_or_gt s 0 with hs | hs
  · rw [funext (regularizedGamma_of_nonpos_left hs)]
    exact continuous_const
  rw [funext fun x => regularizedGamma_eq_div hs x]
  exact (continuous_lowerIncompleteGamma s).div_const _

/-- `γ(s, ·)` is differentiable at every positive `x`, with the expected derivative.

Differentiability at `0` fails for `s < 1`, where the integrand is unbounded there, so the
hypothesis `0 < x` cannot be weakened to `0 ≤ x`. -/
theorem hasDerivAt_lowerIncompleteGamma (hs : 0 < s) (hx : 0 < x) :
    HasDerivAt (lowerIncompleteGamma s) (x ^ (s - 1) * Real.exp (-x)) x := by
  have hcont : ContinuousOn (fun t : ℝ => t ^ (s - 1) * Real.exp (-t)) (Ioi 0) := fun t ht =>
    ((Real.continuousAt_rpow_const t (s - 1) (Or.inl (ne_of_gt ht))).mul
      (Real.continuous_exp.comp continuous_neg).continuousAt).continuousWithinAt
  have hderiv : HasDerivAt (fun y : ℝ => ∫ t in (0 : ℝ)..y, t ^ (s - 1) * Real.exp (-t))
      (x ^ (s - 1) * Real.exp (-x)) x :=
    intervalIntegral.integral_hasDerivAt_right
      (intervalIntegrable_rpow_mul_exp_neg (by linarith : (-1 : ℝ) < s - 1) le_rfl hx.le)
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
`TauCeti.hasDerivAt_lowerIncompleteGamma`, the hypothesis `0 < x` is needed for `s < 1`. -/
theorem hasDerivAt_regularizedGamma (hs : 0 < s) (hx : 0 < x) :
    HasDerivAt (regularizedGamma s) (x ^ (s - 1) * Real.exp (-x) / Real.Gamma s) x := by
  rw [funext fun y => regularizedGamma_eq_div hs y]
  exact (hasDerivAt_lowerIncompleteGamma hs hx).div_const _

/-- The derivative of `P(s, ·)` at a positive point is the normalized integrand. -/
theorem deriv_regularizedGamma (hs : 0 < s) (hx : 0 < x) :
    deriv (regularizedGamma s) x = x ^ (s - 1) * Real.exp (-x) / Real.Gamma s :=
  (hasDerivAt_regularizedGamma hs hx).deriv

/-! ### The recurrence in the shape parameter -/

/-- For a real shape parameter, `γ(s, x)` is Mathlib's `Complex.partialGamma`.

The complex partial gamma function carries the integration by parts behind
`TauCeti.lowerIncompleteGamma_add_one`, so this identification is what lets that recurrence be
imported rather than reproved. -/
theorem ofReal_lowerIncompleteGamma (hs : 0 < s) (hx : 0 ≤ x) :
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

/-- The recurrence `γ(s + 1, x) = s * γ(s, x) - x ^ s * exp (-x)`. -/
theorem lowerIncompleteGamma_add_one (hs : 0 < s) (hx : 0 ≤ x) :
    lowerIncompleteGamma (s + 1) x = s * lowerIncompleteGamma s x - x ^ s * Real.exp (-x) := by
  have hs1 : (0 : ℝ) < s + 1 := by linarith
  have key := Complex.partialGamma_add_one (s := (s : ℂ)) (by simpa using hs) hx
  rw [show (s : ℂ) + 1 = ((s + 1 : ℝ) : ℂ) by push_cast; ring, ← ofReal_lowerIncompleteGamma hs1 hx,
    ← ofReal_lowerIncompleteGamma hs hx, ← Complex.ofReal_cpow hx s, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.ofReal_inj] at key
  rw [key]
  ring

/-! ### The limit at infinity -/

/-- `γ(s, x)` increases to the complete Euler integral `Real.Gamma s` as `x → ∞`. -/
theorem tendsto_lowerIncompleteGamma_atTop (hs : 0 < s) :
    Tendsto (lowerIncompleteGamma s) atTop (𝓝 (Real.Gamma s)) := by
  have hint : IntegrableOn (fun t : ℝ => t ^ (s - 1) * Real.exp (-t)) (Ioi 0) :=
    (Real.GammaIntegral_convergent hs).congr_fun (fun t _ => mul_comm _ _) measurableSet_Ioi
  have hGamma : ∫ t in Ioi (0 : ℝ), t ^ (s - 1) * Real.exp (-t) = Real.Gamma s := by
    rw [Real.Gamma_eq_integral hs]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => mul_comm _ _
  have hmax : Tendsto (fun x : ℝ => max x 0) atTop atTop :=
    tendsto_atTop_mono (fun x => le_max_left x 0) tendsto_id
  rw [lowerIncompleteGamma_eq_comp hs, ← hGamma]
  exact (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id).comp hmax

/-- A truncated Euler integral is at most the complete one. -/
theorem lowerIncompleteGamma_le_Gamma (hs : 0 < s) (x : ℝ) :
    lowerIncompleteGamma s x ≤ Real.Gamma s :=
  (monotone_lowerIncompleteGamma s).ge_of_tendsto (tendsto_lowerIncompleteGamma_atTop hs) x

/-- `P(s, x)` increases to `1` as `x → ∞`: it is the cumulative distribution function of a
probability law. -/
theorem tendsto_regularizedGamma_atTop (hs : 0 < s) :
    Tendsto (regularizedGamma s) atTop (𝓝 1) := by
  rw [funext fun x => regularizedGamma_eq_div hs x]
  have := (tendsto_lowerIncompleteGamma_atTop hs).div_const (Real.Gamma s)
  rwa [div_self (Real.Gamma_pos_of_pos hs).ne'] at this

/-- `P(s, x)` is at most `1`, for every parameter value. -/
theorem regularizedGamma_le_one (s x : ℝ) : regularizedGamma s x ≤ 1 := by
  rcases le_or_gt s 0 with hs | hs
  · rw [regularizedGamma_of_nonpos_left hs]
    exact zero_le_one
  · rw [regularizedGamma_eq_div hs]
    exact (div_le_one (Real.Gamma_pos_of_pos hs)).2 (lowerIncompleteGamma_le_Gamma hs x)

/-! ### The exponential case `s = 1` -/

/-- `γ(1, x) = 1 - exp (-x)` for `0 ≤ x`. -/
theorem lowerIncompleteGamma_one (hx : 0 ≤ x) :
    lowerIncompleteGamma 1 x = 1 - Real.exp (-x) := by
  rw [lowerIncompleteGamma_eq_integral one_pos hx]
  simp only [sub_self, Real.rpow_zero, one_mul]
  rw [intervalIntegral.integral_comp_neg fun t => Real.exp t, integral_exp]
  simp

/-- `P(1, x) = 1 - exp (-x)` for `0 ≤ x`: the regularized lower incomplete gamma function at shape
`1` is the cumulative distribution function of the standard exponential law. -/
theorem regularizedGamma_one (hx : 0 ≤ x) : regularizedGamma 1 x = 1 - Real.exp (-x) := by
  rw [regularizedGamma_eq_div one_pos, lowerIncompleteGamma_one hx, Real.Gamma_one, div_one]

end TauCeti

end
