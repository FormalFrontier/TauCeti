/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.InvLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The logarithmic integral

This file defines the offset logarithmic integral `Li x = ∫ t in 2..x, (log t)⁻¹` and proves the
prime-number-theorem normalisation `Li x ~ x / log x` as `x → ∞`.

The lower endpoint is `2` rather than `0`: the integrand has a nonintegrable singularity at
`t = 1`, so the unshifted `li` exists only as a principal value, while every arithmetic
application compares a prime count with `Li`. The endpoint agrees with the one used by the
partial-summation identities for prime counts, so the two can be combined without a shift of
origin.

The asymptotic is proved from the exact identity
`Li x = x / log x - 2 / log 2 + ∫ t in 2..x, ((log t) ^ 2)⁻¹`,
the fundamental theorem of calculus applied to `t ↦ t / log t`, together with the estimate that
the remaining integral is `o (x / log x)`. Splitting that integral at `√x` bounds it by
`√x / (log 2) ^ 2 + 4 * x / (log x) ^ 2`, and both terms are `o (x / log x)`.

## Main declarations

* `TauCeti.Real.logIntegral` — the offset logarithmic integral.
* `TauCeti.Real.le_logIntegral` — the elementary lower bound `(x - 2) / log x ≤ Li x`.
* `TauCeti.Real.logIntegral_eq_div_log_sub_add` — the antiderivative identity above.
* `TauCeti.Real.logIntegral_isEquivalent_div_log` — `Li x ~ x / log x` at infinity, with the
  quotient form `TauCeti.Real.tendsto_logIntegral_mul_log_div_atTop`.

The auxiliary bounds `TauCeti.Real.integral_inv_log_pow_le` and
`TauCeti.Real.le_integral_inv_log_pow` estimate `∫ t in a..b, ((log t) ^ n)⁻¹` by monotonicity of
the logarithm. They are stated for a general exponent because the identity above needs `n = 2`
while `Li` itself is the case `n = 1`.

## Roadmap role

This is the analytic half of Layer **6.2** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`,
which asks for `Li` together with `Li(x) ∼ x/log x` on the way to the transfer
`ϑ(x) ∼ δx ⟹ π(x) ∼ δ Li(x)` that Layer 10.3 exports as `primeCount_asymptotic_of_primeTheta`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.
-/

public section

namespace TauCeti.Real

open Asymptotics Filter MeasureTheory Set
open scoped Topology

/-! ### Reciprocal powers of the logarithm -/

/-- Reciprocal powers of the logarithm are continuous to the right of its zero `t = 1`. -/
theorem continuousOn_inv_log_pow (n : ℕ) :
    ContinuousOn (fun t : ℝ ↦ (Real.log t ^ n)⁻¹) (Ioi 1) := by
  have hlog : ContinuousOn (fun t : ℝ ↦ Real.log t) (Ioi 1) :=
    Real.continuousOn_log.mono fun t ht ↦ ne_of_gt (lt_trans one_pos ht)
  exact (hlog.pow n).inv₀ fun t ht ↦ ne_of_gt (pow_pos (Real.log_pos ht) n)

/-- Reciprocal powers of the logarithm are interval integrable on any interval to the right
of `1`. -/
theorem intervalIntegrable_inv_log_pow (n : ℕ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t : ℝ ↦ (Real.log t ^ n)⁻¹) volume a b := by
  refine ((continuousOn_inv_log_pow n).mono fun t ht ↦ ?_).intervalIntegrable
  rw [mem_uIcc] at ht
  rcases ht with ht | ht
  · exact lt_of_lt_of_le ha ht.1
  · exact lt_of_lt_of_le hb ht.1

/-- Monotonicity of the logarithm bounds `∫ t in a..b, (log t ^ n)⁻¹` above by the value of the
integrand at the left endpoint. -/
theorem integral_inv_log_pow_le (n : ℕ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, (Real.log t ^ n)⁻¹ ≤ (b - a) / Real.log a ^ n := by
  have hla : 0 < Real.log a := Real.log_pos ha
  have hb : 1 < b := lt_of_lt_of_le ha hab
  have hmono := intervalIntegral.integral_mono_on hab (intervalIntegrable_inv_log_pow n ha hb)
    (g := fun _ ↦ (Real.log a ^ n)⁻¹) intervalIntegrable_const (fun t ht ↦ ?_)
  · simpa [smul_eq_mul, div_eq_mul_inv] using hmono
  · exact inv_anti₀ (pow_pos hla n)
      (pow_le_pow_left₀ hla.le (Real.log_le_log (by linarith) ht.1) n)

/-- Monotonicity of the logarithm bounds `∫ t in a..b, (log t ^ n)⁻¹` below by the value of the
integrand at the right endpoint. -/
theorem le_integral_inv_log_pow (n : ℕ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (b - a) / Real.log b ^ n ≤ ∫ t in a..b, (Real.log t ^ n)⁻¹ := by
  have hla : 0 < Real.log a := Real.log_pos ha
  have hb : 1 < b := lt_of_lt_of_le ha hab
  have hmono := intervalIntegral.integral_mono_on hab
    (f := fun _ ↦ (Real.log b ^ n)⁻¹) intervalIntegrable_const
    (intervalIntegrable_inv_log_pow n ha hb) (fun t ht ↦ ?_)
  · simpa [smul_eq_mul, div_eq_mul_inv] using hmono
  · have hat : a ≤ t := ht.1
    have htb : t ≤ b := ht.2
    have hlt : 0 < Real.log t := lt_of_lt_of_le hla (Real.log_le_log (by linarith) hat)
    exact inv_anti₀ (pow_pos hlt n)
      (pow_le_pow_left₀ hlt.le (Real.log_le_log (by linarith) htb) n)

/-- The integrand `(log t ^ n)⁻¹` is nonnegative to the right of `1`, so its integral is. -/
theorem integral_inv_log_pow_nonneg (n : ℕ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    0 ≤ ∫ t in a..b, (Real.log t ^ n)⁻¹ := by
  refine intervalIntegral.integral_nonneg hab fun t ht ↦ ?_
  have : 0 < Real.log t := Real.log_pos (lt_of_lt_of_le ha ht.1)
  positivity

/-! ### The logarithmic integral -/

/-- The **offset logarithmic integral** `Li x = ∫ t in 2..x, (log t)⁻¹`.

The lower endpoint `2` avoids the singularity of the integrand at `t = 1`; this is the function
appearing in the prime number theorem in the form `π x ~ Li x`. -/
noncomputable def logIntegral (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹

/-- Defining equation of `TauCeti.Real.logIntegral`. -/
theorem logIntegral_def (x : ℝ) : logIntegral x = ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹ := (rfl)

@[simp]
theorem logIntegral_two : logIntegral 2 = 0 := by
  rw [logIntegral_def, intervalIntegral.integral_same]

/-- The logarithmic integral is nonnegative from its base point on. -/
theorem logIntegral_nonneg {x : ℝ} (hx : 2 ≤ x) : 0 ≤ logIntegral x := by
  rw [logIntegral_def]
  simpa using integral_inv_log_pow_nonneg 1 one_lt_two hx

/-- The elementary lower bound `(x - 2) / log x ≤ Li x`, by monotonicity of the logarithm. -/
theorem le_logIntegral {x : ℝ} (hx : 2 ≤ x) : (x - 2) / Real.log x ≤ logIntegral x := by
  rw [logIntegral_def]
  simpa using le_integral_inv_log_pow 1 one_lt_two hx

/-! ### The asymptotic `Li x ~ x / log x` -/

/-- The derivative of `t ↦ t / log t` to the right of `1`. -/
theorem hasDerivAt_div_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun u : ℝ ↦ u / Real.log u) ((Real.log t)⁻¹ - (Real.log t ^ 2)⁻¹) t := by
  have ht₀ : t ≠ 0 := by positivity
  have hlt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have hd : HasDerivAt (fun u : ℝ ↦ u * (Real.log u)⁻¹)
      (1 * (Real.log t)⁻¹ + t * (-t⁻¹ / Real.log t ^ 2)) t :=
    (hasDerivAt_id t).mul (Real.hasDerivAt_inv_log ht₀ (ne_of_gt ht) (by linarith))
  have heq : 1 * (Real.log t)⁻¹ + t * (-t⁻¹ / Real.log t ^ 2)
      = (Real.log t)⁻¹ - (Real.log t ^ 2)⁻¹ := by
    field_simp
    ring
  rw [heq] at hd
  simpa only [div_eq_mul_inv] using hd

/-- **The antiderivative identity for the logarithmic integral.** Integrating the derivative of
`t ↦ t / log t` from `2` to `x` writes `Li x` as `x / log x` plus a constant and a remainder
integral, which the asymptotic below shows is `o (x / log x)`. -/
theorem logIntegral_eq_div_log_sub_add {x : ℝ} (hx : 2 ≤ x) :
    logIntegral x =
      x / Real.log x - 2 / Real.log 2 + ∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹ := by
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le one_lt_two hx
  have h1 : IntervalIntegrable (fun t : ℝ ↦ (Real.log t)⁻¹) volume 2 x := by
    simpa using intervalIntegrable_inv_log_pow 1 one_lt_two hx1
  have h2 : IntervalIntegrable (fun t : ℝ ↦ (Real.log t ^ 2)⁻¹) volume 2 x :=
    intervalIntegrable_inv_log_pow 2 one_lt_two hx1
  have hderiv : ∀ t ∈ uIcc (2 : ℝ) x, HasDerivAt (fun u : ℝ ↦ u / Real.log u)
      ((Real.log t)⁻¹ - (Real.log t ^ 2)⁻¹) t := by
    intro t ht
    rw [uIcc_of_le hx, mem_Icc] at ht
    exact hasDerivAt_div_log (by linarith [ht.1])
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (h1.sub h2)
  rw [intervalIntegral.integral_sub h1 h2] at hFTC
  rw [logIntegral_def]
  linarith [hFTC]

/-- Splitting at `√x` bounds the remainder integral of the antiderivative identity. -/
private theorem integral_inv_log_sq_le {x : ℝ} (hx : 4 ≤ x) :
    (∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹) ≤ √x / Real.log 2 ^ 2 + 4 * x / Real.log x ^ 2 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsq : 2 ≤ √x := by
    have h4 : √(4 : ℝ) ≤ √x := Real.sqrt_le_sqrt hx
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)] at h4
  have hle : √x ≤ x := by
    rw [Real.sqrt_le_self_iff]
    exact Or.inr (by linarith)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogsq : Real.log √x = Real.log x / 2 := Real.log_sqrt hx0.le
  have hsplit : (∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹) =
      (∫ t in (2 : ℝ)..√x, (Real.log t ^ 2)⁻¹) + ∫ t in √x..x, (Real.log t ^ 2)⁻¹ :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_inv_log_pow 2 one_lt_two (by linarith))
      (intervalIntegrable_inv_log_pow 2 (by linarith) (by linarith))).symm
  have hb₁ : (∫ t in (2 : ℝ)..√x, (Real.log t ^ 2)⁻¹) ≤ √x / Real.log 2 ^ 2 := by
    refine le_trans (integral_inv_log_pow_le 2 one_lt_two hsq) ?_
    have hpos : (0 : ℝ) < Real.log 2 ^ 2 := by positivity
    gcongr
    linarith
  have hb₂ : (∫ t in √x..x, (Real.log t ^ 2)⁻¹) ≤ 4 * x / Real.log x ^ 2 := by
    refine le_trans (integral_inv_log_pow_le 2 (by linarith) hle) ?_
    rw [hlogsq, div_pow, div_div_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
    nlinarith [Real.sqrt_nonneg x]
  rw [hsplit]
  linarith

/-- The remainder integral of the antiderivative identity is `o (x / log x)`. -/
theorem tendsto_integral_inv_log_sq_mul_log_div_atTop :
    Tendsto (fun x : ℝ ↦ (∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹) * Real.log x / x)
      atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun x : ℝ ↦ Real.log x / √x) atTop (𝓝 0) := by
    refine ((_root_.isLittleO_log_rpow_atTop (r := 1 / 2)
      (by norm_num)).tendsto_div_nhds_zero).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x _
    rw [Real.sqrt_eq_rpow]
  refine squeeze_zero' (g := fun x : ℝ ↦ Real.log x / √x * (Real.log 2 ^ 2)⁻¹ + 4 / Real.log x)
    ?_ ?_ ?_
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hnn := integral_inv_log_pow_nonneg 2 one_lt_two (by linarith : (2 : ℝ) ≤ x)
    positivity
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hsqpos : (0 : ℝ) < √x := Real.sqrt_pos.mpr hx0
    have hsqx : √x * √x = x := Real.mul_self_sqrt hx0.le
    have hbound := integral_inv_log_sq_le hx
    rw [div_le_iff₀ hx0]
    have hexp : (Real.log x / √x * (Real.log 2 ^ 2)⁻¹ + 4 / Real.log x) * x =
        (√x / Real.log 2 ^ 2 + 4 * x / Real.log x ^ 2) * Real.log x := by
      field_simp
      nlinarith [hsqx]
    rw [hexp]
    exact mul_le_mul_of_nonneg_right hbound hlogx.le
  · have h₁ : Tendsto (fun x : ℝ ↦ Real.log x / √x * (Real.log 2 ^ 2)⁻¹) atTop (𝓝 0) := by
      simpa using hsqrt.mul_const ((Real.log 2 ^ 2)⁻¹)
    have h₂ : Tendsto (fun x : ℝ ↦ (4 : ℝ) / Real.log x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    simpa using h₁.add h₂

/-- **The logarithmic integral is asymptotic to `x / log x`**, in quotient form. -/
theorem tendsto_logIntegral_mul_log_div_atTop :
    Tendsto (fun x : ℝ ↦ logIntegral x * Real.log x / x) atTop (𝓝 1) := by
  have hlog : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hmain : Tendsto (fun x : ℝ ↦ 1 - 2 / Real.log 2 * (Real.log x / x) +
      (∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹) * Real.log x / x) atTop (𝓝 1) := by
    have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h := (hone.sub (hlog.const_mul (2 / Real.log 2))).add
      tendsto_integral_inv_log_sq_mul_log_div_atTop
    simpa using h
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  rw [logIntegral_eq_div_log_sub_add hx]
  field_simp

/-- **`Li x` is asymptotically equivalent to `x / log x`.** -/
theorem logIntegral_isEquivalent_div_log :
    logIntegral ~[atTop] fun x : ℝ ↦ x / Real.log x := by
  refine (isEquivalent_iff_tendsto_one ?_).mpr ?_
  · filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    positivity
  · refine tendsto_logIntegral_mul_log_div_atTop.congr' ?_
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with x _
    rw [Pi.div_apply, div_div_eq_mul_div]

end TauCeti.Real
