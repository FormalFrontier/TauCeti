/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import TauCeti.Analysis.Contour.PiecewiseC1On
public import TauCeti.Analysis.Contour.Winding.Number.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import TauCeti.Analysis.Contour.Argument.Lift
import TauCeti.Analysis.Contour.Winding.SegmentSum

/-!
# The winding number of a point-avoiding arc exponentiates to its endpoint ratio

For a curve `γ` on the oriented interval with endpoints `a`, `b` that avoids `w`, the generalized
winding number `n_w(γ) = windingNumber γ a b w` is an ordinary index integral, and

`exp (2πi · n_w(γ)) = (γ b - w) / (γ a - w)`.

This one identity carries the whole polar bookkeeping of the index integral. Its modulus records
the imaginary part of the winding number,
`Im n_w(γ) = (log ‖γ a - w‖ - log ‖γ b - w‖) / 2π` — so the winding number of an *open* arc is
real exactly when its two endpoints are equidistant from `w`. Its argument records the real part
modulo `1`: `2π · Re n_w(γ) = arg (γ b - w) - arg (γ a - w)` in `Real.Angle`. Closing the curve
(`γ a = γ b`) makes the right-hand side `1`, which is the integrality of the winding number off
the curve (`exists_int_windingNumber_of_closed`, now a three-line corollary).

The identity is the mod-`1` bookkeeping that Hungerbühler–Wasem Proposition 2.2 telescopes. There
a closed piecewise-`C¹` immersion `Λ` is cut at the finitely many parameters where it meets `z₀`
(`IsPwC1ImmersionOn.finite_crossings`), and the real part of the winding number of each *avoiding*
piece is pinned modulo `1` by the directions of `Λ - z₀` at the two ends of that piece —
directions that
`tendsto_normalize_sub_nhdsGT` and `tendsto_normalize_sub_nhdsLT` identify with the outgoing and
reversed incoming tangents, that is with the summands of `crossingAngle`. Summing the pieces
around the closed curve is what turns the endpoint arguments into
`n_{z₀}(Λ) - Σ_ℓ crossingAngle Λ t_ℓ / 2π ∈ ℤ`.

## Main results

* `TauCeti.Contour.exp_two_pi_I_mul_windingNumber_of_avoidance` — the endpoint-ratio identity.
* `TauCeti.Contour.IsPiecewiseC1On.exp_two_pi_I_mul_windingNumber` — the same for a
  piecewise-`C¹` curve, whose regularity supplies the raw hypotheses on its own.
* `TauCeti.Contour.im_windingNumber_of_avoidance` and its piecewise-`C¹` form — the imaginary part
  of the winding number of an arc is the log-modulus decrement of its endpoints, over `2π`.
* `TauCeti.Contour.coe_two_pi_mul_re_windingNumber_eq_arg_sub_arg_of_avoidance` and its
  piecewise-`C¹` form — the real part of the winding number, read modulo `1` as a `Real.Angle`,
  is the argument change between the endpoint directions.

## Provenance

The argument-lift partition and the segment-sum evaluation of the index integral are the ones
already used for winding-number integrality; the private endpoint-sum lemmas below were factored
out of `Winding/Integer.lean`, whose closed-curve statement is now derived from the identity
proved here.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997, Definition 2.1 and Proposition 2.2.
-/

public section

open Complex MeasureTheory Set

open scoped Interval

namespace TauCeti.Contour

variable {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ} {P : Set ℝ}

/-- The lifted argument sum at the left endpoint `a` is `0`: every partition node satisfies
`a ≤ s j`, so each segment ratio at `a` is `1` and its logarithm's imaginary part is `0`. -/
private lemma sum_im_log_segRatio_left_eq_zero {N : ℕ} {s : ℕ → ℝ}
    (hs_zero : s 0 = a) (hs_mono : Monotone s) (hs_avoid : ∀ j < N, γ (s j) - w ≠ 0) :
    (∑ j ∈ Finset.range N, (Complex.log (segRatio γ w (s j) (s (j + 1)) a)).im) = 0 := by
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  have ha_le : a ≤ s j := by rw [← hs_zero]; exact hs_mono (Nat.zero_le j)
  rw [segRatio_eq_one_of_le ha_le (hs_avoid j hj), Complex.log_one, Complex.zero_im]

/-- At the right endpoint `b` the lifted argument sum equals the endpoint-ratio sum: every partition
segment lies to the left of `b`, so each segment ratio evaluated at `b` is the full endpoint ratio
`(γ (s (j + 1)) - w) / (γ (s j) - w)`. -/
private lemma sum_im_log_segRatio_right_eq_sum_im_log_endpoint_div {N : ℕ} {s : ℕ → ℝ}
    (hs_N : s N = b) (hs_mono : Monotone s) :
    (∑ j ∈ Finset.range N, (Complex.log (segRatio γ w (s j) (s (j + 1)) b)).im)
      = ∑ j ∈ Finset.range N, (Complex.log ((γ (s (j + 1)) - w) / (γ (s j) - w))).im := by
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  have hb_ge : s (j + 1) ≤ b := by rw [← hs_N]; exact hs_mono hj
  rw [segRatio_eq_endpoint_div_of_le (hs_mono (Nat.le_succ j)) hb_ge]

/-- The nonnegative-orientation (`a ≤ b`) case of
`exp_two_pi_I_mul_windingNumber_of_avoidance`. The general oriented-interval statement
reduces to this case by orientation reversal. -/
private theorem exp_two_pi_I_mul_windingNumber_of_le
    (hab : a ≤ b) (hP : P.Countable) (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b \ P, DifferentiableAt ℝ γ t)
    (h_avoid : ∀ t ∈ Icc a b, γ t ≠ w)
    (h_int : IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b w)
      = (γ b - w) / (γ a - w) := by
  -- The argument lift gives a monotone partition `s` and a polar form of `γ t - w` at each `t`.
  obtain ⟨N, s, -, hs_zero, hs_N, hs_mono, -, hs_avoid, h_slit, -, h_lift⟩ :=
    exists_continuousOn_arg_lift_with_partition hab hγ_cont h_avoid
  -- Split the index integral into a modulus increment plus `I` times the endpoint-ratio arg-sum.
  have hint := integral_inv_sub_mul_deriv_eq_log_norm_add_I_mul_sum_log_im hP hs_zero hs_N hs_mono
    hγ_cont hγ_diff h_slit h_int
  have hla := h_lift a (left_mem_Icc.mpr hab)
  have hlb := h_lift b (right_mem_Icc.mpr hab)
  rw [sum_im_log_segRatio_left_eq_zero hs_zero hs_mono (fun j hj ↦ hs_avoid j hj.le),
    add_zero] at hla
  rw [sum_im_log_segRatio_right_eq_sum_im_log_endpoint_div hs_N hs_mono] at hlb
  have hua : γ a - w ≠ 0 := sub_ne_zero.mpr (h_avoid a (left_mem_Icc.mpr hab))
  have hub : γ b - w ≠ 0 := sub_ne_zero.mpr (h_avoid b (right_mem_Icc.mpr hab))
  have hra_pos : 0 < ‖γ a - w‖ := norm_pos_iff.mpr hua
  have hrb_pos : 0 < ‖γ b - w‖ := norm_pos_iff.mpr hub
  set Se : ℝ := ∑ j ∈ Finset.range N,
    (Complex.log ((γ (s (j + 1)) - w) / (γ (s j) - w))).im
  set ra : ℝ := ‖γ a - w‖
  set rb : ℝ := ‖γ b - w‖
  set α : ℝ := Complex.arg (γ a - w)
  have hra_ne : (ra : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hra_pos.ne'
  -- The two polar forms differ exactly by the lifted argument increment `Se`.
  have hratio : (γ b - w) / (γ a - w)
      = ((rb : ℂ) / (ra : ℂ)) * Complex.exp (Complex.I * (Se : ℂ)) := by
    rw [hlb, hla, Complex.ofReal_add, mul_add, Complex.exp_add]
    field_simp
  have hcont_u : ContinuousOn γ (uIcc a b) := by rwa [uIcc_of_le hab]
  have havoid_u : ∀ t ∈ uIcc a b, γ t ≠ w := by rwa [uIcc_of_le hab]
  -- Normalizing away the `(2πi)⁻¹` turns the exponent back into the index integral.
  have hwind : 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b w
      = ∫ t in a..b, (γ t - w)⁻¹ * deriv γ t := by
    rw [windingNumber_eq_integral_of_avoidance hcont_u havoid_u h_int, ← mul_assoc,
      mul_inv_cancel₀ Complex.two_pi_I_ne_zero, one_mul]
  rw [hwind, hint, Complex.exp_add, hratio]
  congr 1
  rw [← Complex.ofReal_exp, Real.exp_sub, Real.exp_log hrb_pos, Real.exp_log hra_pos,
    Complex.ofReal_div]

/-- **The winding number of a point-avoiding arc exponentiates to its endpoint ratio.** For a curve
`γ` on the oriented interval with endpoints `a`, `b` that is continuous on `Set.uIcc a b`,
differentiable off a countable set `P`, avoids `w` throughout `Set.uIcc a b`, and has an
interval-integrable index integrand `(γ · - w)⁻¹ * deriv γ`,

`exp (2πi · windingNumber γ a b w) = (γ b - w) / (γ a - w)`.

Both the modulus and the argument of the winding number are read off this identity, by
`im_windingNumber_of_avoidance` and
`coe_two_pi_mul_re_windingNumber_eq_arg_sub_arg_of_avoidance`. -/
theorem exp_two_pi_I_mul_windingNumber_of_avoidance
    (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (h_avoid : ∀ t ∈ uIcc a b, γ t ≠ w)
    (h_int : IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b w)
      = (γ b - w) / (γ a - w) := by
  rcases le_total a b with hab | hba
  · rw [uIcc_of_le hab] at hγ_cont h_avoid
    rw [min_eq_left hab, max_eq_right hab] at hγ_diff
    exact exp_two_pi_I_mul_windingNumber_of_le hab hP hγ_cont hγ_diff h_avoid h_int
  · -- Reversed orientation: the winding number changes sign, and so does the endpoint ratio.
    have hcont_ba : ContinuousOn γ (Icc b a) := by rw [← uIcc_of_ge hba]; exact hγ_cont
    have havoid_ba : ∀ t ∈ Icc b a, γ t ≠ w := fun t ht ↦
      h_avoid t (by rw [uIcc_of_ge hba]; exact ht)
    rw [min_eq_right hba, max_eq_left hba] at hγ_diff
    have hcore := exp_two_pi_I_mul_windingNumber_of_le hba hP hcont_ba hγ_diff havoid_ba h_int.symm
    have hrev : windingNumber γ a b w = -windingNumber γ b a w := by
      rw [windingNumber_eq_integral_of_avoidance hγ_cont h_avoid h_int,
        windingNumber_eq_integral_of_avoidance (by rw [uIcc_comm]; exact hγ_cont)
          (fun t ht ↦ h_avoid t (by rw [uIcc_comm] at ht; exact ht)) h_int.symm,
        intervalIntegral.integral_symm a b]
      ring
    rw [hrev, mul_neg, Complex.exp_neg, hcore, inv_div]

/-- **Piecewise-`C¹` form of the endpoint-ratio identity.** Piecewise-`C¹` regularity supplies the
continuity, differentiability and integrability hypotheses of
`exp_two_pi_I_mul_windingNumber_of_avoidance`. -/
theorem IsPiecewiseC1On.exp_two_pi_I_mul_windingNumber (hγ : IsPiecewiseC1On γ a b)
    (h_avoid : ∀ t ∈ uIcc a b, γ t ≠ w) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b w)
      = (γ b - w) / (γ a - w) := by
  obtain ⟨Q, hQ, hγ_diff⟩ := hγ.exists_countable_differentiableAt
  exact exp_two_pi_I_mul_windingNumber_of_avoidance hQ hγ.continuousOn hγ_diff h_avoid
    (intervalIntegrable_inv_sub_mul_deriv hγ.continuousOn h_avoid hγ.intervalIntegrable_deriv)

/-- The exponent `2πi · n` of the endpoint-ratio identity has real part `-2π · Im n`. -/
private lemma re_two_pi_I_mul (z : ℂ) :
    (2 * (Real.pi : ℂ) * Complex.I * z).re = -(2 * Real.pi * z.im) := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- The exponent `2πi · n` of the endpoint-ratio identity has imaginary part `2π · Re n`. -/
private lemma im_two_pi_I_mul (z : ℂ) :
    (2 * (Real.pi : ℂ) * Complex.I * z).im = 2 * Real.pi * z.re := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- **The imaginary part of the winding number of an arc.** Under the hypotheses of
`exp_two_pi_I_mul_windingNumber_of_avoidance`, the modulus of the endpoint ratio gives

`Im (windingNumber γ a b w) = (log ‖γ a - w‖ - log ‖γ b - w‖) / 2π`.

So the winding number of an open arc is real precisely when its endpoints are equidistant from
`w`; a closed curve is the special case where they coincide. -/
theorem im_windingNumber_of_avoidance
    (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (h_avoid : ∀ t ∈ uIcc a b, γ t ≠ w)
    (h_int : IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b) :
    (windingNumber γ a b w).im
      = (Real.log ‖γ a - w‖ - Real.log ‖γ b - w‖) / (2 * Real.pi) := by
  have hua : γ a - w ≠ 0 := sub_ne_zero.mpr (h_avoid a left_mem_uIcc)
  have hub : γ b - w ≠ 0 := sub_ne_zero.mpr (h_avoid b right_mem_uIcc)
  have h := congrArg (‖·‖) (exp_two_pi_I_mul_windingNumber_of_avoidance hP hγ_cont hγ_diff
    h_avoid h_int)
  rw [Complex.norm_exp, re_two_pi_I_mul, norm_div] at h
  have hlog := congrArg Real.log h
  rw [Real.log_exp, Real.log_div (norm_ne_zero_iff.mpr hub) (norm_ne_zero_iff.mpr hua)] at hlog
  rw [eq_div_iff (by positivity : (2 : ℝ) * Real.pi ≠ 0)]
  linarith

/-- **Piecewise-`C¹` form of the imaginary-part formula.** -/
theorem IsPiecewiseC1On.im_windingNumber (hγ : IsPiecewiseC1On γ a b)
    (h_avoid : ∀ t ∈ uIcc a b, γ t ≠ w) :
    (windingNumber γ a b w).im
      = (Real.log ‖γ a - w‖ - Real.log ‖γ b - w‖) / (2 * Real.pi) := by
  obtain ⟨Q, hQ, hγ_diff⟩ := hγ.exists_countable_differentiableAt
  exact im_windingNumber_of_avoidance hQ hγ.continuousOn hγ_diff h_avoid
    (intervalIntegrable_inv_sub_mul_deriv hγ.continuousOn h_avoid hγ.intervalIntegrable_deriv)

/-- **The real part of the winding number of an arc, modulo `1`.** Under the hypotheses of
`exp_two_pi_I_mul_windingNumber_of_avoidance`, the argument of the endpoint ratio gives

`2π · Re (windingNumber γ a b w) = arg (γ b - w) - arg (γ a - w)` in `Real.Angle`,

so the real part of the winding number of an arc is determined modulo `1` by the directions of
`γ - w` at its two endpoints, while the endpoint norms determine its imaginary part. This is the
bookkeeping that telescopes around a closed curve cut at its crossings (Hungerbühler–Wasem
Proposition 2.2); the statement is an equality of `Real.Angle`s because `arg` is additive only
modulo `2π`. -/
theorem coe_two_pi_mul_re_windingNumber_eq_arg_sub_arg_of_avoidance
    (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (h_avoid : ∀ t ∈ uIcc a b, γ t ≠ w)
    (h_int : IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b) :
    ((2 * Real.pi * (windingNumber γ a b w).re : ℝ) : Real.Angle)
      = (Complex.arg (γ b - w) : Real.Angle) - (Complex.arg (γ a - w) : Real.Angle) := by
  have hua : γ a - w ≠ 0 := sub_ne_zero.mpr (h_avoid a left_mem_uIcc)
  have hub : γ b - w ≠ 0 := sub_ne_zero.mpr (h_avoid b right_mem_uIcc)
  have h := exp_two_pi_I_mul_windingNumber_of_avoidance hP hγ_cont hγ_diff h_avoid h_int
  calc ((2 * Real.pi * (windingNumber γ a b w).re : ℝ) : Real.Angle)
      = (((2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b w).im : ℝ) : Real.Angle) := by
        rw [im_two_pi_I_mul]
    _ = ((Complex.arg
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b w)) : ℝ) :
            Real.Angle) := by
        rw [Complex.arg_exp, Real.Angle.coe_toIocMod]
    _ = ((Complex.arg ((γ b - w) / (γ a - w)) : ℝ) : Real.Angle) := by rw [h]
    _ = (Complex.arg (γ b - w) : Real.Angle) - (Complex.arg (γ a - w) : Real.Angle) :=
        Complex.arg_div_coe_angle hub hua

/-- **Piecewise-`C¹` form of the modulo-`1` reading of the winding number.** -/
theorem IsPiecewiseC1On.coe_two_pi_mul_re_windingNumber (hγ : IsPiecewiseC1On γ a b)
    (h_avoid : ∀ t ∈ uIcc a b, γ t ≠ w) :
    ((2 * Real.pi * (windingNumber γ a b w).re : ℝ) : Real.Angle)
      = (Complex.arg (γ b - w) : Real.Angle) - (Complex.arg (γ a - w) : Real.Angle) := by
  obtain ⟨Q, hQ, hγ_diff⟩ := hγ.exists_countable_differentiableAt
  exact coe_two_pi_mul_re_windingNumber_eq_arg_sub_arg_of_avoidance hQ hγ.continuousOn hγ_diff
    h_avoid (intervalIntegrable_inv_sub_mul_deriv hγ.continuousOn h_avoid
      hγ.intervalIntegrable_deriv)

end TauCeti.Contour

end
