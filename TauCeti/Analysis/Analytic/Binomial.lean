/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.AbelLimit

/-!
# Convergence of multichoose power series

This file determines the exact unconditional summability domain of the power series with
generalized multichoose coefficients and positive real parameter.  The result applies to both real
and complex arguments.  These results supply the analytic criterion used to determine the exact
integrability domain of the negative-binomial probability-generating function.

## Main declarations

* `TauCeti.hasSum_multichoose_mul_geometric_of_abs_lt_one` — the multichoose binomial
  series on the open unit interval.
* `TauCeti.summable_multichoose_mul_geometric_iff_norm_lt_one` — exact summability of
  `∑ n, multichoose r n * q ^ n` for `0 < r`.
-/

public section

open Filter Set
open scoped ENNReal

namespace TauCeti

/-- The generalized multichoose power series sums to `(1 - x)⁻ʳ` when `|x| < 1`. -/
theorem hasSum_multichoose_mul_geometric_of_abs_lt_one {r x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => Ring.multichoose r n * x ^ n) (1 / (1 - x) ^ r) := by
  have hmem : x ∈ Metric.eball (0 : ℝ) (1 : ℝ≥0∞) := by
    rw [Metric.mem_eball]
    simpa [edist_dist, Real.dist_0_eq_abs, enorm_eq_nnnorm] using hx
  have hsum := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero r).hasSum_sub hmem
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, sub_zero, smul_eq_mul] at hsum
  have hchoose (n : ℕ) :
      Ring.choose (r + (n : ℝ) - 1) n = Ring.multichoose r n := by
    rw [Ring.multichoose_eq]
  simpa only [hchoose] using hsum

/-- For positive real `r`, the generalized multichoose power series is unconditionally summable
at a real or complex argument `q` exactly when `q` lies in the open unit ball. -/
@[simp]
theorem summable_multichoose_mul_geometric_iff_norm_lt_one
    {𝕂 : Type*} [RCLike 𝕂] {r : ℝ} {q : 𝕂} (hr : 0 < r) :
    Summable (fun n : ℕ => ((Ring.multichoose r n : ℝ) : 𝕂) * q ^ n) ↔ ‖q‖ < 1 := by
  have hcoeff_pos (n : ℕ) : 0 < Ring.multichoose r n := by
    have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer r n
    rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at h
    apply pos_of_mul_pos_right (by rw [h]; exact ascPochhammer_pos n r hr)
    positivity
  have hnot : ¬ Summable (fun n : ℕ => Ring.multichoose r n) := by
    intro hs
    have habel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hs.hasSum.tendsto_sum_nat
    have hsub : Tendsto (fun x : ℝ => 1 - x) (nhdsWithin 1 (Iio 1))
        (nhdsWithin 0 (Ioi 0)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) (nhds 1) (nhds 1) :=
          tendsto_const_nhds
        have hi : Tendsto (fun x : ℝ => x) (nhds 1) (nhds 1) := tendsto_id
        have hmono : nhdsWithin (1 : ℝ) (Iio 1) ≤ nhds 1 := inf_le_left
        simpa only [sub_self] using (hc.sub hi).mono_left hmono
      · filter_upwards [self_mem_nhdsWithin] with x hx
        exact sub_pos.mpr (by simpa only [mem_Iio] using hx)
    have htop : Tendsto (fun x : ℝ => 1 / (1 - x) ^ r)
        (nhdsWithin 1 (Iio 1)) atTop := by
      refine ((tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.mpr hr)).comp hsub).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : x < 1 := by simpa only [mem_Iio] using hx
      simpa only [Function.comp_apply, one_div] using
        Real.rpow_neg (sub_nonneg.mpr hx'.le) r
    have heq : ∀ᶠ x : ℝ in nhdsWithin 1 (Iio 1),
        (∑' n : ℕ, Ring.multichoose r n * x ^ n) = 1 / (1 - x) ^ r := by
      filter_upwards [Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)] with x hx
      exact (hasSum_multichoose_mul_geometric_of_abs_lt_one
        (r := r) (by simpa [abs_lt] using hx)).tsum_eq
    have heq' : Filter.EventuallyEq (nhdsWithin 1 (Iio 1))
        (fun x : ℝ => 1 / (1 - x) ^ r)
        (fun x => ∑' n : ℕ, Ring.multichoose r n * x ^ n) := by
      filter_upwards [heq] with x hx
      exact hx.symm
    exact not_tendsto_atTop_of_tendsto_nhds habel (htop.congr' heq')
  rw [← summable_norm_iff]
  simp_rw [norm_mul, norm_pow, RCLike.norm_ofReal, abs_of_pos (hcoeff_pos _)]
  constructor
  · intro hs
    by_contra hq
    apply hnot
    exact hs.of_nonneg_of_le (fun n => (hcoeff_pos n).le) fun n => by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (one_le_pow₀ (le_of_not_gt hq)) (hcoeff_pos n).le
  · intro hq
    exact (hasSum_multichoose_mul_geometric_of_abs_lt_one
      (r := r) (by simpa only [abs_norm] using hq)).summable

end TauCeti

end
