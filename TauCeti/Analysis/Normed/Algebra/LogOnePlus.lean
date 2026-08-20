/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.OfScalars

/-!
# The logarithm of one plus an element of a Banach algebra

This file packages the power series
`log (1 + u) = ∑ n ≥ 1, (-1)^(n+1) / n • u^n` in a real Banach algebra. Its radius of
convergence is at least one, so it supplies the local logarithm needed to define the
Baker–Campbell–Hausdorff map near the origin.

## Main definitions and results

* `NormedSpace.logOnePlusSeries`: the formal multilinear series for `log (1 + u)`.
* `NormedSpace.logOnePlusSeries_apply`: its homogeneous terms.
* `NormedSpace.logOnePlus`: its sum.
* `NormedSpace.logOnePlus_eq_tsum`: the defining series equation.
* `NormedSpace.one_le_logOnePlusSeries_radius`: the radius of convergence is at least one.
* `NormedSpace.hasFPowerSeriesOnBall_logOnePlus`: the series represents `logOnePlus` on the
  unit ball.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 3, "Baker–Campbell–Hausdorff".
-/

public section

open Filter
open scoped ENNReal Topology

noncomputable section

namespace NormedSpace

variable (A : Type*) [NormedRing A] [NormedAlgebra ℝ A]

/-- The formal multilinear series for `log (1 + u)` in a real normed algebra. -/
def logOnePlusSeries : FormalMultilinearSeries ℝ A A :=
  FormalMultilinearSeries.ofScalars A fun n ↦ (-1 : ℝ) ^ (n + 1) / n

/-- The homogeneous terms of `logOnePlusSeries`. -/
@[simp]
theorem logOnePlusSeries_apply {n : ℕ} (v : Fin n → A) :
    logOnePlusSeries A n v =
      ((-1 : ℝ) ^ (n + 1) / n) • (List.ofFn v).prod := by
  simp [logOnePlusSeries, FormalMultilinearSeries.ofScalars]

/-- The `tsum` of the power series for `log (1 + u)`. -/
def logOnePlus (u : A) : A :=
  (logOnePlusSeries A).sum u

/-- The defining power-series equation for `logOnePlus`. -/
theorem logOnePlus_eq_tsum (u : A) :
    logOnePlus A u = ∑' n : ℕ, ((-1 : ℝ) ^ (n + 1) / n) • u ^ n := by
  exact FormalMultilinearSeries.ofScalars_sum_eq _ _

/-- The power series for `log (1 + u)` converges throughout the open unit ball. -/
theorem one_le_logOnePlusSeries_radius : 1 ≤ (logOnePlusSeries A).radius := by
  let c : ℕ → ℝ := fun n ↦ (-1 : ℝ) ^ (n + 1) / n
  have hc : Tendsto (fun n ↦ ‖c n.succ‖ / ‖c n‖) atTop (nhds 1) := by
    convert tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1 using 1
    funext n
    by_cases hn : n = 0
    · subst n
      norm_num [c]
    · have hsucc : ‖c n.succ‖ = (n + 1 : ℝ)⁻¹ := by
        simp only [c, norm_div, norm_pow, norm_neg, norm_one, one_pow, Nat.cast_add,
          Nat.cast_one, Nat.succ_eq_add_one]
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        simp only [one_div]
      have hnrm : ‖c n‖ = (n : ℝ)⁻¹ := by
        simp only [c, norm_div, norm_pow, norm_neg, norm_one, one_pow]
        rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
        simp only [one_div]
      rw [hsucc, hnrm]
      field_simp
  simpa [logOnePlusSeries, c] using
    (FormalMultilinearSeries.inv_le_ofScalars_radius_of_tendsto A c one_ne_zero hc)

variable [CompleteSpace A]

/-- The defining series for `logOnePlus` is summable in the open unit ball. -/
theorem summable_logOnePlus {u : A} (hu : ‖u‖ < 1) :
    Summable fun n : ℕ ↦ ((-1 : ℝ) ^ (n + 1) / n) • u ^ n := by
  rw [← FormalMultilinearSeries.ofScalars_apply_eq']
  apply (logOnePlusSeries A).summable
  have hed : edist u 0 < 1 := by
    simpa only [edist_dist, dist_zero_right, ENNReal.ofReal_lt_one] using hu
  exact hed.trans_le (one_le_logOnePlusSeries_radius A)

/-- `logOnePlusSeries` represents `logOnePlus` throughout the open unit ball. -/
theorem hasFPowerSeriesOnBall_logOnePlus :
    HasFPowerSeriesOnBall (logOnePlus A) (logOnePlusSeries A) 0 1 := by
  exact ((logOnePlusSeries A).hasFPowerSeriesOnBall
      (lt_of_lt_of_le zero_lt_one (one_le_logOnePlusSeries_radius A))).mono zero_lt_one
    (one_le_logOnePlusSeries_radius A)

/-- `logOnePlus` is analytic at the origin. -/
theorem analyticAt_logOnePlus : AnalyticAt ℝ (logOnePlus A) 0 :=
  hasFPowerSeriesOnBall_logOnePlus A |>.analyticAt

omit [CompleteSpace A] in
@[simp]
theorem logOnePlus_zero : logOnePlus A 0 = 0 := by
  -- Expose the scalar-series sum so its generic zero theorem applies directly.
  change FormalMultilinearSeries.ofScalarsSum (fun n : ℕ ↦ (-1 : ℝ) ^ (n + 1) / n) 0 = 0
  rw [FormalMultilinearSeries.ofScalarsSum_zero]
  norm_num

end NormedSpace
