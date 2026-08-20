/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.OfScalars

/-!
# The logarithm of one added to an element of a Banach algebra

This file packages the power series
`log (1 + u) = ∑ n ≥ 1, (-1)^(n+1) / n • u^n` in a Banach algebra over a
characteristic-zero normed field. Its radius of
convergence is at least one, so it supplies the local logarithm needed to define the
Baker–Campbell–Hausdorff map near the origin.

## Main definitions and results

* `NormedSpace.logOneAddSeries`: the formal multilinear series for `log (1 + u)`.
* `NormedSpace.logOneAddSeries_apply`: its homogeneous terms.
* `NormedSpace.logOneAdd`: its sum.
* `NormedSpace.logOneAdd_eq_tsum`: the defining series equation.
* `NormedSpace.one_le_logOneAddSeries_radius`: the radius of convergence is at least one.
* `NormedSpace.hasFPowerSeriesOnBall_logOneAdd`: the series represents `logOneAdd` on the
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

section Algebra

variable (𝕂 A : Type*) [Field 𝕂] [Ring A] [Algebra 𝕂 A]
variable [TopologicalSpace A] [IsTopologicalRing A]

/-- The formal multilinear series for `log (1 + u)` in a topological algebra. -/
def logOneAddSeries : FormalMultilinearSeries 𝕂 A A :=
  FormalMultilinearSeries.ofScalars A fun n ↦ (-1 : 𝕂) ^ (n + 1) / n

/-- The homogeneous terms of `logOneAddSeries`. -/
@[simp high]
theorem logOneAddSeries_apply {n : ℕ} (v : Fin n → A) :
    logOneAddSeries 𝕂 A n v =
      ((-1 : 𝕂) ^ (n + 1) / n) • (List.ofFn v).prod := by
  simp only [logOneAddSeries, FormalMultilinearSeries.ofScalars,
    smul_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply]

/-- The `tsum` of the power series for `log (1 + u)`. -/
def logOneAdd (u : A) : A :=
  (logOneAddSeries 𝕂 A).sum u

/-- The defining power-series equation for `logOneAdd`. -/
theorem logOneAdd_eq_tsum (u : A) :
    logOneAdd 𝕂 A u = ∑' n : ℕ, ((-1 : 𝕂) ^ (n + 1) / n) • u ^ n := by
  unfold logOneAdd logOneAddSeries
  exact FormalMultilinearSeries.ofScalars_sum_eq _ _

end Algebra

section Normed

variable (𝕂 A : Type*) [NontriviallyNormedField 𝕂]
variable [NormedRing A] [NormedAlgebra 𝕂 A]
variable [CharZero 𝕂] [ContinuousSMul ℚ≥0 𝕂]

/-- The radius of `logOneAddSeries` is at least one. -/
theorem one_le_logOneAddSeries_radius : 1 ≤ (logOneAddSeries 𝕂 A).radius := by
  let c : ℕ → 𝕂 := fun n ↦ (-1 : 𝕂) ^ (n + 1) / n
  have hratio : (fun n ↦ ‖c n.succ‖ / ‖c n‖) =
      fun n : ℕ ↦ ‖(n : 𝕂) / ((n + 1 : ℕ) : 𝕂)‖ := by
    funext n
    by_cases hn : n = 0
    · subst n
      simp [c]
    · simp only [c, norm_div, norm_pow, norm_neg, norm_one, one_pow,
        Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one]
      have hn𝕂 : (n : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hnorm : ‖(n : 𝕂)‖ ≠ 0 := norm_ne_zero_iff.mpr hn𝕂
      field_simp
  have hc : Tendsto (fun n ↦ ‖c n.succ‖ / ‖c n‖) atTop (nhds 1) := by
    rw [hratio]
    simpa only [Nat.cast_add, Nat.cast_one, norm_one] using
      (tendsto_natCast_div_add_atTop (𝕜 := 𝕂) 1).norm
  simpa [logOneAddSeries, c] using
    (FormalMultilinearSeries.inv_le_ofScalars_radius_of_tendsto A c one_ne_zero hc)

variable [CompleteSpace A]

/-- The defining series for `logOneAdd` is summable in the open unit ball. -/
theorem summable_logOneAdd {u : A} (hu : ‖u‖ < 1) :
    Summable fun n : ℕ ↦ ((-1 : 𝕂) ^ (n + 1) / n) • u ^ n := by
  rw [← FormalMultilinearSeries.ofScalars_apply_eq']
  have hed : edist u 0 < 1 := by
    simpa only [edist_dist, dist_zero_right, ENNReal.ofReal_lt_one] using hu
  simpa only [logOneAddSeries] using
    (logOneAddSeries 𝕂 A).summable
      (hed.trans_le (one_le_logOneAddSeries_radius 𝕂 A))

/-- `logOneAddSeries` represents `logOneAdd` throughout the open unit ball. -/
theorem hasFPowerSeriesOnBall_logOneAdd :
    HasFPowerSeriesOnBall (logOneAdd 𝕂 A) (logOneAddSeries 𝕂 A) 0 1 := by
  unfold logOneAdd
  exact ((logOneAddSeries 𝕂 A).hasFPowerSeriesOnBall
      (lt_of_lt_of_le zero_lt_one (one_le_logOneAddSeries_radius 𝕂 A))).mono zero_lt_one
    (one_le_logOneAddSeries_radius 𝕂 A)

/-- `logOneAdd` is analytic at the origin. -/
theorem analyticAt_logOneAdd : AnalyticAt 𝕂 (logOneAdd 𝕂 A) 0 :=
  hasFPowerSeriesOnBall_logOneAdd 𝕂 A |>.analyticAt

end Normed

section Algebra

variable (𝕂 A : Type*) [Field 𝕂] [Ring A] [Algebra 𝕂 A]
variable [TopologicalSpace A] [IsTopologicalRing A]

/-- `logOneAdd` vanishes at zero. -/
@[simp]
theorem logOneAdd_zero : logOneAdd 𝕂 A 0 = 0 := by
  unfold logOneAdd logOneAddSeries
  simpa only [FormalMultilinearSeries.ofScalarsSum, zero_add, pow_one, Nat.cast_zero,
    div_zero, zero_smul] using
    (FormalMultilinearSeries.ofScalarsSum_zero
      (E := A) (c := fun n : ℕ ↦ (-1 : 𝕂) ^ (n + 1) / n))

end Algebra

end NormedSpace
