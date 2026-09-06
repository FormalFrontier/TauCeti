/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.Topology.Algebra.Order.Field

/-!
# The divergence of `log (1 / (s - 1))` as `s` decreases to `1`

Analytic limit facts about `s ↦ log (1 / (s - 1))` on a right neighbourhood of `1`. The
function diverges to `+∞` there, and consequently any `f` that agrees with it up to a bounded
additive error has `f s / log (1 / (s - 1))` tending to `1`.

This is the shape in which Dirichlet density arguments are stated. A prime sum is estimated as
`log (1 / (s - 1)) + O(1)`, and the density is read off as the limit of the ratio of the sum to
`log (1 / (s - 1))`: the divergence of the denominator is exactly what makes the `O(1)` error
immaterial. Nothing here is specific to that application, and the file contains no number
theory.

## Main results

* `TauCeti.tendsto_log_one_div_sub_one_atTop` — `log (1 / (s - 1))` tends to `atTop` along
  `𝓝[>] 1`.
* `TauCeti.tendsto_div_log_nhds_one_of_le_add_const_of_sub_const_le` — if `f` agrees with
  `log (1 / (s - 1))` up to a
  two-sided additive bounded error near `1` from the right, then `f s / log (1 / (s - 1))` tends
  to `1`.

## Implementation notes

The quotient statement is the `g = log (1 / (s - 1))` case of
`TauCeti.tendsto_div_nhds_one_of_le_add_const_of_sub_const_le`. It is stated separately so that
the divergence hypothesis is discharged once and for all, leaving callers to supply only the two
error bounds they actually estimate.

## References

Adapted from `tendsto_log_one_div_sub_one_atTop` and `tendsto_ratio_one_of_log_pm_bounded` in
`CebotarevDensity/ForMathlib/LogOneDivSubOne.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`.
-/

public section

namespace TauCeti

open Filter Topology

/-- `log (1 / (s - 1))` tends to `+∞` as `s` decreases to `1`: the divergence driving the
Dirichlet density asymptotics. -/
theorem tendsto_log_one_div_sub_one_atTop :
    Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ)) atTop := by
  refine Real.tendsto_log_atTop.comp ?_
  have h1 : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((continuous_sub_right 1).tendsto' 1 0 (by ring)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun s hs ↦ by
        simp only [Set.mem_Ioi] at hs ⊢
        linarith)
  simpa only [one_div, Pi.inv_def] using h1.inv_tendsto_nhdsGT_zero

/-- If `f` agrees with `log (1 / (s - 1))` up to a two-sided additive bounded error on a right
neighbourhood of `1`, then `f s / log (1 / (s - 1))` tends to `1`. The analytic content is only
that `log (1 / (s - 1))` diverges, so the additive error washes out under division; the log-free
statement is `TauCeti.tendsto_div_nhds_one_of_le_add_const_of_sub_const_le`. -/
theorem tendsto_div_log_nhds_one_of_le_add_const_of_sub_const_le (f : ℝ → ℝ)
    (h_le : ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), f s ≤ Real.log (1 / (s - 1)) + C)
    (h_lower : ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), Real.log (1 / (s - 1)) - C ≤ f s) :
    Tendsto (fun s : ℝ ↦ f s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 1) :=
  tendsto_div_nhds_one_of_le_add_const_of_sub_const_le tendsto_log_one_div_sub_one_atTop h_le
    h_lower

end TauCeti
