/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.CDF

/-!
# The cumulative distribution function of a natural-valued law

A probability measure `μ` on `ℕ` becomes a real law by pushing it forward along the cast
`ℕ → ℝ`. The resulting cumulative distribution function is determined by the cumulative masses of
`μ` itself: it vanishes below the origin, where the pushforward has no mass at all, and at a
nonnegative point `x` it is the mass `μ` gives to the initial segment below the natural floor of
`x`. Every discrete law on `ℕ` therefore reads its real cdf off its own cumulative masses.

## Main results

* `TauCeti.Probability.cdf_map_natCast` evaluates the cdf at a nonnegative point;
* `TauCeti.Probability.cdf_map_natCast_of_neg` evaluates it below the origin.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti

namespace Probability

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

/-- At a nonnegative point, the cdf of a natural-valued law cast to the reals is the cumulative
mass of the initial segment below the natural floor of that point. -/
theorem cdf_map_natCast {x : ℝ} (hx : 0 ≤ x) :
    cdf (μ.map (Nat.cast : ℕ → ℝ)) x = μ.real (Iic ⌊x⌋₊) := by
  have hpre : (Nat.cast : ℕ → ℝ) ⁻¹' Iic x = Iic ⌊x⌋₊ := by
    ext k
    simp only [mem_preimage, mem_Iic]
    exact (Nat.le_floor_iff hx).symm
  rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic, hpre]

/-- Below the origin, the cdf of a natural-valued law cast to the reals vanishes: the law is
carried by the natural numbers. -/
theorem cdf_map_natCast_of_neg {x : ℝ} (hx : x < 0) :
    cdf (μ.map (Nat.cast : ℕ → ℝ)) x = 0 := by
  have hpre : (Nat.cast : ℕ → ℝ) ⁻¹' Iic x = ∅ := by
    ext k
    simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
    exact lt_of_lt_of_le hx (Nat.cast_nonneg k)
  rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic, hpre,
    measureReal_empty]

end Probability

end TauCeti
