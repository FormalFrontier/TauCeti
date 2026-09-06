/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.NumberTheory.LSeries.Convergence

/-!
# Continuity of an L-series along a vertical line

If a Dirichlet series is summable at `s`, then at every point of the vertical line `s + ℝ * I`
its terms have exactly the same norms, so the series converges uniformly along that line and
`LSeries a` is continuous there.

Mathlib's `LSeries_differentiableOn` gives more, but only *strictly* inside the half-plane of
absolute convergence: it needs `abscissaOfAbsConv a < s.re`, whereas `LSeriesSummable a s` only
gives `abscissaOfAbsConv a ≤ s.re`. The line through a point of summability may therefore be the
boundary line of that half-plane, which is exactly the situation in the Wiener--Ikehara argument.

## Main results

* `TauCeti.LSeries.continuous_LSeries_vertical`: `fun t : ℝ ↦ LSeries a (s + t * I)` is continuous
  whenever `LSeriesSummable a s`.
-/

public section

namespace TauCeti.LSeries

open Complex

/-- A Dirichlet series summable at `s` is continuous along the vertical line through `s`. -/
theorem continuous_LSeries_vertical {a : ℕ → ℂ} {s : ℂ} (hs : LSeriesSummable a s) :
    Continuous fun t : ℝ ↦ LSeries a (s + t * I) := by
  have hterm n : Continuous fun t : ℝ ↦ _root_.LSeries.term a (s + t * I) n := by
    by_cases hn : n = 0
    · simpa [_root_.LSeries.term, hn] using continuous_const
    · simp only [_root_.LSeries.term, hn, ite_false]
      exact continuous_const.div₀ (continuous_const.cpow (by fun_prop) (by simp [hn]))
        (fun t ↦ by simp [hn])
  have hnorm n (t : ℝ) :
      ‖_root_.LSeries.term a (s + t * I) n‖ = ‖_root_.LSeries.term a s n‖ := by
    simp only [_root_.LSeries.norm_term_eq]
    simp
  exact continuous_tsum hterm (summable_norm_iff.mpr hs) (fun n t ↦ le_of_eq (hnorm n t))

end TauCeti.LSeries
