/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Analysis.Contour.Argument.Divisor
import Mathlib.Analysis.Normed.Module.Convex

/-!
# The zero count of a holomorphic function on a disc

The zero count of `f` on an open disc is the finitely supported sum
`∑ᶠ z ∈ ball c R, analyticOrderNatAt f z`. It is what the argument principle produces — through
`TauCeti.Contour.argumentPrinciple_divisor` and the bridge
`TauCeti.Contour.divisor_eq_analyticOrderNatAt` — and what Rouché's theorem
(`TauCeti.rouche_symm`) and Hurwitz's theorem (`TauCeti.hurwitz`) compare. This file collects the
three facts about that sum which those consumers need, none of which mentions either theorem.

Care is needed about points of *infinite* order, where `f` vanishes identically nearby:
`analyticOrderNatAt` reads `0` there, exactly as it does where `f` does not vanish at all, so the
count does not see such a point. That is why detecting a zero from a vanishing count
(`TauCeti.finsum_analyticOrderNatAt_ball_eq_zero_iff`) needs a hypothesis ruling infinite order
out. One point of the closed disc at which `f` is nonzero is enough: the disc is convex, hence
preconnected, so `AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected` propagates the finite
order there to every point.

## Main results

* `TauCeti.analyticOrderNatAt_le_finsum_ball` — the order of vanishing at a single point of the
  open disc is at most the total count.
* `TauCeti.finsum_analyticOrderNatAt_ball_eq_zero_of_forall_ne_zero` — a zero-free function has
  count `0`.
* `TauCeti.finsum_analyticOrderNatAt_ball_eq_zero_iff` — conversely, given a point of the closed
  disc where `f` does not vanish, a count of `0` means there is no zero in the open disc at all.
-/

public section

open Complex Metric

namespace TauCeti

variable {f : ℂ → ℂ} {c : ℂ} {R : ℝ}

/-- The order of vanishing at a single point of the open disc is at most the total zero count.
Both sides read `0` at a point of infinite order, so the bound is trivially true there too.

The finiteness the sum needs is `MeromorphicOn.divisor_ball_support_finite`, transported along
`TauCeti.Contour.divisor_eq_analyticOrderNatAt`. -/
theorem analyticOrderNatAt_le_finsum_ball (hf : AnalyticOnNhd ℂ f (closedBall c R))
    {z₀ : ℂ} (hz₀ : z₀ ∈ ball c R) :
    analyticOrderNatAt f z₀ ≤ ∑ᶠ z ∈ ball c R, analyticOrderNatAt f z := by
  classical
  have hfin : (Function.support
      fun z => ∑ᶠ (_ : z ∈ ball c R), analyticOrderNatAt f z).Finite := by
    refine Set.Finite.subset (MeromorphicOn.divisor_ball_support_finite hf.meromorphicOn)
      (fun z hz => ?_)
    simp only [Function.mem_support, ne_eq] at hz
    by_cases hzb : z ∈ ball c R
    · simp only [hzb, finsum_true] at hz
      simp only [Function.mem_support, ne_eq,
        Contour.divisor_eq_analyticOrderNatAt (hf.mono ball_subset_closedBall).meromorphicOn
          (hf _ (ball_subset_closedBall hzb)) hzb]
      exact_mod_cast hz
    · exact absurd (by simp [hzb]) hz
  simpa [hz₀] using single_le_finsum z₀ hfin (fun _ => Nat.zero_le _)

/-- A function holomorphic and zero-free on the open disc has zero count `0` there. -/
theorem finsum_analyticOrderNatAt_ball_eq_zero_of_forall_ne_zero
    (hf : AnalyticOnNhd ℂ f (ball c R)) (hne : ∀ z ∈ ball c R, f z ≠ 0) :
    (∑ᶠ z ∈ ball c R, analyticOrderNatAt f z) = 0 :=
  finsum_mem_of_eqOn_zero fun z hz => by
    simp [analyticOrderNatAt, (hf z hz).analyticOrderAt_eq_zero.2 (hne z hz)]

/-- **The zero count detects zeros.** For `f` holomorphic on `closedBall c R` and nonvanishing at
*some* point of that closed disc, the count `∑ᶠ z ∈ ball c R, analyticOrderNatAt f z` vanishes
precisely when `f` has no zero in the open disc.

The nontrivial direction is that a zero contributes a *nonzero* order. That fails without a
hypothesis of this kind: `analyticOrderNatAt` sends a point of infinite order to `0`, so the
identically zero function has count `0` while vanishing everywhere. A single point of
nonvanishing rules that out, the closed disc being preconnected. -/
theorem finsum_analyticOrderNatAt_ball_eq_zero_iff (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hne : ∃ z ∈ closedBall c R, f z ≠ 0) :
    (∑ᶠ z ∈ ball c R, analyticOrderNatAt f z) = 0 ↔ ∀ z ∈ ball c R, f z ≠ 0 := by
  refine ⟨fun hsum z₀ hz₀ h0 => ?_, fun h =>
    finsum_analyticOrderNatAt_ball_eq_zero_of_forall_ne_zero (hf.mono ball_subset_closedBall) h⟩
  obtain ⟨w, hw, hwne⟩ := hne
  have h1 : analyticOrderAt f z₀ ≠ 0 :=
    (hf z₀ (ball_subset_closedBall hz₀)).analyticOrderAt_ne_zero.2 h0
  have h2 : analyticOrderAt f z₀ ≠ ⊤ :=
    hf.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall c R).isPreconnected hw
      (ball_subset_closedBall hz₀) (by simp [(hf w hw).analyticOrderAt_eq_zero.2 hwne])
  have hnz : analyticOrderNatAt f z₀ ≠ 0 := by
    simp [analyticOrderNatAt, ENat.toNat_eq_zero, h1, h2]
  have hle := analyticOrderNatAt_le_finsum_ball hf hz₀
  rw [hsum] at hle
  exact hnz (Nat.le_zero.1 hle)

end TauCeti
