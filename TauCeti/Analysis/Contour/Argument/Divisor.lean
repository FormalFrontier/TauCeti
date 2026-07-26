/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor
public import TauCeti.Analysis.Contour.Argument.Principle

/-!
# The argument principle against the divisor

`TauCeti.Contour.argumentPrinciple` asks its caller for the data of the counting problem: a finite
set `S` collecting the nonzero-order points, an order function `ord`, and proofs that the two agree
and that `S` is exhaustive. Mathlib's `MeromorphicOn.divisor` already packages exactly that data —
`MeromorphicOn.divisor_apply` evaluates it to `(meromorphicOrderAt f z).untop₀`, and
`MeromorphicOn.divisor_ball_support_finite` supplies the finiteness from the same
`MeromorphicOn f (closedBall c R)` hypothesis the argument principle already assumes. This file
restates the argument principle against that API, so callers that already speak `divisor` need not
rebuild the finset and the order function by hand.

The only hypothesis this adds is `hsphere`: the bounding circle carries no zeros or poles. It does
double duty.

* It confines the nonzero-order points to the *open* disc, so a divisor taken over `ball c R` still
  accounts for every such point of `closedBall c R`.
* It rules out order `⊤`. This matters because `(⊤ : WithTop ℤ).untop₀ = 0`, so at a point where `f`
  vanishes identically the divisor reads `0` while the order does not, and the exhaustiveness
  obligation of `argumentPrinciple` would fail exactly there. No separate hypothesis is needed:
  `closedBall c R` is convex, hence preconnected, and the sphere is nonempty as `0 < R`, so
  `MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected` propagates the finite order at a
  boundary point to the whole disc.

## Main results

* `TauCeti.Contour.argumentPrinciple_divisor` —
  `∮_{C(c,R)} logDeriv f = 2πi · ∑ᶠ z, divisor f (ball c R) z`, the argument principle with the
  counting data taken from `MeromorphicOn.divisor`. The conclusion uses the canonical finitely
  supported sum `∑ᶠ`, which is well defined because the divisor vanishes off `ball c R`; the
  finiteness witness `MeromorphicOn.divisor_ball_support_finite` stays inside the proof rather than
  appearing in the statement.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

open Filter Topology Metric Complex
open scoped Real

namespace TauCeti.Contour

/-- **The argument principle, against the divisor.** For `f` meromorphic on the closed disc
`C(c, R)` with no zero or pole on the bounding circle, the contour integral of the logarithmic
derivative is `2πi` times the sum of `MeromorphicOn.divisor` over the open disc.

This is `TauCeti.Contour.argumentPrinciple` with the finite set and the order function supplied by
Mathlib's divisor API rather than by the caller. -/
theorem argumentPrinciple_divisor {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : MeromorphicOn f (closedBall c R))
    (hsphere : ∀ z ∈ sphere c R, meromorphicOrderAt f z = 0) :
    circleIntegral (logDeriv f) c R
      = 2 * (Real.pi : ℂ) * Complex.I *
        (∑ᶠ z, ((MeromorphicOn.divisor f (ball c R) z : ℤ) : ℂ)) := by
  have hfb : MeromorphicOn f (ball c R) := fun x hx => hf x (ball_subset_closedBall hx)
  have hsupp : Function.support (fun z => ((MeromorphicOn.divisor f (ball c R) z : ℤ) : ℂ))
      ⊆ ((MeromorphicOn.divisor_ball_support_finite hf).toFinset : Set ℂ) := by
    intro z hz
    simp only [Function.mem_support, ne_eq, Int.cast_eq_zero] at hz
    simpa [Set.Finite.mem_toFinset] using hz
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp]
  have hxs : c + (R : ℂ) ∈ sphere c R := by simp [abs_of_pos hR]
  have htop : ∀ z ∈ closedBall c R, meromorphicOrderAt f z ≠ ⊤ := fun z hz =>
    hf.meromorphicOrderAt_ne_top_of_isPreconnected (convex_closedBall c R).isPreconnected
      (sphere_subset_closedBall hxs) hz (by rw [hsphere _ hxs]; exact WithTop.zero_ne_top)
  refine argumentPrinciple hR _ (fun z => MeromorphicOn.divisor f (ball c R) z) hf ?_ ?_ ?_
  · intro z hz
    simp only [Set.Finite.coe_toFinset, Function.mem_support] at hz
    exact (MeromorphicOn.divisor f (ball c R)).supportWithinDomain hz
  · intro z hz hord
    have hzball : z ∈ ball c R := by
      rcases lt_or_eq_of_le (mem_closedBall.mp hz) with h | h
      · exact mem_ball.mpr h
      · exact absurd (hsphere z (mem_sphere.mpr h)) hord
    simp only [Set.Finite.mem_toFinset, Function.mem_support, ne_eq,
      MeromorphicOn.divisor_apply hfb hzball]
    exact fun hc => hord ((WithTop.untop₀_eq_zero.mp hc).resolve_right (htop z hz))
  · intro z hz
    simp only [Set.Finite.mem_toFinset, Function.mem_support] at hz
    have hzball := (MeromorphicOn.divisor f (ball c R)).supportWithinDomain hz
    rw [MeromorphicOn.divisor_apply hfb hzball,
      WithTop.coe_untop₀_of_ne_top (htop z (ball_subset_closedBall hzball))]

end TauCeti.Contour
