/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# A strict form of the Schwarz lemma

Schwarz's lemma bounds the derivative at the centre of a ball by `R₂ / R₁` when a holomorphic
map into a strictly convex complex normed space sends `ball c R₁` into `closedBall (g c) R₂`.
This file records the **strict** form: the bound is attained only by an injective map, so a
non-injective one has `‖deriv g c‖ < R₂ / R₁`.

## The argument

Mathlib's `Complex.norm_deriv_le_div_of_mapsTo_ball` gives `‖deriv g c‖ ≤ R₂ / R₁`. In the equality
case `Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div` — the equality case of Schwarz, available
for `ℂ` because it is a strictly convex space — forces `g` to be the affine map
`z ↦ g c + (z - c) • deriv g c` on the ball. The slope is a nonzero vector, having norm
`R₂ / R₁ > 0`, so that map is injective, contradicting the hypothesis.

Both radii must be positive. With `R₂ = 0` the target is the single point `g c`, so `g` is constant
and *not* injective, while the claimed bound `‖deriv g c‖ < 0` is false.

## Main statements

* `TauCeti.norm_deriv_lt_div_of_not_injOn` — the strict bound.
* `TauCeti.norm_deriv_lt_one_of_not_injOn` — its equal-radius form.

## Coordination with upstream Mathlib

The Riemann mapping theorem is being formalized upstream at
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), which proves the
L0–L3 prerequisites internally as private lemmas. The declaration here is an explicitly
**temporary shim**: delete it and refactor downstream consumers onto the exported Mathlib version
once that lands.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6 §1.2.
-/

public section

namespace TauCeti

open Complex Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [StrictConvexSpace ℝ E]

/-- **Strict Schwarz lemma.** A holomorphic map of `ball c R₁` into `closedBall (g c) R₂` that is
**not** injective has `‖deriv g c‖ < R₂ / R₁`.

Schwarz's lemma gives `‖deriv g c‖ ≤ R₂ / R₁`; in the equality case the map is affine with nonzero
slope, hence injective. Both radii must be positive: for `R₂ = 0` the map is constant, so it is
not injective and the strict bound fails. -/
theorem norm_deriv_lt_div_of_not_injOn {g : ℂ → E} {c : ℂ} {R₁ R₂ : ℝ} (hR₁ : 0 < R₁)
    (hR₂ : 0 < R₂) (hgd : DifferentiableOn ℂ g (ball c R₁))
    (hgm : MapsTo g (ball c R₁) (closedBall (g c) R₂)) (hgi : ¬ InjOn g (ball c R₁)) :
    ‖deriv g c‖ < R₂ / R₁ := by
  rcases (Complex.norm_deriv_le_div_of_mapsTo_ball hgd hgm hR₁).lt_or_eq with hlt | heq
  · exact hlt
  refine absurd ?_ hgi
  -- In the equality case Schwarz forces `g z = g c + (z - c) * deriv g c`, which is injective.
  have hds : ‖dslope g c c‖ = R₂ / R₁ := by simpa [dslope_same] using heq
  have haff := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hgd hgm (mem_ball_self hR₁) hds
  have hd₀ : deriv g c ≠ 0 := by
    intro h₀
    rw [h₀, norm_zero] at heq
    exact (div_pos hR₂ hR₁).ne' heq.symm
  intro z hz w hw hzw
  rw [haff hz, haff hw] at hzw
  simp only [dslope_same, add_right_inj] at hzw
  -- The slope is a nonzero vector, so the affine map is injective.
  have hsub : (z - w) • deriv g c = 0 := by
    rw [sub_smul]
    rw [sub_smul, sub_smul] at hzw
    have := sub_eq_zero.mpr hzw
    simpa using this
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hd₀)

/-- **Strict Schwarz lemma, equal radii.** A holomorphic map of `ball c R` into
`closedBall (g c) R` that is **not** injective has `‖deriv g c‖ < 1`. -/
theorem norm_deriv_lt_one_of_not_injOn {g : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hgd : DifferentiableOn ℂ g (ball c R)) (hgm : MapsTo g (ball c R) (closedBall (g c) R))
    (hgi : ¬ InjOn g (ball c R)) : ‖deriv g c‖ < 1 := by
  simpa [div_self hR.ne'] using norm_deriv_lt_div_of_not_injOn hR hR hgd hgm hgi

end TauCeti
