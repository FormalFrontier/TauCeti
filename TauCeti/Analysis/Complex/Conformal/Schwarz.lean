module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# A strict form of the Schwarz lemma

Schwarz's lemma bounds the derivative at the centre of a ball by `1` when a holomorphic map sends
that ball into the closed ball of the same radius about the image of the centre. This file records
the **strict** form: the bound is attained only by an injective map, so a non-injective one has
`‖deriv g c‖ < 1`.

## The argument

Mathlib's `Complex.norm_deriv_le_one_of_mapsTo_ball` gives `‖deriv g c‖ ≤ 1`. In the equality case
`Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div` — the equality case of Schwarz, available for
`ℂ` because it is a strictly convex space — forces `g` to be the affine map
`z ↦ g c + (z - c) * deriv g c` on the ball. The multiplier is nonzero, having norm `1`, so that map
is injective, contradicting the hypothesis.

## Main statements

* `TauCeti.norm_deriv_lt_one_of_not_injOn` — the strict bound.

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

/-- **Strict Schwarz lemma.** A holomorphic map of `ball c R` into `closedBall (g c) R` that is
**not** injective has `‖deriv g c‖ < 1`.

Schwarz's lemma gives `‖deriv g c‖ ≤ 1`; in the equality case the map is affine with nonzero
multiplier, hence injective. -/
theorem norm_deriv_lt_one_of_not_injOn {g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hgd : DifferentiableOn ℂ g (ball c R)) (hgm : MapsTo g (ball c R) (closedBall (g c) R))
    (hgi : ¬ InjOn g (ball c R)) : ‖deriv g c‖ < 1 := by
  rcases (Complex.norm_deriv_le_one_of_mapsTo_ball hgd hgm hR).lt_or_eq with hlt | heq
  · exact hlt
  refine absurd ?_ hgi
  -- In the equality case Schwarz forces `g z = g c + (z - c) * deriv g c`, which is injective.
  have hds : ‖dslope g c c‖ = R / R := by
    rw [div_self hR.ne']
    simpa [dslope_same] using heq
  have haff := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hgd hgm (mem_ball_self hR) hds
  have hd₀ : deriv g c ≠ 0 := fun h₀ => one_ne_zero (heq.symm.trans (by rw [h₀, norm_zero]))
  intro z hz w hw hzw
  rw [haff hz, haff hw] at hzw
  simp only [dslope_same, smul_eq_mul, add_right_inj] at hzw
  linear_combination mul_right_cancel₀ hd₀ hzw

end TauCeti
