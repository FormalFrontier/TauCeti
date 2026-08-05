/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import TauCeti.Topology.MetricSpace.Cut

/-!
# The near side of a ball cut by a sphere

`TauCeti/Topology/MetricSpace/Cut.lean` cuts an arbitrary set `s` by a sphere `sphere y ρ` into a
*near side* `s ∩ ball y ρ` and a *far side* `s \ closedBall y ρ`. This file specialises the cut set
to a ball, `s = ball x r`, and records what the near side then is: a convex set, hence connected as
soon as it is nonempty, hence one of the two connected components of the cut ball. Its frontier is
covered by the two spheres involved.

Everything here is stated at the generality its proof uses, which is never more than a real normed
space and for the frontier bound not even that:

* the frontier bound `TauCeti.frontier_ball_inter_ball_subset` is Mathlib's `frontier_inter_subset`
  fed with `frontier_ball_subset_sphere` and `closure_ball_subset_closedBall`, so it holds in an
  arbitrary pseudo-metric space, with no relation between the two balls;
* nonemptiness, connectedness and the component identification use convexity of a ball, so they
  ask for a real vector space with a seminorm, and nothing else — no completeness, no
  non-degeneracy of the norm, and no finite dimensionality.

The *far side* is deliberately absent: it is not convex, and identifying it needs a genuine
argument that depends on the ambient geometry. In the plane that argument is the Möbius inversion
at the cut point, and it lives with its complex-analytic consumer in
`TauCeti/Analysis/Complex/Conformal/Crosscut/Basic.lean`
(`TauCeti.isConnected_ball_diff_closedBall` and
`TauCeti.connectedComponentIn_ball_diff_sphere_eq_ball_diff_closedBall`).

## The overlap condition

Two balls meet exactly when their radii together exceed the distance between the centres. One
direction is Mathlib's `Metric.dist_lt_add_of_nonempty_ball_inter_ball`; the other is
`TauCeti.nonempty_ball_inter_ball`, whose witness is the point `c + t • (ζ - c)` of the segment
joining the two centres at the parameter `t = r / (r + ρ)` that divides it in the ratio of the two
radii. That one parameter works for every pair of balls: it puts the witness at distance
`r * dist c ζ / (r + ρ)` from `c` and `ρ * dist c ζ / (r + ρ)` from `ζ`, and both are below the
corresponding radius precisely when `dist c ζ < r + ρ`.

## The intended consumer

Layer **L5** of `TauCetiRoadmap/ConformalMapping/README.md`, Carathéodory's boundary
correspondence, cuts a disc `ball c r` in the plane by the circle `sphere ζ ρ` about a point `ζ`
of its boundary — the *circular crosscut* of
`TauCeti/Analysis/Complex/Conformal/Crosscut/Basic.lean` — and reads the boundary behaviour of a
conformal map along the near side. There `dist ζ c = r`, so
the overlap condition `dist c ζ < r + ρ` holds for every `ρ > 0`, and the frontier bound is what
the maximum modulus principle is applied against. None of that is used here.

## Main results

* `TauCeti.frontier_ball_inter_ball_subset` — the frontier of the near side lies on the two spheres.
* `TauCeti.nonempty_ball_inter_ball` — two balls that overlap meet.
* `TauCeti.isConnected_ball_inter_ball` — the near side is connected.
* `TauCeti.connectedComponentIn_ball_diff_sphere_eq_ball_inter_ball` — the near side is a connected
  component of the cut ball.
-/

public section

namespace TauCeti

open Metric Set

section PseudoMetric

variable {X : Type*} [PseudoMetricSpace X] {x y : X} {r ρ : ℝ}

/-- **The frontier of the near side lies on the two spheres.** The frontier of `ball x r ∩ ball y ρ`
is covered by the piece `sphere x r ∩ closedBall y ρ` of the first sphere inside the second closed
ball together with the piece `closedBall x r ∩ sphere y ρ` of the second sphere inside the first
closed ball.

Only the inclusion is claimed, and only the inclusion holds without further hypotheses: if one ball
contains the other, the near side is that ball and its frontier misses the other sphere entirely.

This is Mathlib's `frontier_inter_subset`, whose two summands are pinned down by
`frontier_ball_subset_sphere` and `closure_ball_subset_closedBall`. Nothing relates the two balls,
and no hypothesis on the radii is needed. -/
theorem frontier_ball_inter_ball_subset :
    frontier (ball x r ∩ ball y ρ) ⊆ sphere x r ∩ closedBall y ρ ∪ closedBall x r ∩ sphere y ρ :=
  (frontier_inter_subset _ _).trans <| union_subset_union
    (inter_subset_inter frontier_ball_subset_sphere closure_ball_subset_closedBall)
    (inter_subset_inter closure_ball_subset_closedBall frontier_ball_subset_sphere)

end PseudoMetric

section Normed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {c ζ z : E} {r ρ : ℝ}

/-- **Two balls whose radii together exceed the distance between their centres meet.** This is the
converse of Mathlib's `Metric.dist_lt_add_of_nonempty_ball_inter_ball`, and it is where the linear
structure enters: the witness is the point of the segment joining the two centres that divides it
in the ratio of the two radii,
`c + (r / (r + ρ)) • (ζ - c)`, at distance `r * dist c ζ / (r + ρ) < r` from `c` and
`ρ * dist c ζ / (r + ρ) < ρ` from `ζ`.

Both radii must be positive, or the corresponding ball is empty while the hypothesis can still
hold. -/
theorem nonempty_ball_inter_ball (hr : 0 < r) (hρ : 0 < ρ) (h : dist c ζ < r + ρ) :
    (ball c r ∩ ball ζ ρ).Nonempty := by
  have hsum : 0 < r + ρ := by linarith
  set t : ℝ := r / (r + ρ) with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : 0 ≤ 1 - t := by
    rw [sub_nonneg, ht, div_le_one hsum]
    linarith
  have hone : 1 - t = ρ / (r + ρ) := by
    rw [ht, eq_div_iff hsum.ne', sub_mul, one_mul, div_mul_cancel₀ _ hsum.ne']
    ring
  refine ⟨c + t • (ζ - c), ?_, ?_⟩
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht0, ← dist_eq_norm, dist_comm ζ c, ht, div_mul_eq_mul_div,
      div_lt_iff₀ hsum]
    exact mul_lt_mul_of_pos_left h hr
  · have hsub : c + t • (ζ - c) - ζ = (1 - t) • (c - ζ) := by module
    rw [mem_ball, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht1,
      ← dist_eq_norm, hone, div_mul_eq_mul_div, div_lt_iff₀ hsum]
    exact mul_lt_mul_of_pos_left h hρ

/-- **The near side of a cut ball is connected**, being an intersection of two balls, hence convex.
Its nonemptiness is `TauCeti.nonempty_ball_inter_ball`, and that is the only role the overlap
condition `dist c ζ < r + ρ` plays. -/
theorem isConnected_ball_inter_ball (hr : 0 < r) (hρ : 0 < ρ) (h : dist c ζ < r + ρ) :
    IsConnected (ball c r ∩ ball ζ ρ) :=
  ((convex_ball c r).inter (convex_ball ζ ρ)).isConnected (nonempty_ball_inter_ball hr hρ h)

/-- **The near side is a connected component of the cut ball.** Removing `sphere ζ ρ` from
`ball c r` leaves the near side `ball c r ∩ ball ζ ρ` and the far side `ball c r \ closedBall ζ ρ`;
the near side is preconnected, being convex, and by
`TauCeti.subset_inter_ball_or_subset_sdiff_closedBall` the component of one of its points cannot
spill into the far side.

No hypothesis on the radii is needed: the membership `hz` already forces both to be positive, and
the statement is about the component of `z` alone. -/
theorem connectedComponentIn_ball_diff_sphere_eq_ball_inter_ball (hz : z ∈ ball c r ∩ ball ζ ρ) :
    connectedComponentIn (ball c r \ sphere ζ ρ) z = ball c r ∩ ball ζ ρ := by
  have hsub : ball c r ∩ ball ζ ρ ⊆ ball c r \ sphere ζ ρ :=
    sdiff_sphere_eq_inter_ball_union_sdiff_closedBall (x := ζ) (s := ball c r) ▸ subset_union_left
  refine Subset.antisymm ?_ (((convex_ball c r).inter (convex_ball ζ ρ)).isPreconnected
    |>.subset_connectedComponentIn hz hsub)
  rcases subset_inter_ball_or_subset_sdiff_closedBall (x := ζ) (s := ball c r) isOpen_ball
    isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _) with h | h
  · exact h
  · exact absurd (h (mem_connectedComponentIn (hsub hz)))
      (Set.disjoint_left.mp disjoint_inter_ball_sdiff_closedBall hz)

end Normed

end TauCeti
