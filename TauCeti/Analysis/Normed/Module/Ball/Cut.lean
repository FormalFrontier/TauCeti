/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import TauCeti.Topology.MetricSpace.Cut
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# A set cut by a sphere, in a normed space

`TauCeti/Topology/MetricSpace/Cut.lean` cuts an arbitrary set `s` by a sphere `sphere y ρ` into a
*near side* `s ∩ ball y ρ` and a *far side* `s \ closedBall y ρ`. This file adds what the linear
structure of a normed space contributes to that cut.

Two things, of which the first keeps the cut set arbitrary: for an *open* `s`, the part of the
cutting sphere inside `s` is adherent to **both** sides, because in a normed space a sphere is
adherent both to the open ball it bounds and to the exterior of the closed one. So neither side can
be separated from the cut itself.

The second specialises the cut set to a ball, `s = ball x r`, and records what the near side then
is: a convex set, hence connected as soon as it is nonempty, hence a connected component of the cut
ball. Its frontier is covered by the two spheres involved.

Only *a* component, and not one of exactly two: at this generality the far side can itself be
disconnected — in `ℝ`, cutting `ball 0 1` by `sphere 0 (1 / 2)` leaves three components — so how
many components the cut ball has is a question about the ambient geometry, settled in the plane
rather than here.

Everything here is stated at the generality its proof uses, which is never more than a seminormed
real vector space and for the frontier bound not even that:

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

Two balls *of positive radius* meet exactly when their radii together exceed the distance between
the centres. One direction is Mathlib's `Metric.dist_lt_add_of_nonempty_ball_inter_ball`, and needs
no positivity; the other is `TauCeti.nonempty_ball_inter_ball`, and does — a ball of non-positive
radius is empty while `dist c ζ < r + ρ` can still hold.

Its witness is supplied by Mathlib's `exists_dist_lt_lt`: the point of the segment joining the two
centres that divides it in the ratio of the two radii, at distance `r * dist c ζ / (r + ρ)` from
`c` and `ρ * dist c ζ / (r + ρ)` from `ζ`, both below the corresponding radius precisely when
`dist c ζ < r + ρ`.

## The intended consumer

Layer **L5** of `TauCetiRoadmap/ConformalMapping/README.md`, Carathéodory's boundary
correspondence, cuts a disc `ball c r` in the plane by the circle `sphere ζ ρ` about a point `ζ`
of its boundary — the *circular crosscut* of
`TauCeti/Analysis/Complex/Conformal/Crosscut/Basic.lean` — and reads the boundary behaviour of a
conformal map along the near side. There `dist ζ c = r`, so
the overlap condition `dist c ζ < r + ρ` holds for every `ρ > 0`, and the frontier bound is what
the maximum modulus principle is applied against. None of that is used here.

## Main results

* `TauCeti.inter_sphere_subset_closure_inter_ball` and
  `TauCeti.inter_sphere_subset_closure_sdiff_closedBall` — the part of the cutting sphere inside an
  open set is adherent to both sides of the cut.
* `TauCeti.frontier_ball_inter_ball_subset` — the frontier of the near side lies on the two spheres.
* `TauCeti.nonempty_ball_inter_ball` — two balls that overlap meet, and
  `TauCeti.nonempty_ball_inter_sphere` — a sphere about a boundary point of a ball, of radius below
  the diameter of the ball, meets it.
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

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {c ζ z : E} {r ρ : ℝ}

/-! ## Both sides of the cut cling to the cutting sphere -/

/-- **The cut of an open set clings to the near side.** The part `s ∩ sphere x r` of the cutting
sphere lying in an open `s` is adherent to the near side `s ∩ ball x r`.

The linear structure enters through `closure_ball`, which identifies the closure of a ball of
nonzero radius with the closed ball and so puts the sphere inside it; the openness of `s` is what
lets the closure be taken inside the intersection, by `IsOpen.inter_closure`. Both hypotheses are
needed: in a general metric space a sphere can be disjoint from the closure of its ball, and for a
non-open `s` the point of `s ∩ sphere x r` may be isolated in `s`. -/
theorem inter_sphere_subset_closure_inter_ball (hs : IsOpen s) (x : E) (hr : r ≠ 0) :
    s ∩ sphere x r ⊆ closure (s ∩ ball x r) := by
  have hsph : sphere x r ⊆ closure (ball x r) := by
    rw [closure_ball x hr]; exact sphere_subset_closedBall
  exact (inter_subset_inter_right s hsph).trans hs.inter_closure

/-- **The cut of an open set clings to the far side.** The mirror of
`TauCeti.inter_sphere_subset_closure_inter_ball`: the part `s ∩ sphere x r` of the cutting sphere
lying in an open `s` is adherent to the far side `s \ closedBall x r` as well.

Here the sphere is put inside the closure of the *exterior* of the closed ball: it is the frontier
of that closed ball by `frontier_closedBall`, hence the frontier of its complement, hence adherent
to it. -/
theorem inter_sphere_subset_closure_sdiff_closedBall (hs : IsOpen s) (x : E) (hr : r ≠ 0) :
    s ∩ sphere x r ⊆ closure (s \ closedBall x r) := by
  have hsph : sphere x r ⊆ closure (closedBall x r)ᶜ := by
    rw [← frontier_closedBall x hr, ← frontier_compl]
    exact frontier_subset_closure
  simpa only [sdiff_eq] using (inter_subset_inter_right s hsph).trans hs.inter_closure

/-! ## The near side of a ball -/

/-- **Two balls whose radii together exceed the distance between their centres meet.** This is the
converse of Mathlib's `Metric.dist_lt_add_of_nonempty_ball_inter_ball`, and it is where the linear
structure enters, through Mathlib's `exists_dist_lt_lt`: the witness is the point of the segment
joining the two centres that divides it in the ratio of the two radii, at distance
`r * dist c ζ / (r + ρ) < r` from `c` and `ρ * dist c ζ / (r + ρ) < ρ` from `ζ`.

Both radii must be positive, or the corresponding ball is empty while the hypothesis can still
hold. -/
theorem nonempty_ball_inter_ball (hr : 0 < r) (hρ : 0 < ρ) (h : dist c ζ < r + ρ) :
    (ball c r ∩ ball ζ ρ).Nonempty := by
  obtain ⟨w, hcw, hwζ⟩ := exists_dist_lt_lt hr hρ (by rwa [add_comm] at h)
  exact ⟨w, mem_ball'.2 hcw, mem_ball.2 hwζ⟩

/-- **A sphere about a boundary point of a ball meets that ball** as soon as its radius is positive
and below the diameter of the ball. Together with
`TauCeti.nonempty_ball_inter_ball` this says that a circular crosscut of a ball at a boundary point
is a genuine, nonempty cut.

The witness is the point `ζ + (ρ / r) • (c - ζ)` reached by walking from the cut centre `ζ` towards
the centre `c` of the ball for a distance `ρ`. It sits on `sphere ζ ρ` because `‖c - ζ‖ = r`, and at
distance `|r - ρ|` from `c`, which is below `r` exactly when `0 < ρ < 2 * r`; positivity of `r` is
not a separate hypothesis, being forced by those two bounds. -/
theorem nonempty_ball_inter_sphere (hζ : dist ζ c = r) (hρ : 0 < ρ) (hρ' : ρ < 2 * r) :
    (ball c r ∩ sphere ζ ρ).Nonempty := by
  have hr : 0 < r := by linarith
  have hnorm : ‖ζ - c‖ = r := by rw [← dist_eq_norm, hζ]
  have hpos : 0 < ρ / r := by positivity
  have hlt : ρ / r < 2 := (div_lt_iff₀ hr).mpr (by linarith)
  refine ⟨ζ + (ρ / r) • (c - ζ), ?_, ?_⟩
  · have hsub : ζ + (ρ / r) • (c - ζ) - c = (1 - ρ / r) • (ζ - c) := by module
    rw [mem_ball, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, hnorm]
    calc |1 - ρ / r| * r < 1 * r := by
          refine mul_lt_mul_of_pos_right (abs_lt.mpr ⟨by linarith, by linarith⟩) hr
      _ = r := one_mul r
  · rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hpos, ← dist_eq_norm, dist_comm, hζ, div_mul_cancel₀ _ hr.ne']

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
