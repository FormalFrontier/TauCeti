/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Cutting a set by a sphere

Removing the sphere `sphere x ρ` from a set `s` leaves two pieces: the *near side*
`s ∩ ball x ρ`, of the points of `s` closer to `x` than `ρ`, and the *far side*
`s \ closedBall x ρ`, of those further away. This file records that they cover `s \ sphere x ρ`,
that they are disjoint, and — when `s` is open, so that both sides are open — that a preconnected
subset of `s` missing the sphere lies entirely in one of them.

Nothing beyond the containments `ball x ρ ⊆ closedBall x ρ` and `sphere x ρ ⊆ closedBall x ρ`, and
the openness of a ball against the closedness of a closed ball, is used, so `s` is an arbitrary set
in an arbitrary pseudo-metric space.

The intended consumer is layer **L5** of `TauCetiRoadmap/ConformalMapping/README.md`, Carathéodory's
boundary correspondence, through `TauCeti/Analysis/Complex/Conformal/Crosscut/Basic.lean` and
`TauCeti/Analysis/Complex/Conformal/CutDiameter.lean`: there `X = ℂ` and the sphere is the
*circular crosscut* of a plane domain at a boundary point, whose near side is the approach region
along which the boundary behaviour of a conformal map is read off. Nothing here is specific to that
use, and Mathlib has no form of the decomposition.

## Main results

* `TauCeti.sdiff_sphere_eq_inter_ball_union_sdiff_closedBall` — the two sides cover the cut set.
* `TauCeti.disjoint_inter_ball_sdiff_closedBall` — the two sides are disjoint.
* `TauCeti.subset_inter_ball_or_subset_sdiff_closedBall` — a preconnected subset of an open cut set
  missing the sphere lies on one side of it.
-/

public section

namespace TauCeti

open Metric Set

variable {X : Type*} [PseudoMetricSpace X] {x : X} {ρ : ℝ}

/-- **A circular cut splits a set into a near side and a far side.** Removing the sphere
`sphere x ρ` from a set `s` leaves the points of `s` at distance less than `ρ` from `x` together
with those at distance more than `ρ`. -/
theorem sdiff_sphere_eq_inter_ball_union_sdiff_closedBall {s : Set X} :
    s \ sphere x ρ = s ∩ ball x ρ ∪ s \ closedBall x ρ := by
  ext y
  constructor
  · rintro ⟨hy, hne⟩
    rw [Metric.mem_sphere] at hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl ⟨hy, Metric.mem_ball.mpr h⟩
    · exact Or.inr ⟨hy, fun hc => absurd (Metric.mem_closedBall.mp hc) (not_le.mpr h)⟩
  · rintro (⟨hy, h⟩ | ⟨hy, h⟩)
    · exact ⟨hy, fun hc => (Metric.mem_ball.mp h).ne (Metric.mem_sphere.mp hc)⟩
    · exact ⟨hy, fun hc => h (Metric.sphere_subset_closedBall hc)⟩

/-- The two sides of a circular cut are disjoint, the near side lying inside `closedBall x ρ` and
the far side outside it. -/
theorem disjoint_inter_ball_sdiff_closedBall {s : Set X} :
    Disjoint (s ∩ ball x ρ) (s \ closedBall x ρ) :=
  Set.disjoint_sdiff_right.mono_left (inter_subset_right.trans ball_subset_closedBall)

/-- **A connected subset of an open set missing a circular cut lies on one side of it.** This is
the separation statement the decomposition exists for: the two sides are open and disjoint, so a
preconnected subset of their union cannot meet both. Only openness of the cut set is used. -/
theorem subset_inter_ball_or_subset_sdiff_closedBall {s S : Set X} (hs : IsOpen s)
    (hS : IsPreconnected S) (hSsub : S ⊆ s \ sphere x ρ) :
    S ⊆ s ∩ ball x ρ ∨ S ⊆ s \ closedBall x ρ :=
  hS.subset_or_subset (hs.inter isOpen_ball) (hs.sdiff isClosed_closedBall)
    disjoint_inter_ball_sdiff_closedBall
    (sdiff_sphere_eq_inter_ball_union_sdiff_closedBall (x := x) (s := s) ▸ hSsub)

end TauCeti
