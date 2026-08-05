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

The decomposition is then pushed forward through a map `f : X → Y`: the image of `s` is the union
of the images of the two sides and of the part of `s` on the sphere, and — for a topological `Y` —
the frontier of `f '' s` is covered by the frontiers of the two side images together with the
closure of the middle one. Nothing whatever is asked of `f`; it is not assumed continuous, let
alone injective or open.

The intended consumer is layer **L5** of `TauCetiRoadmap/ConformalMapping/README.md`, Carathéodory's
boundary correspondence, through `TauCeti/Analysis/Complex/Conformal/Crosscut/Basic.lean`,
`TauCeti/Analysis/Complex/Conformal/Crosscut/Image.lean` and
`TauCeti/Analysis/Complex/Conformal/CutDiameter.lean`: there `X = Y = ℂ` and the sphere is the
*circular crosscut* of a plane domain at a boundary point, whose near side is the approach region
along which the boundary behaviour of a conformal map is read off. Nothing here is specific to that
use, and Mathlib has no form of the decomposition.

## Main results

* `TauCeti.sdiff_sphere_eq_inter_ball_union_sdiff_closedBall` — the two sides cover the cut set.
* `TauCeti.disjoint_inter_ball_sdiff_closedBall` — the two sides are disjoint.
* `TauCeti.subset_inter_ball_or_subset_sdiff_closedBall` — a preconnected subset of an open cut set
  missing the sphere lies on one side of it.
* `TauCeti.image_eq_union_image_inter_sphere` — the image of a cut set is the union of the images
  of the two sides and of the part on the sphere.
* `TauCeti.frontier_image_subset_union_closure_image_inter_sphere` and
  `TauCeti.frontier_image_eq_union_closure_image_inter_sphere` — the frontier of the image is
  covered by, and so splits into, the frontiers of the two side images and the part of it adherent
  to the middle image.
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

/-! ## The cut pushed forward through a map -/

variable {Y : Type*}

/-- **A sphere splits the image of a set into three pieces**: the images of the parts of the set
inside, on, and outside it. This is
`TauCeti.sdiff_sphere_eq_inter_ball_union_sdiff_closedBall` pushed forward, and needs nothing of
`f` and nothing of `s`. -/
theorem image_eq_union_image_inter_sphere (f : X → Y) (s : Set X) (x : X) (ρ : ℝ) :
    f '' s = f '' (s ∩ ball x ρ) ∪ f '' (s ∩ sphere x ρ) ∪ f '' (s \ closedBall x ρ) := by
  rw [← image_union, ← image_union]
  congr 1
  rw [union_right_comm, ← sdiff_sphere_eq_inter_ball_union_sdiff_closedBall, sdiff_union_inter]

variable [TopologicalSpace Y]

/-- **The frontier of the image of a cut set is covered by the frontiers of the images of the two
sides together with the closure of the image of the part on the sphere.**

Like the decomposition itself this needs nothing of `f`: the image is the union of the three pieces
by `TauCeti.image_eq_union_image_inter_sphere`, the frontier of a union is covered by the frontiers
of the two parts by `frontier_union_subset`, and the frontier of the middle image lies in its
closure. -/
theorem frontier_image_subset_union_closure_image_inter_sphere (f : X → Y) (s : Set X) (x : X)
    (ρ : ℝ) :
    frontier (f '' s) ⊆
      frontier (f '' (s ∩ ball x ρ)) ∪ closure (f '' (s ∩ sphere x ρ)) ∪
        frontier (f '' (s \ closedBall x ρ)) := by
  have hunion : ∀ a b : Set Y, frontier (a ∪ b) ⊆ frontier a ∪ frontier b := fun a b =>
    (frontier_union_subset a b).trans (union_subset_union inter_subset_left inter_subset_right)
  rw [image_eq_union_image_inter_sphere f s x ρ]
  exact (hunion _ _).trans (union_subset_union
    ((hunion _ _).trans (union_subset_union subset_rfl frontier_subset_closure)) subset_rfl)

/-- **A sphere cuts the frontier of the image into two pieces and a middle piece.** The equality
form of `TauCeti.frontier_image_subset_union_closure_image_inter_sphere`: `frontier (f '' s)` is the
union of the two *boundary pieces* the sphere determines — its intersections with the frontiers of
the images of the parts of `s` inside and outside the sphere — and of the part of it adherent to
`f '' (s ∩ sphere x ρ)`.

The three pieces are not claimed to be disjoint, and none of them is claimed nonempty; what the
equality says is that no boundary point of the image escapes all three. -/
theorem frontier_image_eq_union_closure_image_inter_sphere (f : X → Y) (s : Set X) (x : X) (ρ : ℝ) :
    frontier (f '' s) =
      frontier (f '' s) ∩ frontier (f '' (s ∩ ball x ρ)) ∪
        frontier (f '' s) ∩ closure (f '' (s ∩ sphere x ρ)) ∪
        frontier (f '' s) ∩ frontier (f '' (s \ closedBall x ρ)) := by
  rw [← inter_union_distrib_left, ← inter_union_distrib_left]
  exact (inter_eq_left.mpr
    (frontier_image_subset_union_closure_image_inter_sphere f s x ρ)).symm

end TauCeti
