/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Crosscut.EndpointLimit
import TauCeti.Analysis.Complex.Conformal.ShortCrosscut

/-!
# The ends of an image crosscut are two boundary points

A circular crosscut `ball c r ∩ sphere ζ ρ` at a boundary point `ζ` of a disc is carried by a
conformal map `f` to a curve inside the image domain `f '' ball c r`, and that curve reaches the
boundary of the image domain only in the limit. Two files describe what it reaches:

* `Conformal/Crosscut/Image.lean` identifies the *boundary piece* the image crosscut clings to,
  `frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ))`, with the union of the cluster
  sets of `f` at the two endpoints of the crosscut, and shows each of those cluster sets to be a
  continuum;
* `Conformal/Crosscut/EndpointLimit.lean` collapses each continuum to a point as soon as the image
  crosscut has finite length, so that union is a pair
  (`TauCeti.exists_biUnion_clusterSetOn_ball_inter_sphere_eq_pair`).

Putting the two together is what this file does: for an *injective* holomorphic `f`, the closed
image crosscut meets the boundary of the image domain in a pair of points,

> `frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)) = {u, v}`,

and those two points are no further apart than the image crosscut is wide. Feeding that width
bound the length–area estimate of `Conformal/ShortCrosscut.lean` then gives the statement layer
**L5** of `TauCetiRoadmap/ConformalMapping/README.md` — Carathéodory's boundary correspondence —
consumes: at every boundary point of the disc, and below every prescribed radius, there is a
crosscut whose image is narrow *and* whose two ends are two points of the image boundary within
`ε` of each other.

That is precisely the hypothesis `TauCeti.IsJordanCurve.exists_pos_forall_exists_diam_le` of
`TauCeti/Topology/JordanCurve/SmallArc.lean` runs on: two nearby points of a Jordan curve cut a
small closed arc off it. Until now nothing connected the analytic side of L5 — the length–area
method, which produces short image crosscuts — to the topological side, which turns two nearby
boundary points into a small boundary arc; the pair `{u, v}` produced here is the connection.

## What is not claimed

The two ends may coincide: an image crosscut is free to close up, and no hypothesis available here
excludes it. So `{u, v}` is a pair only in the sense of `Set.instInsert`, possibly a singleton, and
the small-arc theorem — which asks `p ≠ q` — still has to rule that out from properties of the
image domain. Nor is the *piece* of the boundary cut off between the two ends identified: enclosing
`frontier (f '' ball c r) ∩ frontier (f '' (ball c r ∩ ball ζ ρ))` in a small bounded set is a
geometric input to `TauCeti.diam_image_inter_ball_le`, whose conclusion supplies the
approach-region diameter hypothesis of
`TauCeti.exists_continuousOn_closure_eqOn_of_forall_exists_diam_le`. That enclosure is a matter of
the image domain rather than of the crosscut, and is untouched here.

## Main results

* `TauCeti.exists_frontier_inter_closure_image_ball_inter_sphere_eq_pair` — the closed image
  crosscut of finite length meets the boundary of the image domain in a pair of points.
* `TauCeti.exists_frontier_inter_closure_image_ball_inter_sphere_eq_pair_dist_le`
  — the conclusion, from Wolff's lemma: a holomorphic injection of a disc with finite Dirichlet
  integral has, at every boundary point and below every positive radius, a crosscut whose image has
  diameter at most `ε` and whose two ends lie within `ε` of each other on the image boundary.
* `TauCeti.exists_frontier_inter_closure_image_ball_inter_sphere_eq_pair_dist_le_of_isBounded`
  — its corollary for an injection with bounded image, the case a Riemann map falls under.

## Generality

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0–L6, everything below is stated for maps of `ℂ`. The disc is a
general `ball c r` rather than the unit disc, the boundary point entering only through
`dist ζ c = r`.

## Coordination with upstream Mathlib

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself, and the
pinned Mathlib has no boundary correspondence for conformal maps. So this file is new Lean
formalization rather than a temporary shim. Through
`Conformal/Crosscut/Image.lean` it consumes the L0–L3 shim
`TauCeti.isOpen_image_of_differentiableOn_of_injOn`, to be refactored onto Mathlib's open mapping
API once the upstream work lands.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2–2.3 (crosscuts and the length–area
  method).
* P. L. Duren, *Univalent Functions*, Ch. 3.
-/

public section

namespace TauCeti

open Bornology Complex MeasureTheory Metric Set

variable {f : ℂ → ℂ} {c ζ : ℂ} {r ρ : ℝ}

/-! ## The boundary piece of an image crosscut is a pair -/

/-- **A closed image crosscut of finite length meets the boundary of the image domain in a pair
of points.** For `f` holomorphic and injective on `ball c r`, and a genuine circular crosscut
`ball c r ∩ sphere ζ ρ` at a boundary point `ζ` whose image has finite length,

> `frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)) = {u, v}`.

The two ingredients are already in place and only have to be matched up:
`TauCeti.frontier_inter_closure_image_inter_sphere_eq_biUnion_clusterSetOn` writes the left-hand
side as the union of the cluster sets of `f` over `frontier (ball c r) ∩ sphere ζ ρ`, which is
`sphere c r ∩ sphere ζ ρ` since `0 < r`, and
`TauCeti.exists_biUnion_clusterSetOn_ball_inter_sphere_eq_pair` evaluates that union to a pair.

Injectivity enters only through the first of the two, where it makes `f '' ball c r` open and so
disjoint from its own frontier; that is what excludes the image crosscut itself from the boundary
piece. The two points may coincide.

Membership of the two ends in `frontier (f '' ball c r)` is read off the statement: `u` and `v` lie
in `{u, v}`, hence in the left-hand side, hence in `frontier (f '' ball c r)`. -/
theorem exists_frontier_inter_closure_image_ball_inter_sphere_eq_pair (hζ : dist ζ c = r)
    (hρ : 0 < ρ) (hρr : ρ < 2 * r) (hf : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) (hfin : circleImageLength f (ball c r) ζ ρ ≠ ⊤) :
    ∃ u v, frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)) = {u, v} := by
  obtain ⟨u, v, hends⟩ := exists_biUnion_clusterSetOn_ball_inter_sphere_eq_pair hζ hρ hρr hf hfin
  have hr : 0 < r := by linarith
  refine ⟨u, v, ?_⟩
  rw [frontier_inter_closure_image_inter_sphere_eq_biUnion_clusterSetOn isOpen_ball hf hinj,
    frontier_ball c hr.ne', hends]

/-! ## Crosscuts with a short image and close ends -/

/-- **A holomorphic injection of finite Dirichlet integral has, at every boundary point, crosscuts
of arbitrarily small radius whose image is narrow and whose two ends are close together on the
image boundary.** For `f` holomorphic and injective on `ball c r` with
`∫⁻ z in ball c r, ‖deriv f z‖ₑ ^ 2 ≠ ⊤`, every tolerance `ε > 0` and every bound `R > 0` admit a
radius `ρ < R` at which the image of `ball c r ∩ sphere ζ ρ` has diameter at most `ε` and the
closed image crosscut meets `frontier (f '' ball c r)` in two points at distance at most `ε`.

The radius comes from
`TauCeti.exists_diam_image_ball_inter_sphere_le_and_circleImageLength_ne_top`, the length--area
selection of `Conformal/ShortCrosscut.lean`: below any prescribed bound it produces a radius at
which `TauCeti.circleImageLength f (ball c r) ζ ρ` is finite — which is what
`TauCeti.exists_frontier_inter_closure_image_ball_inter_sphere_eq_pair` needs, so the ends are two
points — and at which the image crosscut is no wider than `ε`. That width is passed on to the two
ends by `TauCeti.diam_frontier_inter_closure_image_inter_sphere_le`: they lie in the boundary piece
and so are no further apart than the image crosscut is wide.

Only `0 < r` is asked of the disc, and only `0 < R` of the prescribed bound: the radius is searched
for below `min R (2 * r)` instead of below `R`, which is what makes `ball c r ∩ sphere ζ ρ` a
genuine circular crosscut rather than the empty set. -/
theorem exists_frontier_inter_closure_image_ball_inter_sphere_eq_pair_dist_le
    (hζ : dist ζ c = r) (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) (hfin : ∫⁻ z in ball c r, ‖deriv f z‖ₑ ^ 2 ≠ ⊤) {ε : ℝ}
    (hε : 0 < ε) {R : ℝ} (hR : 0 < R) :
    ∃ ρ ∈ Ioo 0 R, ∃ u v,
      frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)) = {u, v} ∧
        dist u v ≤ ε ∧ diam (f '' (ball c r ∩ sphere ζ ρ)) ≤ ε := by
  obtain ⟨ρ, hρmem, hfin', hdiam, hb⟩ :=
    exists_diam_image_ball_inter_sphere_le_and_circleImageLength_ne_top (ζ := ζ) hf hfin hε
      (lt_min hR (by linarith : (0 : ℝ) < 2 * r))
  obtain ⟨u, v, hpair⟩ := exists_frontier_inter_closure_image_ball_inter_sphere_eq_pair hζ hρmem.1
    (hρmem.2.trans_le (min_le_right _ _)) hf hinj hfin'
  have hu : u ∈ frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)) := by
    rw [hpair]; exact mem_insert _ _
  have hv : v ∈ frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)) := by
    rw [hpair]; exact mem_insert_of_mem _ rfl
  exact ⟨ρ, ⟨hρmem.1, hρmem.2.trans_le (min_le_left _ _)⟩, u, v, hpair,
    (dist_le_diam_of_mem (hb.closure.subset inter_subset_right) hu hv).trans
      ((diam_frontier_inter_closure_image_inter_sphere_le hb).trans hdiam), hdiam⟩

/-- **A conformal map of a disc has, at every boundary point, crosscuts of arbitrarily small radius
whose image is narrow and whose two ends are close together on the image boundary.** This is the
case of `TauCeti.exists_frontier_inter_closure_image_ball_inter_sphere_eq_pair_dist_le`
that a Riemann map falls under: for `f` injective on `ball c r` with bounded image the Dirichlet
integral is the area of that image, hence finite by
`TauCeti.lintegral_enorm_deriv_sq_ne_top_of_isBounded`.

This is the form the Jordan-domain boundary correspondence consumes. Its two ends `u` and `v` lie
on `frontier (f '' ball c r)`, which for a Jordan domain is a Jordan curve, and they are within `ε`
of each other, so `TauCeti.IsJordanCurve.exists_pos_forall_exists_diam_le` cuts a small closed arc
off that curve between them — once `u ≠ v` is known, which nothing here supplies. -/
theorem exists_frontier_inter_closure_image_ball_inter_sphere_eq_pair_dist_le_of_isBounded
    (hζ : dist ζ c = r) (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) (hb : IsBounded (f '' ball c r)) {ε : ℝ} (hε : 0 < ε) {R : ℝ}
    (hR : 0 < R) :
    ∃ ρ ∈ Ioo 0 R, ∃ u v,
      frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)) = {u, v} ∧
        dist u v ≤ ε ∧ diam (f '' (ball c r ∩ sphere ζ ρ)) ≤ ε :=
  exists_frontier_inter_closure_image_ball_inter_sphere_eq_pair_dist_le hζ hr hf
    hinj (lintegral_enorm_deriv_sq_ne_top_of_isBounded isOpen_ball hf
      measurableSet_ball.nullMeasurableSet subset_rfl hinj hb) hε hR

end TauCeti
