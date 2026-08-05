/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected
public import TauCeti.Analysis.Normed.Module.DiamFrontier
public import TauCeti.Topology.ClusterSet
import TauCeti.Topology.MetricSpace.Cut

/-!
# The piece a crosscut cuts off, measured by its boundary

`Topology/MetricSpace/Cut.lean` supplies the set-splitting lemmas that cut a set at a point `ζ` by
the circle `sphere ζ ρ`, leaving the *crosscut neighbourhood* `U ∩ ball ζ ρ` of `ζ`, and
`Conformal/Crosscut/Basic.lean` turns an oscillation bound on that neighbourhood into a boundary
limit for a *disc* `U`, by the maximum modulus principle. This file carries that criterion to an
arbitrary open `U`, and supplies the oscillation bound for a *conformal* map, in the geometric form
that layer **L5** of `TauCetiRoadmap/ConformalMapping/README.md` — the Carathéodory boundary
correspondence — produces it: the image of the crosscut neighbourhood is no wider than the image of
the crosscut arc together with the piece of `∂Ω` that arc cuts off.

## The boundary of the image of a crosscut neighbourhood

Write `Ω = f '' U` for the image domain and `A = f '' (U ∩ ball ζ ρ)` for the image of the crosscut
neighbourhood, `f` being holomorphic and injective on the open set `U`. Then
(`TauCeti.frontier_image_inter_ball_subset`)

> `frontier A ⊆ f '' (U ∩ sphere ζ ρ) ∪ frontier Ω`:

the boundary of `A` consists of the *image crosscut* and of boundary points of `Ω`, and nothing
else.

Nothing in that statement distinguishes the two sides of the crosscut, nor uses any complex
analysis, so it is proved once and elsewhere:
`TauCeti.frontier_image_subset_image_union_frontier_image` in `TauCeti/Topology/Frontier.lean`
splits an arbitrary set into two pieces `s`, `t` with disjoint open images and a remainder `u`,
over arbitrary topological spaces. All that is spent here is the
open mapping theorem, which turns the two open sides of the crosscut into open images. Simple
connectivity plays no role, and neither does the geometry of `Ω` — nor even openness of `U`, which
enters only when the splitting is produced.

Instantiating it at the near side and at the far side `U \ closedBall ζ ρ`, which by
`TauCeti.sdiff_sphere_eq_inter_ball_union_sdiff_closedBall` are disjoint and open and leave exactly
the crosscut arc, gives `TauCeti.frontier_image_inter_ball_subset` and
`TauCeti.frontier_image_sdiff_closedBall_subset`: a consumer may bound either side.

## From the boundary to the piece

A bounded set in a normed space is no wider than anything bounded that contains its frontier
(`TauCeti.diam_le_diam_of_frontier_subset`, in
`TauCeti/Analysis/Normed/Module/DiamFrontier.lean`), so the inclusion above is already a diameter
bound: for any `E` containing the boundary points of `Ω` that lie on `frontier A`,

> `diam A ≤ diam (f '' (U ∩ sphere ζ ρ) ∪ E)`

(`TauCeti.diam_image_inter_ball_le`), and likewise for the far side
(`TauCeti.diam_image_sdiff_closedBall_le`), both through the same
`TauCeti.diam_image_le_diam_image_union`. Feeding those bounds, one for each tolerance, to the
Cauchy criterion `TauCeti.subsingleton_clusterSetOn_of_forall_exists_diam_le` of
`Topology/ClusterSet.lean` gives the boundary limit
`TauCeti.exists_tendsto_nhdsWithin_of_forall_exists_diam_union_le` and, if the bounds are available
at every point of `frontier U`, the continuous extension to `closure U`,
`TauCeti.exists_continuousOn_closure_eqOn_of_forall_exists_diam_union_le`.

This is the **geometric** counterpart of the analytic criterion
`TauCeti.exists_continuousOn_closedBall_eqOn` of `Conformal/Crosscut/Basic.lean`. That one asks for
a bound on the values of `f` along the crosscut arc *and along a collar* of the boundary circle, and
runs on the maximum modulus principle; this one replaces the collar bound by a hypothesis about
the *image*, namely that the boundary points of `Ω` clinging to the cut-off piece can be enclosed in
a small set `E`. That is the shape in which the two remaining L5 inputs arrive: the length–area
method makes the image crosscut short, and local connectedness of `∂Ω` supplies the small
connected `E`
joining its two ends. Neither is proved here; what is proved here is that those two data suffice,
with no maximum principle and no estimate on `f` inside the domain.

Nothing below assumes that `ζ` lies on `frontier U`, or that `Ω` is anything but bounded, so the
hypotheses stay checkable; only the final two theorems, which produce a limit, ask `ζ` to be
adherent to `U`.

## Generality

The domain `U` is an arbitrary open set rather than a disc. The disc is where the *inputs* live —
`Conformal/ShortCrosscut.lean` makes an image crosscut of a disc short — but nothing in the
argument below uses the shape of `U`, and the Carathéodory correspondence is a statement about
both a Jordan domain and the disc it is mapped from, so both directions of it are served only by
the general form. The cut itself is still a circle `sphere ζ ρ`, which is what makes the crosscut
neighbourhoods a neighbourhood basis of `ζ`.

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0–L6, everything below is stated for maps of `ℂ`. The three steps
that never mention a holomorphic map are stated at their own generality elsewhere, and consumed
here: `TauCeti.frontier_image_subset_image_union_frontier_image` for maps between arbitrary
topological spaces, `TauCeti.diam_le_diam_of_frontier_subset` — through `TauCeti.diam_frontier`
and `TauCeti.IsPreconnected.inter_frontier_nonempty` — for an arbitrary real normed space, and
`TauCeti.subsingleton_clusterSetOn_of_forall_exists_diam_le` for a map between metric spaces. What
remains here is exactly the conformal content: the open mapping theorem, and the reading of a
circular cut as a crosscut.

## Main results

* `TauCeti.diam_image_le_diam_image_union` — the diameter bound for one side of an arbitrary
  splitting of the domain into two pieces with disjoint open images and a remainder.
* `TauCeti.frontier_image_inter_ball_subset` and `TauCeti.frontier_image_sdiff_closedBall_subset` —
  the boundary of the image of either side of a crosscut is covered by the image crosscut and the
  boundary of the image domain.
* `TauCeti.diam_image_inter_ball_le` and `TauCeti.diam_image_sdiff_closedBall_le` — either side of a
  crosscut has image no wider than the image crosscut together with the boundary piece it cuts off.
* `TauCeti.subsingleton_clusterSetOn_of_forall_exists_diam_union_le` — small cut-off pieces make
  the boundary cluster set a subsingleton.
* `TauCeti.exists_tendsto_nhdsWithin_of_forall_exists_diam_union_le` and
  `TauCeti.exists_continuousOn_closure_eqOn_of_forall_exists_diam_union_le` — the resulting
  boundary limit and continuous extension to the closure.

The disc signatures these replace are kept as deprecated compatibility wrappers in a final section,
each naming its generalized replacement.

## Coordination with upstream Mathlib

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself, and Mathlib
has no boundary correspondence for conformal maps. So this file is new Lean formalization rather
than a temporary shim. It consumes the L0–L3 shim
`TauCeti.isOpen_image_of_differentiableOn_of_injOn`, to be refactored onto Mathlib's open mapping
API once the upstream work lands.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2–2.3.
* P. L. Duren, *Univalent Functions*, Ch. 3.
-/

public section

namespace TauCeti

open Bornology Complex Filter Metric Set Topology

variable {f : ℂ → ℂ} {U : Set ℂ} {ζ : ℂ} {ρ : ℝ}

/-! ## The boundary of the image of one side -/

/-- The open mapping theorem on an open piece of a domain of injective holomorphy. This is the only
place the analytic hypotheses enter the splitting step
`TauCeti.frontier_image_subset_image_union_frontier_image`, which asks nothing of `f` beyond
openness of the images of the two sides and injectivity across them. -/
private theorem isOpen_image_of_subset (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    {s : Set ℂ} (hsU : s ⊆ U) (hs : IsOpen s) : IsOpen (f '' s) :=
  isOpen_image_of_differentiableOn_of_injOn hs (hd.mono hsU) (hinj.mono hsU)

/-- **The boundary of the image of a crosscut neighbourhood lies on the image crosscut and on the
boundary of the image domain.** For `f` holomorphic and injective on an open `U`, the frontier of
the image `f '' (U ∩ ball ζ ρ)` of the crosscut neighbourhood is covered by the image
`f '' (U ∩ sphere ζ ρ)` of the crosscut arc together with `frontier (f '' U)`.

This is `TauCeti.frontier_image_subset_image_union_frontier_image` for the near side of the
crosscut, the two sides of which are disjoint and open and cover the domain apart from the crosscut
arc by `TauCeti.sdiff_sphere_eq_inter_ball_union_sdiff_closedBall`. -/
theorem frontier_image_inter_ball_subset (hUo : IsOpen U) (hd : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) :
    frontier (f '' (U ∩ ball ζ ρ)) ⊆ f '' (U ∩ sphere ζ ρ) ∪ frontier (f '' U) := by
  have hcov : U = U ∩ ball ζ ρ ∪ U \ closedBall ζ ρ ∪ U ∩ sphere ζ ρ := by
    rw [← sdiff_sphere_eq_inter_ball_union_sdiff_closedBall, sdiff_union_inter]
  have hsub : U ∩ ball ζ ρ ∪ U \ closedBall ζ ρ ⊆ U := union_subset inter_subset_left sdiff_subset
  exact frontier_image_subset_image_union_frontier_image
    (isOpen_image_of_subset hd hinj inter_subset_left (hUo.inter isOpen_ball))
    (isOpen_image_of_subset hd hinj sdiff_subset (hUo.sdiff isClosed_closedBall))
    (hinj.mono hsub) inter_subset_left disjoint_inter_ball_sdiff_closedBall hcov.subset

/-- **The boundary of the image of the far side of a crosscut lies on the image crosscut and on the
boundary of the image domain.** The mirror of `TauCeti.frontier_image_inter_ball_subset`: it is
`TauCeti.frontier_image_subset_image_union_frontier_image` read across the crosscut, the two sides
entering that lemma symmetrically. -/
theorem frontier_image_sdiff_closedBall_subset (hUo : IsOpen U) (hd : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) :
    frontier (f '' (U \ closedBall ζ ρ)) ⊆ f '' (U ∩ sphere ζ ρ) ∪ frontier (f '' U) := by
  have hcov : U = U \ closedBall ζ ρ ∪ U ∩ ball ζ ρ ∪ U ∩ sphere ζ ρ := by
    rw [union_comm (U \ closedBall ζ ρ), ← sdiff_sphere_eq_inter_ball_union_sdiff_closedBall,
      sdiff_union_inter]
  have hsub : U \ closedBall ζ ρ ∪ U ∩ ball ζ ρ ⊆ U := union_subset sdiff_subset inter_subset_left
  exact frontier_image_subset_image_union_frontier_image
    (isOpen_image_of_subset hd hinj sdiff_subset (hUo.sdiff isClosed_closedBall))
    (isOpen_image_of_subset hd hinj inter_subset_left (hUo.inter isOpen_ball))
    (hinj.mono hsub) sdiff_subset disjoint_inter_ball_sdiff_closedBall.symm hcov.subset

/-! ## The diameter of the cut-off piece -/

/-- **A piece of the domain whose image has its boundary on the image of a set and on the boundary
of the image domain is no wider than the two together.** For `s` and `u` inside `U` with
`frontier (f '' s) ⊆ f '' u ∪ frontier (f '' U)`, and a bounded `E` containing the boundary points
of the image domain that lie on `frontier (f '' s)`, the image `f '' s` has diameter at most that of
`f '' u ∪ E`.

This is `TauCeti.diam_le_diam_of_frontier_subset` — a bounded set is no wider than anything bounded
containing its frontier — applied to a boundary inclusion; no estimate on `f` is used, the width of
the piece being entirely determined by the width of what bounds it. The two hypotheses combine into
the single inclusion `frontier (f '' s) ⊆ f '' u ∪ E` that lemma consumes. -/
theorem diam_image_le_diam_image_union (hb : IsBounded (f '' U)) {s u : Set ℂ}
    (hsU : s ⊆ U) (huU : u ⊆ U)
    (hfr : frontier (f '' s) ⊆ f '' u ∪ frontier (f '' U)) {E : Set ℂ} (hE : IsBounded E)
    (hEsub : frontier (f '' U) ∩ frontier (f '' s) ⊆ E) :
    diam (f '' s) ≤ diam (f '' u ∪ E) :=
  diam_le_diam_of_frontier_subset (hb.subset (image_mono hsU))
    ((hb.subset (image_mono huU)).union hE)
    fun _ hp => (hfr hp).imp id fun h => hEsub ⟨h, hp⟩

/-- **The image of a crosscut neighbourhood is no wider than the image crosscut together with the
boundary piece it cuts off.** If every boundary point of the image domain `f '' U` that lies on the
frontier of `f '' (U ∩ ball ζ ρ)` belongs to a bounded set `E`, then the diameter of that image is
at most the diameter of `f '' (U ∩ sphere ζ ρ) ∪ E`.

This is `TauCeti.frontier_image_inter_ball_subset` read through
`TauCeti.diam_image_le_diam_image_union`. -/
theorem diam_image_inter_ball_le (hUo : IsOpen U) (hd : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) (hb : IsBounded (f '' U)) {E : Set ℂ} (hE : IsBounded E)
    (hEsub : frontier (f '' U) ∩ frontier (f '' (U ∩ ball ζ ρ)) ⊆ E) :
    diam (f '' (U ∩ ball ζ ρ)) ≤ diam (f '' (U ∩ sphere ζ ρ) ∪ E) :=
  diam_image_le_diam_image_union hb inter_subset_left inter_subset_left
    (frontier_image_inter_ball_subset hUo hd hinj) hE hEsub

/-- **The image of the far side of a crosscut is no wider than the image crosscut together with the
boundary piece it cuts off.** The mirror of `TauCeti.diam_image_inter_ball_le`: whichever of the two
sides a boundary piece is supplied for, that side is the one bounded. -/
theorem diam_image_sdiff_closedBall_le (hUo : IsOpen U) (hd : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) (hb : IsBounded (f '' U)) {E : Set ℂ} (hE : IsBounded E)
    (hEsub : frontier (f '' U) ∩ frontier (f '' (U \ closedBall ζ ρ)) ⊆ E) :
    diam (f '' (U \ closedBall ζ ρ)) ≤ diam (f '' (U ∩ sphere ζ ρ) ∪ E) :=
  diam_image_le_diam_image_union hb sdiff_subset inter_subset_left
    (frontier_image_sdiff_closedBall_subset hUo hd hinj) hE hEsub

/-! ## The boundary limit -/

/-- **The crosscut criterion in geometric form, cluster-set version.** If for every `ε > 0` there
is a crosscut radius `ρ > 0` and a bounded set `E` enclosing the boundary points of the image domain
that cling to the cut-off piece, such that the image crosscut together with `E` has diameter at most
`ε`, then `f` has at most one cluster value at `ζ` along `U`.

This is `TauCeti.diam_image_inter_ball_le` fed to
`TauCeti.subsingleton_clusterSetOn_of_forall_exists_diam_le`. -/
theorem subsingleton_clusterSetOn_of_forall_exists_diam_union_le (hUo : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U) (hb : IsBounded (f '' U))
    (h : ∀ ε > 0, ∃ ρ > 0, ∃ E : Set ℂ, IsBounded E ∧
      frontier (f '' U) ∩ frontier (f '' (U ∩ ball ζ ρ)) ⊆ E ∧
      diam (f '' (U ∩ sphere ζ ρ) ∪ E) ≤ ε) :
    (clusterSetOn f U ζ).Subsingleton := by
  refine subsingleton_clusterSetOn_of_forall_exists_diam_le hb fun ε hε => ?_
  obtain ⟨ρ, hρ, E, hEb, hEsub, hEdiam⟩ := h ε hε
  exact ⟨ρ, hρ, (diam_image_inter_ball_le hUo hd hinj hb hEb hEsub).trans hEdiam⟩

/-- **The crosscut criterion in geometric form, boundary-limit version.** A conformal map of a
domain with bounded image has a limit at a point `ζ` of its closure, along the domain, as soon as
the pieces it cuts off at `ζ` can be made small in the sense of
`TauCeti.subsingleton_clusterSetOn_of_forall_exists_diam_union_le`.

The cluster set is a subsingleton by that theorem, and it is nonempty because `f` maps the domain
into the compact closure of its bounded image, which is what
`TauCeti.exists_tendsto_of_clusterSetOn_subsingleton` needs. -/
theorem exists_tendsto_nhdsWithin_of_forall_exists_diam_union_le (hUo : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U) (hb : IsBounded (f '' U))
    (hζ : ζ ∈ closure U)
    (h : ∀ ε > 0, ∃ ρ > 0, ∃ E : Set ℂ, IsBounded E ∧
      frontier (f '' U) ∩ frontier (f '' (U ∩ ball ζ ρ)) ⊆ E ∧
      diam (f '' (U ∩ sphere ζ ρ) ∪ E) ≤ ε) :
    ∃ v, Tendsto f (𝓝[U] ζ) (𝓝 v) :=
  exists_tendsto_of_clusterSetOn_subsingleton hb.isCompact_closure
    (fun w hw => subset_closure ⟨w, hw, rfl⟩) hζ
    (subsingleton_clusterSetOn_of_forall_exists_diam_union_le hUo hd hinj hb h)

/-- **The crosscut criterion in geometric form, continuous-extension version.** If the hypothesis of
`TauCeti.exists_tendsto_nhdsWithin_of_forall_exists_diam_union_le` holds at *every* boundary point
of the domain, the conformal map `f` extends continuously to `closure U`.

This is the shape the Carathéodory boundary correspondence is proved in once the two geometric
inputs are available: the length–area method makes the image crosscut short at some radius, and
local connectedness of the image boundary supplies the small set `E` joining its ends. Nothing here
asserts that the extension is injective, which is an independent matter. For a disc,
`Metric.frontier_ball` and `Metric.closure_ball` turn the hypothesis and the conclusion into
statements about `sphere c r` and `closedBall c r`. -/
theorem exists_continuousOn_closure_eqOn_of_forall_exists_diam_union_le (hUo : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U) (hb : IsBounded (f '' U))
    (h : ∀ w ∈ frontier U, ∀ ε > 0, ∃ ρ > 0, ∃ E : Set ℂ, IsBounded E ∧
      frontier (f '' U) ∩ frontier (f '' (U ∩ ball w ρ)) ⊆ E ∧
      diam (f '' (U ∩ sphere w ρ) ∪ E) ≤ ε) :
    ∃ F : ℂ → ℂ, ContinuousOn F (closure U) ∧ EqOn F f U :=
  exists_continuousOn_closure_eqOn_of_isBounded hUo hd.continuousOn hb fun w hw =>
    subsingleton_clusterSetOn_of_forall_exists_diam_union_le hUo hd hinj hb (h w hw)

/-! ## Deprecated disc-specific forms

Everything above was stated for `U = ball c r`. The old signatures are retained here as deprecated
compatibility wrappers, each naming its generalized replacement; the openness hypothesis is
discharged by `Metric.isOpen_ball`, and `Metric.frontier_ball` and `Metric.closure_ball` turn
`frontier U` and `closure U` back into `sphere c r` and `closedBall c r`. -/

variable {c : ℂ} {r : ℝ}

/-- Deprecated compatibility wrapper for the disc case of
`TauCeti.frontier_image_subset_image_union_frontier_image`, which asks openness of the two images
rather than of the two sides, injectivity on `s ∪ t` only, no holomorphy, and does not need
`t ⊆ U`. -/
@[deprecated frontier_image_subset_image_union_frontier_image (since := "2026-08-04")]
theorem frontier_image_subset_image_union_frontier_image_ball
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r)) {s t u : Set ℂ}
    (hs : IsOpen s) (ht : IsOpen t) (hsr : s ⊆ ball c r) (htr : t ⊆ ball c r)
    (hst : Disjoint s t) (hcov : ball c r ⊆ s ∪ t ∪ u) :
    frontier (f '' s) ⊆ f '' u ∪ frontier (f '' ball c r) :=
  frontier_image_subset_image_union_frontier_image (isOpen_image_of_subset hd hinj hsr hs)
    (isOpen_image_of_subset hd hinj htr ht) (hinj.mono (union_subset hsr htr)) hsr hst hcov

/-- Deprecated compatibility wrapper for the disc case of
`TauCeti.frontier_image_inter_ball_subset`. -/
@[deprecated frontier_image_inter_ball_subset (since := "2026-08-04")]
theorem frontier_image_ball_inter_ball_subset (hd : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) :
    frontier (f '' (ball c r ∩ ball ζ ρ))
      ⊆ f '' (ball c r ∩ sphere ζ ρ) ∪ frontier (f '' ball c r) :=
  frontier_image_inter_ball_subset isOpen_ball hd hinj

/-- Deprecated compatibility wrapper for the disc case of
`TauCeti.frontier_image_sdiff_closedBall_subset`. -/
@[deprecated frontier_image_sdiff_closedBall_subset (since := "2026-08-04")]
theorem frontier_image_ball_diff_closedBall_subset (hd : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) :
    frontier (f '' (ball c r \ closedBall ζ ρ))
      ⊆ f '' (ball c r ∩ sphere ζ ρ) ∪ frontier (f '' ball c r) :=
  frontier_image_sdiff_closedBall_subset isOpen_ball hd hinj

/-- Deprecated compatibility wrapper for the disc case of `TauCeti.diam_image_inter_ball_le`. -/
@[deprecated diam_image_inter_ball_le (since := "2026-08-04")]
theorem diam_image_ball_inter_ball_le (hd : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) (hb : IsBounded (f '' ball c r)) {E : Set ℂ} (hE : IsBounded E)
    (hEsub : frontier (f '' ball c r) ∩ frontier (f '' (ball c r ∩ ball ζ ρ)) ⊆ E) :
    diam (f '' (ball c r ∩ ball ζ ρ)) ≤ diam (f '' (ball c r ∩ sphere ζ ρ) ∪ E) :=
  diam_image_inter_ball_le isOpen_ball hd hinj hb hE hEsub

/-- Deprecated compatibility wrapper for the disc case of
`TauCeti.diam_image_sdiff_closedBall_le`. -/
@[deprecated diam_image_sdiff_closedBall_le (since := "2026-08-04")]
theorem diam_image_ball_diff_closedBall_le (hd : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) (hb : IsBounded (f '' ball c r)) {E : Set ℂ} (hE : IsBounded E)
    (hEsub : frontier (f '' ball c r) ∩ frontier (f '' (ball c r \ closedBall ζ ρ)) ⊆ E) :
    diam (f '' (ball c r \ closedBall ζ ρ)) ≤ diam (f '' (ball c r ∩ sphere ζ ρ) ∪ E) :=
  diam_image_sdiff_closedBall_le isOpen_ball hd hinj hb hE hEsub

/-- Deprecated compatibility wrapper for the disc case of
`TauCeti.subsingleton_clusterSetOn_of_forall_exists_diam_le`. -/
@[deprecated subsingleton_clusterSetOn_of_forall_exists_diam_le (since := "2026-08-04")]
theorem subsingleton_clusterSetOn_ball_of_forall_exists_diam_le (hb : IsBounded (f '' ball c r))
    (h : ∀ ε > 0, ∃ ρ > 0, diam (f '' (ball c r ∩ ball ζ ρ)) ≤ ε) :
    (clusterSetOn f (ball c r) ζ).Subsingleton :=
  subsingleton_clusterSetOn_of_forall_exists_diam_le hb h

/-- Deprecated compatibility wrapper for the disc case of
`TauCeti.subsingleton_clusterSetOn_of_forall_exists_diam_union_le`. -/
@[deprecated subsingleton_clusterSetOn_of_forall_exists_diam_union_le (since := "2026-08-04")]
theorem subsingleton_clusterSetOn_ball_of_forall_exists_diam_union_le
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r))
    (h : ∀ ε > 0, ∃ ρ > 0, ∃ E : Set ℂ, IsBounded E ∧
      frontier (f '' ball c r) ∩ frontier (f '' (ball c r ∩ ball ζ ρ)) ⊆ E ∧
      diam (f '' (ball c r ∩ sphere ζ ρ) ∪ E) ≤ ε) :
    (clusterSetOn f (ball c r) ζ).Subsingleton :=
  subsingleton_clusterSetOn_of_forall_exists_diam_union_le isOpen_ball hd hinj hb h

/-- Deprecated compatibility wrapper for the disc case of
`TauCeti.exists_tendsto_nhdsWithin_of_forall_exists_diam_union_le`, whose hypothesis
`ζ ∈ closure U` the disc discharges from `dist ζ c = r` through `Metric.closure_ball`. -/
@[deprecated exists_tendsto_nhdsWithin_of_forall_exists_diam_union_le (since := "2026-08-04")]
theorem exists_tendsto_nhdsWithin_ball_of_forall_exists_diam_union_le (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r)) (hζ : dist ζ c = r)
    (h : ∀ ε > 0, ∃ ρ > 0, ∃ E : Set ℂ, IsBounded E ∧
      frontier (f '' ball c r) ∩ frontier (f '' (ball c r ∩ ball ζ ρ)) ⊆ E ∧
      diam (f '' (ball c r ∩ sphere ζ ρ) ∪ E) ≤ ε) :
    ∃ v, Tendsto f (𝓝[ball c r] ζ) (𝓝 v) :=
  exists_tendsto_nhdsWithin_of_forall_exists_diam_union_le isOpen_ball hd hinj hb
    (closure_ball c hr.ne' ▸ mem_closedBall.mpr hζ.le) h

/-- Deprecated compatibility wrapper for the disc case of
`TauCeti.exists_continuousOn_closure_eqOn_of_forall_exists_diam_union_le`, whose `frontier U` and
`closure U` the disc turns into `sphere c r` and `closedBall c r`. -/
@[deprecated exists_continuousOn_closure_eqOn_of_forall_exists_diam_union_le
  (since := "2026-08-04")]
theorem exists_continuousOn_closedBall_eqOn_of_forall_exists_diam_union_le (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r))
    (h : ∀ w ∈ sphere c r, ∀ ε > 0, ∃ ρ > 0, ∃ E : Set ℂ, IsBounded E ∧
      frontier (f '' ball c r) ∩ frontier (f '' (ball c r ∩ ball w ρ)) ⊆ E ∧
      diam (f '' (ball c r ∩ sphere w ρ) ∪ E) ≤ ε) :
    ∃ F : ℂ → ℂ, ContinuousOn F (closedBall c r) ∧ EqOn F f (ball c r) := by
  obtain ⟨F, hFc, hFe⟩ := exists_continuousOn_closure_eqOn_of_forall_exists_diam_union_le
    isOpen_ball hd hinj hb (frontier_ball c hr.ne' ▸ h)
  exact ⟨F, closure_ball c hr.ne' ▸ hFc, hFe⟩

end TauCeti
