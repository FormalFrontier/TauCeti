/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected
public import TauCeti.Analysis.Normed.Module.DiamFrontier
public import TauCeti.Topology.ClusterSet
import TauCeti.Analysis.Complex.Conformal.Crosscut.Basic

/-!
# The piece a crosscut cuts off, measured by its boundary

`Conformal/Crosscut/Basic.lean` cuts a domain at a boundary point `ζ` by the circle `sphere ζ ρ`,
leaving the *crosscut neighbourhood* `U ∩ ball ζ ρ` of `ζ`, and turns an oscillation bound on that
neighbourhood into a boundary limit. This file supplies such a bound for a *conformal* map, in the
geometric form that layer **L5** of `TauCetiRoadmap/ConformalMapping/README.md` — the Carathéodory
boundary correspondence — produces it: the image of the crosscut neighbourhood is no wider than the
image of the crosscut arc together with the piece of `∂Ω` that arc cuts off.

## The boundary of the image of a crosscut neighbourhood

Write `Ω = f '' U` for the image domain and `A = f '' (U ∩ ball ζ ρ)` for the image of the crosscut
neighbourhood, `f` being holomorphic and injective on the open set `U`. Then
(`TauCeti.frontier_image_inter_ball_subset`)

> `frontier A ⊆ f '' (U ∩ sphere ζ ρ) ∪ frontier Ω`:

the boundary of `A` consists of the *image crosscut* and of boundary points of `Ω`, and nothing
else.

Nothing in that statement distinguishes the two sides of the crosscut, so it is proved once for an
arbitrary splitting of the domain into two disjoint open pieces `s`, `t` and a remainder `u`
(`TauCeti.frontier_image_subset_image_union_frontier_image`), by the open mapping theorem applied
twice: a point `p` of `frontier (f '' s)` lies in `closure Ω = Ω ∪ frontier Ω`, so if it is not on
`frontier Ω` it is `f w` for a unique `w` in `U`, and `w ∈ s` would put `p` in the open set
`f '' s`, which is disjoint from its own frontier, while `w ∈ t` would put `p` in the *open* set
`f '' t`, which injectivity makes disjoint from `f '' s`, contradicting `p ∈ closure (f '' s)`.
So `w ∈ u`. Simple connectivity plays no role, and neither does the geometry of `Ω` — nor even
openness of `U`, which enters only when the splitting is produced.

Instantiating it at the near side and at the far side `U \ closedBall ζ ρ`, which by
`TauCeti.diff_sphere_eq_inter_ball_union_diff_closedBall` are disjoint and open and leave exactly
the crosscut arc, gives `TauCeti.frontier_image_inter_ball_subset` and
`TauCeti.frontier_image_diff_closedBall_subset`: a consumer may bound either side.

## From the boundary to the piece

A bounded set in a normed space is exactly as wide as its frontier
(`TauCeti.diam_frontier`, in `TauCeti/Analysis/Normed/Module/DiamFrontier.lean`), so the inclusion
above is already a diameter bound: for any `E` containing the boundary points of `Ω` that lie on
`frontier A`,

> `diam A ≤ diam (f '' (U ∩ sphere ζ ρ) ∪ E)`

(`TauCeti.diam_image_inter_ball_le`), and likewise for the far side
(`TauCeti.diam_image_diff_closedBall_le`), both through the same
`TauCeti.diam_image_le_diam_image_union`. Feeding those bounds, one for each tolerance, to the
Cauchy criterion of `Topology/ClusterSet.lean` gives the boundary limit
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
every theorem added in layers L0–L6, everything below is stated for maps of `ℂ`. The two ingredients
are stated at their own generality elsewhere: `TauCeti.diam_frontier` for an arbitrary real normed
space, and `TauCeti.IsPreconnected.inter_frontier_nonempty` for an arbitrary topological space.

## Main results

* `TauCeti.frontier_image_subset_image_union_frontier_image` and
  `TauCeti.diam_image_le_diam_image_union` — the boundary inclusion and the diameter bound for one
  side of an arbitrary splitting of the domain into two disjoint open pieces and a remainder.
* `TauCeti.frontier_image_inter_ball_subset` and `TauCeti.frontier_image_diff_closedBall_subset` —
  the boundary of the image of either side of a crosscut is covered by the image crosscut and the
  boundary of the image domain.
* `TauCeti.diam_image_inter_ball_le` and `TauCeti.diam_image_diff_closedBall_le` — either side of a
  crosscut has image no wider than the image crosscut together with the boundary piece it cuts off.
* `TauCeti.subsingleton_clusterSetOn_of_forall_exists_diam_le` and
  `TauCeti.subsingleton_clusterSetOn_of_forall_exists_diam_union_le` — small cut-off pieces make
  the boundary cluster set a subsingleton.
* `TauCeti.exists_tendsto_nhdsWithin_of_forall_exists_diam_union_le` and
  `TauCeti.exists_continuousOn_closure_eqOn_of_forall_exists_diam_union_le` — the resulting
  boundary limit and continuous extension to the closure.

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

/-- **The boundary of the image of one open side of a splitting of a domain lies on the image of
the splitting set and on the boundary of the image of the domain.** If `U` is covered by two
disjoint open subsets `s` and `t` of it together with a third set `u`, and `f` is holomorphic and
injective on `U`, then `frontier (f '' s) ⊆ f '' u ∪ frontier (f '' U)`.

The two sides enter symmetrically, so the lemma bounds either of them; the crosscut instances are
`TauCeti.frontier_image_inter_ball_subset` and
`TauCeti.frontier_image_diff_closedBall_subset`.

The sets `f '' s` and `f '' t` are open by the open mapping theorem, and injectivity makes them
disjoint. A frontier point of `f '' s` lies in `closure (f '' U)`, so if it is not a frontier point
of `f '' U` it is a value `f w` with `w` in one of the three covering sets: `w ∈ s` would place it
inside an open set disjoint from its own frontier, and `w ∈ t` inside an open set disjoint from a
set it is in the closure of, so `w ∈ u`. Openness of `U` is not used: only the two named sides need
to be open. -/
theorem frontier_image_subset_image_union_frontier_image
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U) {s t u : Set ℂ}
    (hs : IsOpen s) (ht : IsOpen t) (hsU : s ⊆ U) (htU : t ⊆ U)
    (hst : Disjoint s t) (hcov : U ⊆ s ∪ t ∪ u) :
    frontier (f '' s) ⊆ f '' u ∪ frontier (f '' U) := by
  have hsopen : IsOpen (f '' s) :=
    isOpen_image_of_differentiableOn_of_injOn hs (hd.mono hsU) (hinj.mono hsU)
  have htopen : IsOpen (f '' t) :=
    isOpen_image_of_differentiableOn_of_injOn ht (hd.mono htU) (hinj.mono htU)
  intro p hp
  have hpΩ : p ∈ closure (f '' U) := closure_mono (image_mono hsU) hp.1
  rw [closure_eq_self_union_frontier] at hpΩ
  rcases hpΩ with hpin | hpfr
  · obtain ⟨w, hw, rfl⟩ := hpin
    rcases hcov hw with (hws | hwt) | hwu
    · exact absurd ⟨mem_image_of_mem f hws, hp⟩
        (eq_empty_iff_forall_notMem.mp hsopen.inter_frontier_eq (f w))
    · obtain ⟨q, ⟨v, hv, hfv⟩, ⟨x, hx, hfx⟩⟩ :=
        mem_closure_iff.mp hp.1 _ htopen (mem_image_of_mem f hwt)
      exact absurd (hinj (htU hv) (hsU hx) (hfv.trans hfx.symm) ▸ hv)
        (Set.disjoint_left.mp hst hx)
    · exact Or.inl (mem_image_of_mem f hwu)
  · exact Or.inr hpfr

/-- **The boundary of the image of a crosscut neighbourhood lies on the image crosscut and on the
boundary of the image domain.** For `f` holomorphic and injective on an open `U`, the frontier of
the image `f '' (U ∩ ball ζ ρ)` of the crosscut neighbourhood is covered by the image
`f '' (U ∩ sphere ζ ρ)` of the crosscut arc together with `frontier (f '' U)`.

This is `TauCeti.frontier_image_subset_image_union_frontier_image` for the near side of the
crosscut, the two sides of which are disjoint and open and cover the domain apart from the crosscut
arc by `TauCeti.diff_sphere_eq_inter_ball_union_diff_closedBall`. -/
theorem frontier_image_inter_ball_subset (hUo : IsOpen U) (hd : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) :
    frontier (f '' (U ∩ ball ζ ρ)) ⊆ f '' (U ∩ sphere ζ ρ) ∪ frontier (f '' U) := by
  have hcov : U = U ∩ ball ζ ρ ∪ U \ closedBall ζ ρ ∪ U ∩ sphere ζ ρ := by
    rw [← diff_sphere_eq_inter_ball_union_diff_closedBall, sdiff_union_inter]
  exact frontier_image_subset_image_union_frontier_image hd hinj
    (hUo.inter isOpen_ball) (hUo.sdiff isClosed_closedBall) inter_subset_left
    sdiff_subset disjoint_inter_ball_diff_closedBall hcov.subset

/-- **The boundary of the image of the far side of a crosscut lies on the image crosscut and on the
boundary of the image domain.** The mirror of `TauCeti.frontier_image_inter_ball_subset`: it is
`TauCeti.frontier_image_subset_image_union_frontier_image` read across the crosscut, the two sides
entering that lemma symmetrically. -/
theorem frontier_image_diff_closedBall_subset (hUo : IsOpen U) (hd : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) :
    frontier (f '' (U \ closedBall ζ ρ)) ⊆ f '' (U ∩ sphere ζ ρ) ∪ frontier (f '' U) := by
  have hcov : U = U \ closedBall ζ ρ ∪ U ∩ ball ζ ρ ∪ U ∩ sphere ζ ρ := by
    rw [union_comm (U \ closedBall ζ ρ), ← diff_sphere_eq_inter_ball_union_diff_closedBall,
      sdiff_union_inter]
  exact frontier_image_subset_image_union_frontier_image hd hinj
    (hUo.sdiff isClosed_closedBall) (hUo.inter isOpen_ball) sdiff_subset
    inter_subset_left disjoint_inter_ball_diff_closedBall.symm hcov.subset

/-! ## The diameter of the cut-off piece -/

/-- **A piece of the domain whose image has its boundary on the image of a set and on the boundary
of the image domain is no wider than the two together.** For `s` and `u` inside `U` with
`frontier (f '' s) ⊆ f '' u ∪ frontier (f '' U)`, and a bounded `E` containing the boundary points
of the image domain that lie on `frontier (f '' s)`, the image `f '' s` has diameter at most that of
`f '' u ∪ E`.

This is `TauCeti.diam_frontier` — a bounded set has exactly the diameter of its frontier — applied
to a boundary inclusion; no estimate on `f` is used, the width of the piece being entirely
determined by the width of what bounds it. -/
theorem diam_image_le_diam_image_union (hb : IsBounded (f '' U)) {s u : Set ℂ}
    (hsU : s ⊆ U) (huU : u ⊆ U)
    (hfr : frontier (f '' s) ⊆ f '' u ∪ frontier (f '' U)) {E : Set ℂ} (hE : IsBounded E)
    (hEsub : frontier (f '' U) ∩ frontier (f '' s) ⊆ E) :
    diam (f '' s) ≤ diam (f '' u ∪ E) := by
  rw [← diam_frontier (hb.subset (image_mono hsU))]
  refine diam_mono (fun p hp => ?_) ((hb.subset (image_mono huU)).union hE)
  rcases hfr hp with h | h
  · exact Or.inl h
  · exact Or.inr (hEsub ⟨h, hp⟩)

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
theorem diam_image_diff_closedBall_le (hUo : IsOpen U) (hd : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) (hb : IsBounded (f '' U)) {E : Set ℂ} (hE : IsBounded E)
    (hEsub : frontier (f '' U) ∩ frontier (f '' (U \ closedBall ζ ρ)) ⊆ E) :
    diam (f '' (U \ closedBall ζ ρ)) ≤ diam (f '' (U ∩ sphere ζ ρ) ∪ E) :=
  diam_image_le_diam_image_union hb sdiff_subset inter_subset_left
    (frontier_image_diff_closedBall_subset hUo hd hinj) hE hEsub

/-! ## The boundary limit -/

/-- **Small cut-off pieces make the boundary cluster set a subsingleton.** If for every `ε > 0`
there is a radius `ρ > 0` at which the image `f '' (U ∩ ball ζ ρ)` of the crosscut neighbourhood has
diameter at most `ε`, then `f` has at most one cluster value at `ζ` along `U`.

Only boundedness of the image is assumed — no holomorphy, no injectivity — because the diameter
hypothesis *is* the Cauchy criterion of `TauCeti.subsingleton_clusterSetOn_of_forall_exists`: the
crosscut neighbourhoods are exactly the traces on `U` of the balls around `ζ`. Boundedness is needed
only because `Metric.diam` vanishes on unbounded sets, so a diameter bound is otherwise no bound at
all. -/
theorem subsingleton_clusterSetOn_of_forall_exists_diam_le (hb : IsBounded (f '' U))
    (h : ∀ ε > 0, ∃ ρ > 0, diam (f '' (U ∩ ball ζ ρ)) ≤ ε) :
    (clusterSetOn f U ζ).Subsingleton := by
  refine subsingleton_clusterSetOn_of_forall_exists fun ε hε => ?_
  obtain ⟨ρ, hρ, hdiam⟩ := h ε hε
  refine ⟨ρ, hρ, fun x hx y hy => le_trans ?_ hdiam⟩
  exact dist_le_diam_of_mem (hb.subset (image_mono inter_subset_left))
    (mem_image_of_mem f hx) (mem_image_of_mem f hy)

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

end TauCeti
