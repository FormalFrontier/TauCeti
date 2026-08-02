/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected
public import TauCeti.Analysis.Normed.Module.DiamFrontier
public import TauCeti.Topology.ClusterSet

/-!
# The piece a crosscut cuts off, measured by its boundary

`Conformal/Crosscut/Basic.lean` cuts a disc `ball c r` at a boundary point `ζ` by the circle
`sphere ζ ρ`, leaving the *crosscut neighbourhood* `ball c r ∩ ball ζ ρ` of `ζ`, and turns an
oscillation bound on that neighbourhood into a boundary limit. This file supplies such a bound for a
*conformal* map, in the geometric form that layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md` — the Carathéodory boundary correspondence — produces
it: the image of the crosscut neighbourhood is no wider than the image of the crosscut arc together
with the piece of `∂Ω` that arc cuts off.

## The boundary of the image of a crosscut neighbourhood

Write `Ω = f '' ball c r` for the image domain and `A = f '' (ball c r ∩ ball ζ ρ)` for the image of
the crosscut neighbourhood, `f` being holomorphic and injective on the disc. Then
(`TauCeti.frontier_image_ball_inter_ball_subset`)

> `frontier A ⊆ f '' (ball c r ∩ sphere ζ ρ) ∪ frontier Ω`:

the boundary of `A` consists of the *image crosscut* and of boundary points of `Ω`, and nothing
else. The proof is the open mapping theorem applied three times. A point `p` of `frontier A` lies in
`closure Ω = Ω ∪ frontier Ω`; if it is not on `frontier Ω` it is `f w` for a unique `w` in the disc,
and `w` is at distance `< ρ`, `= ρ` or `> ρ` from `ζ`. The first case puts `p` in the open set `A`,
which is disjoint from `frontier A`. The third puts `p` in the *open* image of the far side
`ball c r \ closedBall ζ ρ`, which injectivity makes disjoint from `A`, contradicting `p ∈ closure
A`. So only the middle case survives, and there `p` lies on the image crosscut. Simple connectivity
of the disc plays no role, and neither does the geometry of `Ω`.

## From the boundary to the piece

A bounded set in a normed space is exactly as wide as its frontier
(`TauCeti.diam_frontier`, in `TauCeti/Analysis/Normed/Module/DiamFrontier.lean`), so the inclusion
above is already a diameter bound: for any `E` containing the boundary points of `Ω` that lie on
`frontier A`,

> `diam A ≤ diam (f '' (ball c r ∩ sphere ζ ρ) ∪ E)`

(`TauCeti.diam_image_ball_inter_ball_le`). Feeding those bounds, one for each tolerance, to the
Cauchy criterion of `Topology/ClusterSet.lean` gives the boundary limit
`TauCeti.exists_tendsto_nhdsWithin_ball_of_forall_exists_diam_union_le` and, if the bounds are
available at every point of the boundary circle, the continuous extension to the closed disc
`TauCeti.exists_continuousOn_closedBall_eqOn_of_forall_exists_diam_union_le`.

This is the **geometric** counterpart of the analytic criterion
`TauCeti.exists_continuousOn_closedBall_eqOn` of `Conformal/Crosscut/Basic.lean`. That one asks for
a bound on the values of `f` along the crosscut arc *and along a collar* of the boundary circle, and
runs on the maximum modulus principle; this one replaces the collar bound by a hypothesis about
the *image*, namely that the boundary points of `Ω` clinging to the cut-off piece can be enclosed in
a small set `E`. That is the shape in which the two remaining L5 inputs arrive: the length–area
method makes the image crosscut short, and local connectedness of `∂Ω` supplies the small
connected `E`
joining its two ends. Neither is proved here; what is proved here is that those two data suffice,
with no maximum principle and no estimate on `f` inside the disc.

Nothing below assumes that `ζ` lies on the boundary circle, that `ρ` is smaller than `2 * r`, or
that `Ω` is anything but bounded, so the hypotheses stay checkable; only the final two theorems,
which produce a limit, ask `ζ` to be a boundary point.

## Generality

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0–L6, everything below is stated for maps of `ℂ`. The two ingredients
are stated at their own generality elsewhere: `TauCeti.diam_frontier` for an arbitrary real normed
space, and `TauCeti.IsPreconnected.inter_frontier_nonempty` for an arbitrary topological space.

## Main results

* `TauCeti.frontier_image_ball_inter_ball_subset` — the boundary of the image of a crosscut
  neighbourhood is covered by the image crosscut and the boundary of the image domain.
* `TauCeti.diam_image_ball_inter_ball_le` — the image of a crosscut neighbourhood is no wider than
  the image crosscut together with the boundary piece it cuts off.
* `TauCeti.subsingleton_clusterSetOn_ball_of_forall_exists_diam_le` and
  `TauCeti.subsingleton_clusterSetOn_ball_of_forall_exists_diam_union_le` — small cut-off pieces
  make the boundary cluster set a subsingleton.
* `TauCeti.exists_tendsto_nhdsWithin_ball_of_forall_exists_diam_union_le` and
  `TauCeti.exists_continuousOn_closedBall_eqOn_of_forall_exists_diam_union_le` — the resulting
  boundary limit and continuous extension to the closed disc.

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

variable {f : ℂ → ℂ} {c ζ : ℂ} {r ρ : ℝ}

/-! ## The boundary of the image of a crosscut neighbourhood -/

/-- **The boundary of the image of a crosscut neighbourhood lies on the image crosscut and on the
boundary of the image domain.** For `f` holomorphic and injective on `ball c r`, the frontier of the
image `f '' (ball c r ∩ ball ζ ρ)` of the crosscut neighbourhood is covered by the image
`f '' (ball c r ∩ sphere ζ ρ)` of the crosscut arc together with `frontier (f '' ball c r)`.

The three sets `f '' (ball c r ∩ ball ζ ρ)`, `f '' (ball c r \ closedBall ζ ρ)` and `f '' ball c r`
are open by the open mapping theorem, and injectivity makes the first two disjoint. A frontier point
of the first that is not a frontier point of the third is therefore a value `f w` with
`dist w ζ = ρ`: the case `dist w ζ < ρ` would place it inside an open set disjoint from its own
frontier, and the case `dist w ζ > ρ` would place it inside an open set disjoint from a set it is in
the closure of. -/
theorem frontier_image_ball_inter_ball_subset (hd : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) :
    frontier (f '' (ball c r ∩ ball ζ ρ))
      ⊆ f '' (ball c r ∩ sphere ζ ρ) ∪ frontier (f '' ball c r) := by
  have hAopen : IsOpen (f '' (ball c r ∩ ball ζ ρ)) :=
    isOpen_image_of_differentiableOn_of_injOn (isOpen_ball.inter isOpen_ball)
      (hd.mono inter_subset_left) (hinj.mono inter_subset_left)
  intro p hp
  have hpΩ : p ∈ closure (f '' ball c r) :=
    closure_mono (image_mono inter_subset_left) hp.1
  rw [closure_eq_self_union_frontier] at hpΩ
  rcases hpΩ with hpin | hpfr
  · obtain ⟨w, hw, rfl⟩ := hpin
    rcases lt_trichotomy (dist w ζ) ρ with hlt | heq | hgt
    · exact absurd ⟨⟨w, ⟨hw, mem_ball.mpr hlt⟩, rfl⟩, hp⟩
        (eq_empty_iff_forall_notMem.mp hAopen.inter_frontier_eq (f w))
    · exact Or.inl ⟨w, ⟨hw, mem_sphere.mpr heq⟩, rfl⟩
    · exfalso
      have hBopen : IsOpen (f '' (ball c r \ closedBall ζ ρ)) :=
        isOpen_image_of_differentiableOn_of_injOn (isOpen_ball.sdiff isClosed_closedBall)
          (hd.mono sdiff_subset) (hinj.mono sdiff_subset)
      have hwB : f w ∈ f '' (ball c r \ closedBall ζ ρ) :=
        ⟨w, ⟨hw, fun hc => absurd (mem_closedBall.mp hc) (not_le.mpr hgt)⟩, rfl⟩
      obtain ⟨q, ⟨u, hu, hfu⟩, ⟨v, hv, hfv⟩⟩ := mem_closure_iff.mp hp.1 _ hBopen hwB
      have huv : u = v := hinj hu.1 hv.1 (hfu.trans hfv.symm)
      subst huv
      exact hu.2 (ball_subset_closedBall hv.2)
  · exact Or.inr hpfr

/-! ## The diameter of the cut-off piece -/

/-- **The image of a crosscut neighbourhood is no wider than the image crosscut together with the
boundary piece it cuts off.** If every boundary point of the image domain `f '' ball c r` that lies
on the frontier of `f '' (ball c r ∩ ball ζ ρ)` belongs to a bounded set `E`, then the diameter of
that image is at most the diameter of `f '' (ball c r ∩ sphere ζ ρ) ∪ E`.

This is `TauCeti.frontier_image_ball_inter_ball_subset` read through `TauCeti.diam_frontier`, which
says a bounded set has exactly the diameter of its frontier. No estimate on `f` is used: the width
of the cut-off piece is entirely determined by the width of what bounds it. -/
theorem diam_image_ball_inter_ball_le (hd : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) (hb : IsBounded (f '' ball c r)) {E : Set ℂ} (hE : IsBounded E)
    (hEsub : frontier (f '' ball c r) ∩ frontier (f '' (ball c r ∩ ball ζ ρ)) ⊆ E) :
    diam (f '' (ball c r ∩ ball ζ ρ)) ≤ diam (f '' (ball c r ∩ sphere ζ ρ) ∪ E) := by
  have harc : IsBounded (f '' (ball c r ∩ sphere ζ ρ)) :=
    hb.subset (image_mono inter_subset_left)
  rw [← diam_frontier (hb.subset (image_mono inter_subset_left))]
  refine diam_mono (fun p hp => ?_) (harc.union hE)
  rcases frontier_image_ball_inter_ball_subset hd hinj hp with h | h
  · exact Or.inl h
  · exact Or.inr (hEsub ⟨h, hp⟩)

/-! ## The boundary limit -/

/-- **Small cut-off pieces make the boundary cluster set a subsingleton.** If for every `ε > 0`
there is a radius `ρ > 0` at which the image `f '' (ball c r ∩ ball ζ ρ)` of the crosscut
neighbourhood has diameter at most `ε`, then `f` has at most one cluster value at `ζ` along the
disc.

Only boundedness of the image is assumed — no holomorphy, no injectivity — because the diameter
hypothesis *is* the Cauchy criterion of `TauCeti.subsingleton_clusterSetOn_of_forall_exists`: the
crosscut neighbourhoods are exactly the traces on the disc of the balls around `ζ`. Boundedness is
needed only because `Metric.diam` vanishes on unbounded sets, so a diameter bound is otherwise no
bound at all. -/
theorem subsingleton_clusterSetOn_ball_of_forall_exists_diam_le (hb : IsBounded (f '' ball c r))
    (h : ∀ ε > 0, ∃ ρ > 0, diam (f '' (ball c r ∩ ball ζ ρ)) ≤ ε) :
    (clusterSetOn f (ball c r) ζ).Subsingleton := by
  refine subsingleton_clusterSetOn_of_forall_exists fun ε hε => ?_
  obtain ⟨ρ, hρ, hdiam⟩ := h ε hε
  refine ⟨ρ, hρ, fun x hx y hy => le_trans ?_ hdiam⟩
  exact dist_le_diam_of_mem (hb.subset (image_mono inter_subset_left))
    (mem_image_of_mem f hx) (mem_image_of_mem f hy)

/-- **The crosscut criterion in geometric form, cluster-set version.** If for every `ε > 0` there
is a crosscut radius `ρ > 0` and a bounded set `E` enclosing the boundary points of the image domain
that cling to the cut-off piece, such that the image crosscut together with `E` has diameter at most
`ε`, then `f` has at most one cluster value at `ζ` along the disc.

This is `TauCeti.diam_image_ball_inter_ball_le` fed to
`TauCeti.subsingleton_clusterSetOn_ball_of_forall_exists_diam_le`. -/
theorem subsingleton_clusterSetOn_ball_of_forall_exists_diam_union_le
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r))
    (h : ∀ ε > 0, ∃ ρ > 0, ∃ E : Set ℂ, IsBounded E ∧
      frontier (f '' ball c r) ∩ frontier (f '' (ball c r ∩ ball ζ ρ)) ⊆ E ∧
      diam (f '' (ball c r ∩ sphere ζ ρ) ∪ E) ≤ ε) :
    (clusterSetOn f (ball c r) ζ).Subsingleton := by
  refine subsingleton_clusterSetOn_ball_of_forall_exists_diam_le hb fun ε hε => ?_
  obtain ⟨ρ, hρ, E, hEb, hEsub, hEdiam⟩ := h ε hε
  exact ⟨ρ, hρ, (diam_image_ball_inter_ball_le hd hinj hb hEb hEsub).trans hEdiam⟩

/-- **The crosscut criterion in geometric form, boundary-limit version.** A conformal map of a disc
with bounded image has a limit at a boundary point `ζ`, along the disc, as soon as the pieces it
cuts off at `ζ` can be made small in the sense of
`TauCeti.subsingleton_clusterSetOn_ball_of_forall_exists_diam_union_le`.

The cluster set is a subsingleton by that theorem, and it is nonempty because `f` maps the disc into
the compact closure of its bounded image, which is what
`TauCeti.exists_tendsto_of_clusterSetOn_subsingleton` needs. -/
theorem exists_tendsto_nhdsWithin_ball_of_forall_exists_diam_union_le (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r)) (hζ : dist ζ c = r)
    (h : ∀ ε > 0, ∃ ρ > 0, ∃ E : Set ℂ, IsBounded E ∧
      frontier (f '' ball c r) ∩ frontier (f '' (ball c r ∩ ball ζ ρ)) ⊆ E ∧
      diam (f '' (ball c r ∩ sphere ζ ρ) ∪ E) ≤ ε) :
    ∃ v, Tendsto f (𝓝[ball c r] ζ) (𝓝 v) := by
  refine exists_tendsto_of_clusterSetOn_subsingleton hb.isCompact_closure
    (fun w hw => subset_closure ⟨w, hw, rfl⟩) ?_
    (subsingleton_clusterSetOn_ball_of_forall_exists_diam_union_le hd hinj hb h)
  rw [closure_ball c hr.ne']
  exact mem_closedBall.mpr hζ.le

/-- **The crosscut criterion in geometric form, continuous-extension version.** If the hypothesis of
`TauCeti.exists_tendsto_nhdsWithin_ball_of_forall_exists_diam_union_le` holds at *every* point
of the boundary circle, the conformal map `f` extends continuously to `closedBall c r`.

This is the shape the Carathéodory boundary correspondence is proved in once the two geometric
inputs are available: the length–area method makes the image crosscut short at some radius, and
local connectedness of the image boundary supplies the small set `E` joining its ends. Nothing here
asserts that the extension is injective, which is an independent matter. -/
theorem exists_continuousOn_closedBall_eqOn_of_forall_exists_diam_union_le (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r))
    (h : ∀ w ∈ sphere c r, ∀ ε > 0, ∃ ρ > 0, ∃ E : Set ℂ, IsBounded E ∧
      frontier (f '' ball c r) ∩ frontier (f '' (ball c r ∩ ball w ρ)) ⊆ E ∧
      diam (f '' (ball c r ∩ sphere w ρ) ∪ E) ≤ ε) :
    ∃ F : ℂ → ℂ, ContinuousOn F (closedBall c r) ∧ EqOn F f (ball c r) := by
  obtain ⟨F, hFc, hFe⟩ := exists_continuousOn_closure_eqOn_of_isBounded isOpen_ball
    hd.continuousOn hb fun w hw => by
      refine subsingleton_clusterSetOn_ball_of_forall_exists_diam_union_le hd hinj hb (h w ?_)
      rwa [frontier_ball c hr.ne'] at hw
  exact ⟨F, closure_ball c hr.ne' ▸ hFc, hFe⟩

end TauCeti
