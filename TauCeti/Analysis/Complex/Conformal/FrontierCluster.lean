/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.ClusterSet
public import TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected

/-!
# The boundary piece a crosscut cuts off, as boundary cluster sets

`Conformal/ClusterSet.lean` proves that the boundary cluster sets of a conformal map `f` on an open
`U` **exhaust** the frontier of the image: `⋃ w ∈ frontier U, clusterSetOn f U w =
frontier (f '' U)` (`TauCeti.biUnion_clusterSetOn_eq_frontier_image`). That covering is global — it
says nothing about *which* boundary points of the image are reached from a given part of
`frontier U`. This file localizes it to the crosscut decomposition that
`Conformal/CutDiameter.lean` runs on.

## The statement

Cut the disc `ball c r` at a point `ζ` of its boundary circle by the sphere `sphere ζ ρ`, leaving
the crosscut neighbourhood `ball c r ∩ ball ζ ρ`, and write `Ω = f '' ball c r` for the image
domain and `A = f '' (ball c r ∩ ball ζ ρ)` for the image of that neighbourhood. The *piece of
`∂Ω` cut off* is `frontier Ω ∩ frontier A`, the set `Conformal/CutDiameter.lean` asks to be
enclosed in a small set `E`. The two inclusions below identify it, up to the two endpoints of the
crosscut, with the union of the boundary cluster sets over the arc of the boundary circle that the
crosscut cuts off:

> `⋃ w ∈ sphere c r ∩ ball ζ ρ, clusterSetOn f (ball c r) w ⊆ frontier Ω ∩ frontier A ⊆`
> `⋃ w ∈ sphere c r ∩ closedBall ζ ρ, clusterSetOn f (ball c r) w`

(`TauCeti.biUnion_clusterSetOn_subset_frontier_image_inter_frontier_image` and
`TauCeti.frontier_image_inter_frontier_image_subset_biUnion_clusterSetOn`). The gap between the two
is exactly the pair of points `sphere c r ∩ sphere ζ ρ` where the crosscut meets the boundary
circle, and closing it is not attempted.

## The two arguments

The upper inclusion is the general covering theorem
`TauCeti.exists_mem_frontier_mem_clusterSetOn_of_notMem_image` applied to the crosscut
neighbourhood rather than to the whole disc, plus the observation that the resulting boundary point
cannot lie on the crosscut arc itself. A point `v` of `frontier Ω` is not a value of `f` on the
disc, the image being open; so it is an unattained adherent value of `f` on `ball c r ∩ ball ζ ρ`
and is a cluster value there at some `w ∈ frontier (ball c r ∩ ball ζ ρ)`, hence with
`dist w c ≤ r` and `dist w ζ ≤ ρ`. Were `dist w c < r`, the cluster set of `f` on the *whole* disc
at `w` would be the single value `f w`, by continuity at an interior point, and `v = f w` would be
attained after all. So `dist w c = r`.

The lower inclusion is the locality of the cluster set
(`TauCeti.clusterSetOn_inter_of_mem_nhdsWithin`, added for this purpose in
`TauCeti/Topology/ClusterSet.lean`): at a `w` in the **open** ball `ball ζ ρ` the approach region
`ball c r` may be replaced by `ball c r ∩ ball ζ ρ` without changing the cluster set, so every
cluster value there is adherent to `A`; it lies on `frontier Ω` by
`TauCeti.clusterSetOn_subset_frontier_image` and so is not in `A ⊆ Ω`, which puts it on
`frontier A`. This is where the openness of `ball ζ ρ` is used, and it is why the reverse inclusion
is stated with the open ball.

## What this supplies, and what it deliberately does not

`Conformal/CutDiameter.lean` reduces a boundary limit for `f` to a family of bounded sets `E`, one
per tolerance, enclosing the cut-off piece and small together with the image crosscut. The two
inclusions say what such an `E` has to enclose, in terms of the boundary cluster sets of `f`: at
least those over the open cut-off arc, at most those over the closed one.

They do **not** let `E` be *taken* to be those cluster sets. The lower inclusion at `w = ζ` —
`TauCeti.clusterSetOn_subset_frontier_image_inter_frontier_image` — says the cut-off piece always
contains `clusterSetOn f (ball c r) ζ` outright, so a bounded `E` enclosing it and of diameter at
most `ε` for every `ε` forces `clusterSetOn f (ball c r) ζ` to be a subsingleton on the spot. Any
criterion whose hypothesis bounds the diameter of the cluster sets themselves therefore already
contains its own conclusion, and no such criterion is stated here. What makes
`Conformal/CutDiameter.lean`'s criteria substantive is precisely that `E` is *not* required to be
a cluster set: it is to be produced from the geometry of `∂Ω`, by local connectedness, which is
the ingredient this file does not supply and the Carathéodory milestone still waits on.

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0–L6, everything below is stated for maps of `ℂ`; the locality of
the cluster set it runs on is stated for arbitrary topological spaces.

## Main results

* `TauCeti.exists_mem_sphere_inter_closedBall_mem_clusterSetOn` — an unattained value adherent to
  the image of a crosscut neighbourhood is a cluster value at a point of the boundary circle that
  the crosscut cuts off.
* `TauCeti.frontier_image_inter_closure_image_subset_biUnion_clusterSetOn` and
  `TauCeti.frontier_image_inter_frontier_image_subset_biUnion_clusterSetOn` — the conformal form:
  the piece of `∂Ω` cut off is covered by the cluster sets over the cut-off arc.
* `TauCeti.biUnion_clusterSetOn_subset_frontier_image_inter_frontier_image` — the reverse
  inclusion, over the open arc.
* `TauCeti.clusterSetOn_subset_frontier_image_inter_frontier_image` — its case `w = ζ`: the cut-off
  piece always contains the cluster set at `ζ`, whatever the crosscut radius.

## Coordination with upstream Mathlib

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself, and
Mathlib has no boundary correspondence for conformal maps. So this file is new Lean formalization
rather than a temporary shim. It consumes the L0–L3 shim
`TauCeti.isOpen_image_of_differentiableOn_of_injOn`, to be refactored onto Mathlib's open mapping
API once the upstream work lands.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* E. F. Collingwood and A. J. Lohwater, *The Theory of Cluster Sets*, Ch. 1.
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2–2.3.
-/

public section

namespace TauCeti

open Bornology Complex Filter Metric Set Topology

variable {f : ℂ → ℂ} {c ζ v : ℂ} {r ρ : ℝ}

/-! ## The cut-off piece is covered by cluster sets over the cut-off arc -/

/-- **An unattained value adherent to the image of a crosscut neighbourhood is a boundary cluster
value on the arc the crosscut cuts off.** If `v` is adherent to `f '' (ball c r ∩ ball ζ ρ)` but is
not a value of `f` on `ball c r`, then `v` is a cluster value of `f` on the disc at some point of
`sphere c r ∩ closedBall ζ ρ`.

This is `TauCeti.exists_mem_frontier_mem_clusterSetOn_of_notMem_image` applied to the crosscut
neighbourhood: it produces a witness `w` on `frontier (ball c r ∩ ball ζ ρ)`, which lies in
`closedBall c r ∩ closedBall ζ ρ`, and enlarging the approach region back to the disc keeps `v` a
cluster value. The witness cannot be interior to the disc, since there the cluster set of `f` on
the disc is the single value `f w`, which `v` is assumed not to be; so `dist w c = r`.

Only continuity of `f` is used — holomorphy enters in the corollaries below, and only to know that
the image is open, which is what makes a frontier point of the image unattained. -/
theorem exists_mem_sphere_inter_closedBall_mem_clusterSetOn (hfc : ContinuousOn f (ball c r))
    (hvn : v ∉ f '' ball c r) (hv : v ∈ closure (f '' (ball c r ∩ ball ζ ρ))) :
    ∃ w ∈ sphere c r ∩ closedBall ζ ρ, v ∈ clusterSetOn f (ball c r) w := by
  obtain ⟨w, hw, hvw⟩ := exists_mem_frontier_mem_clusterSetOn_of_notMem_image
    (isBounded_ball.subset inter_subset_left).isCompact_closure (hfc.mono inter_subset_left) hv
    fun hmem => hvn (image_mono inter_subset_left hmem)
  have hvw' : v ∈ clusterSetOn f (ball c r) w := clusterSetOn_mono inter_subset_left hvw
  have hwcl : w ∈ closedBall c r ∩ closedBall ζ ρ :=
    closure_minimal (inter_subset_inter ball_subset_closedBall ball_subset_closedBall)
      (isClosed_closedBall.inter isClosed_closedBall) (frontier_subset_closure hw)
  refine ⟨w, ⟨?_, hwcl.2⟩, hvw'⟩
  rcases (mem_closedBall.mp hwcl.1).lt_or_eq with hlt | heq
  · -- An interior witness would make `v` the attained value `f w`.
    have hwmem : w ∈ ball c r := mem_ball.mpr hlt
    rw [clusterSetOn_eq_singleton_of_continuousWithinAt hwmem (hfc w hwmem),
      mem_singleton_iff] at hvw'
    exact absurd (hvw' ▸ mem_image_of_mem f hwmem) hvn
  · exact mem_sphere.mpr heq

/-- **The piece of the image boundary clinging to a crosscut neighbourhood is covered by the cluster
sets over the cut-off arc.** For `f` holomorphic and injective on `ball c r`, every point of
`frontier (f '' ball c r)` adherent to `f '' (ball c r ∩ ball ζ ρ)` is a boundary cluster value of
`f` at a point of `sphere c r ∩ closedBall ζ ρ`.

Conformality is used only through
`TauCeti.isOpen_image_of_differentiableOn_of_injOn`: the image being open, a point of its frontier
is not one of its values, which is the hypothesis
`TauCeti.exists_mem_sphere_inter_closedBall_mem_clusterSetOn` needs. -/
theorem frontier_image_inter_closure_image_subset_biUnion_clusterSetOn
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r)) :
    frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ ball ζ ρ))
      ⊆ ⋃ w ∈ sphere c r ∩ closedBall ζ ρ, clusterSetOn f (ball c r) w := by
  intro v hv
  have hvn : v ∉ f '' ball c r := by
    rw [(isOpen_image_of_differentiableOn_of_injOn isOpen_ball hd hinj).frontier_eq] at hv
    exact hv.1.2
  obtain ⟨w, hw, hvw⟩ :=
    exists_mem_sphere_inter_closedBall_mem_clusterSetOn hd.continuousOn hvn hv.2
  exact mem_biUnion hw hvw

/-- **The cut-off piece is covered by the cluster sets over the cut-off arc.** The form
`Conformal/CutDiameter.lean` consumes: the set
`frontier (f '' ball c r) ∩ frontier (f '' (ball c r ∩ ball ζ ρ))` whose smallness that file asks
for is enclosed in the union of the boundary cluster sets over `sphere c r ∩ closedBall ζ ρ`.

Immediate from `TauCeti.frontier_image_inter_closure_image_subset_biUnion_clusterSetOn`, a frontier
being contained in a closure. -/
theorem frontier_image_inter_frontier_image_subset_biUnion_clusterSetOn
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r)) :
    frontier (f '' ball c r) ∩ frontier (f '' (ball c r ∩ ball ζ ρ))
      ⊆ ⋃ w ∈ sphere c r ∩ closedBall ζ ρ, clusterSetOn f (ball c r) w :=
  (inter_subset_inter_right _ frontier_subset_closure).trans
    (frontier_image_inter_closure_image_subset_biUnion_clusterSetOn hd hinj)

/-- **The cluster sets over any set of points are bounded when the image is.** Each of them lies in
`closure (f '' ball c r)` by `TauCeti.clusterSetOn_subset_closure_image`, so this is boundedness of
the closure of a bounded set.

Recorded because any statement measuring the covering above by its diameter needs it: `Metric.diam`
vanishes on unbounded sets, so a diameter bound on a set not known to be bounded is no bound at
all. -/
theorem isBounded_biUnion_clusterSetOn (hb : IsBounded (f '' ball c r)) (s : Set ℂ) :
    IsBounded (⋃ w ∈ s, clusterSetOn f (ball c r) w) :=
  hb.closure.subset (iUnion₂_subset fun _ _ => clusterSetOn_subset_closure_image)

/-! ## The reverse inclusion -/

/-- **Every cluster value over the open cut-off arc lies on the cut-off piece.** For `f`
holomorphic and injective on `ball c r` and `w` on `sphere c r ∩ ball ζ ρ`, each cluster value of
`f` at `w` lies both on `frontier (f '' ball c r)` and on
`frontier (f '' (ball c r ∩ ball ζ ρ))`.

The first is `TauCeti.clusterSetOn_subset_frontier_image`, `sphere c r` being the frontier of the
disc. For the second, `ball ζ ρ` is a neighbourhood of `w`, so
`TauCeti.clusterSetOn_inter_of_mem_nhdsWithin` lets the approach region be cut down to the crosscut
neighbourhood: the cluster value is then adherent to its image, and it is not *in* that image,
being a frontier point of the larger open set `f '' ball c r`.

Together with `TauCeti.frontier_image_inter_frontier_image_subset_biUnion_clusterSetOn` this pins
the cut-off piece down between the cluster sets over the open arc and those over the closed arc;
the two differ only over `sphere c r ∩ sphere ζ ρ`, the endpoints of the crosscut. The open ball is
essential here: at an endpoint the approach region cannot be cut down, since points of the disc
near it need not lie in `ball ζ ρ`. -/
theorem biUnion_clusterSetOn_subset_frontier_image_inter_frontier_image (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r)) :
    (⋃ w ∈ sphere c r ∩ ball ζ ρ, clusterSetOn f (ball c r) w)
      ⊆ frontier (f '' ball c r) ∩ frontier (f '' (ball c r ∩ ball ζ ρ)) := by
  refine iUnion₂_subset fun w hw v hv => ?_
  have hwf : w ∈ frontier (ball c r) := by rw [frontier_ball c hr.ne']; exact hw.1
  have hvfr : v ∈ frontier (f '' ball c r) :=
    clusterSetOn_subset_frontier_image isOpen_ball hd hinj hwf hv
  refine ⟨hvfr, ?_⟩
  have hnhds : ball ζ ρ ∈ 𝓝[ball c r] w :=
    nhdsWithin_le_nhds (isOpen_ball.mem_nhds hw.2)
  rw [← clusterSetOn_inter_of_mem_nhdsWithin hnhds] at hv
  have hvn : v ∉ f '' (ball c r ∩ ball ζ ρ) := by
    rw [(isOpen_image_of_differentiableOn_of_injOn isOpen_ball hd hinj).frontier_eq] at hvfr
    exact fun hmem => hvfr.2 (image_mono inter_subset_left hmem)
  exact ⟨clusterSetOn_subset_closure_image hv, fun hint => hvn (interior_subset hint)⟩

/-- **A cluster value at a boundary point lies on the piece every crosscut at that point cuts
off.** The case `w = ζ` of
`TauCeti.biUnion_clusterSetOn_subset_frontier_image_inter_frontier_image`, recorded because it is
what fixes the standing of the cut-off piece: *any* set enclosing it, at any crosscut radius,
already contains the whole cluster set of `f` at `ζ`. So the enclosing set `E` of
`Conformal/CutDiameter.lean` cannot be taken to be the cluster sets over the cut-off arc — that
would put the conclusion of those criteria into their hypothesis — and has to come from geometry of
`∂Ω`, which is what local connectedness supplies. -/
theorem clusterSetOn_subset_frontier_image_inter_frontier_image (hr : 0 < r) (hρ : 0 < ρ)
    (hζ : ζ ∈ sphere c r) (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r)) :
    clusterSetOn f (ball c r) ζ
      ⊆ frontier (f '' ball c r) ∩ frontier (f '' (ball c r ∩ ball ζ ρ)) :=
  fun _ hv => biUnion_clusterSetOn_subset_frontier_image_inter_frontier_image hr hd hinj
    (mem_biUnion ⟨hζ, mem_ball_self hρ⟩ hv)

end TauCeti
