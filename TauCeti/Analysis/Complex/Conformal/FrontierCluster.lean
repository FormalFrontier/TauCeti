/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.ClusterSet
import TauCeti.Analysis.Complex.Conformal.CutDiameter

/-!
# The converse of the crosscut criterion

`Conformal/CutDiameter.lean` reduces a boundary limit for a conformal map `f` on `ball c r` to a
family of bounded enclosing sets, one per tolerance: at every boundary point `ζ` and every `ε > 0`
a crosscut radius `ρ` and a bounded `E` enclosing the *cut-off piece*
`frontier (f '' ball c r) ∩ frontier (f '' (ball c r ∩ ball ζ ρ))` with
`diam (f '' (ball c r ∩ sphere ζ ρ) ∪ E) ≤ ε`. That gives a continuous extension of `f` to the
closed disc (`TauCeti.exists_continuousOn_closure_eqOn_of_forall_exists_diam_union_le`), and it is
stated in that direction only. This file proves the converse, so that the criterion
**characterizes** continuous extendability:

> `(∀ w ∈ sphere c r, ∀ ε > 0, ∃ ρ > 0, ∃ E, …) ↔ ∃ F, ContinuousOn F (closedBall c r) ∧`
> `EqOn F f (ball c r)`

(`TauCeti.forall_exists_diam_union_le_iff_exists_continuousOn_closedBall_eqOn`). The criterion is
therefore not stronger than the conclusion it is aimed at: the enclosing sets the remaining
Carathéodory geometry has to produce are asked for by a condition the sought extension itself
satisfies.

## The covering step

The converse is not immediate, because the cut-off piece is described by the *image of the crosscut
neighbourhood* and not by boundary data of `f` at all, while a continuous extension `F` controls
only the boundary behaviour: at a boundary point `w` it makes the cluster set
`clusterSetOn f (ball c r) w` the single value `F w`. What bridges the two is the covering of the
cut-off piece by the boundary cluster sets over the arc the crosscut cuts off:

> `frontier (f '' ball c r) ∩ frontier (f '' (ball c r ∩ ball ζ ρ)) ⊆`
> `⋃ w ∈ sphere c r ∩ closedBall ζ ρ, clusterSetOn f (ball c r) w`

(`TauCeti.frontier_image_inter_frontier_image_subset_biUnion_clusterSetOn`). It localizes the global
covering of `Conformal/ClusterSet.lean` — `⋃ w ∈ frontier U, clusterSetOn f U w =
frontier (f '' U)` (`TauCeti.biUnion_clusterSetOn_eq_frontier_image`), which says nothing about
*which* boundary points of the image are reached from a given part of `frontier U`. With it, a small
closed ball around `F ζ` is an admissible `E` at every tolerance
(`TauCeti.exists_diam_union_le_of_continuousOn_closedBall_eqOn`).

The covering itself is the general covering theorem
`TauCeti.exists_mem_frontier_mem_clusterSetOn_of_notMem_image` applied to the crosscut
neighbourhood rather than to the whole disc, plus the observation that the resulting boundary point
cannot lie inside the disc. A point `v` of `frontier (f '' ball c r)` is not a value of `f` on the
disc, the image being open; so it is an unattained adherent value of `f` on `ball c r ∩ ball ζ ρ`
and is a cluster value there at some `w ∈ frontier (ball c r ∩ ball ζ ρ)`, hence with
`dist w c ≤ r` and `dist w ζ ≤ ρ`. Were `dist w c < r`, the cluster set of `f` on the *whole* disc
at `w` would be the single value `f w`, by continuity at an interior point, and `v = f w` would be
attained after all. So `dist w c = r`.

The crosscut picture is how the covering is meant to be read, not a hypothesis it imposes: it holds
for an arbitrary cutting centre `ζ` and radius `ρ`. It is only in the configuration the picture
describes — `ζ ∈ sphere c r` and `0 < ρ < 2 * r`, so that the two circles genuinely cross — that
`sphere c r ∩ closedBall ζ ρ` is the arc of the boundary circle that a crosscut cuts off, together
with the two points where it meets that circle.

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0–L6, everything below is stated for maps of `ℂ`.

## Main results

* `TauCeti.exists_mem_sphere_inter_closedBall_mem_clusterSetOn` — an unattained value adherent to
  the image of a crosscut neighbourhood is a cluster value at a point of the boundary circle that
  the crosscut cuts off.
* `TauCeti.frontier_image_inter_closure_image_subset_biUnion_clusterSetOn` and
  `TauCeti.frontier_image_inter_frontier_image_subset_biUnion_clusterSetOn` — the conformal form:
  the piece of the image boundary cut off is covered by the cluster sets over the cut-off arc.
* `TauCeti.exists_diam_union_le_of_continuousOn_closedBall_eqOn` and
  `TauCeti.forall_exists_diam_union_le_iff_exists_continuousOn_closedBall_eqOn` — a conformal map
  that extends continuously to the closed disc satisfies the crosscut criterion of
  `Conformal/CutDiameter.lean` at every boundary point, so that criterion characterizes continuous
  extendability.

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

open Complex Filter Metric Set Topology

variable {f F : ℂ → ℂ} {c ζ v : ℂ} {r ρ : ℝ}

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

/-! ## The crosscut criterion is exactly continuous extendability -/

/-- **A conformal map extending continuously to the closed disc cuts off small pieces at every
boundary point.** If `f` agrees on `ball c r` with a map `F` continuous on `closedBall c r`, then
at each `ζ` on the boundary circle and each `ε > 0` there is a crosscut radius `ρ > 0` and a bounded
set `E` enclosing the cut-off piece with `diam (f '' (ball c r ∩ sphere ζ ρ) ∪ E) ≤ ε` — the
hypothesis of `TauCeti.subsingleton_clusterSetOn_of_forall_exists_diam_union_le`, satisfied with
`E` a small closed ball around `F ζ`.

This is where `TauCeti.frontier_image_inter_frontier_image_subset_biUnion_clusterSetOn` does its
work: continuity of `F` bounds the *cluster sets* over the cut-off arc, each of them being the
single value `F w`, and the covering is what transfers that bound to the cut-off piece, which is
otherwise described by the image of the crosscut neighbourhood and not by boundary data of `f` at
all. -/
theorem exists_diam_union_le_of_continuousOn_closedBall_eqOn (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hFc : ContinuousOn F (closedBall c r)) (hFf : EqOn F f (ball c r)) (hζ : ζ ∈ sphere c r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∃ E : Set ℂ, Bornology.IsBounded E ∧
      frontier (f '' ball c r) ∩ frontier (f '' (ball c r ∩ ball ζ ρ)) ⊆ E ∧
      diam (f '' (ball c r ∩ sphere ζ ρ) ∪ E) ≤ ε := by
  obtain ⟨δ, hδ, hδF⟩ :=
    Metric.continuousWithinAt_iff.mp (hFc ζ (sphere_subset_closedBall hζ)) (ε / 2) (by linarith)
  -- At a point of the closed disc within `δ / 2` of `ζ` the extension is within `ε / 2` of `F ζ`.
  have hnear : ∀ u ∈ closedBall c r, dist u ζ ≤ δ / 2 → F u ∈ closedBall (F ζ) (ε / 2) :=
    fun u hu hdu => mem_closedBall.mpr (hδF hu (by linarith)).le
  -- On the boundary circle the cluster set of `f` is the single value of the extension.
  have hcl : ∀ u ∈ closedBall c r, clusterSetOn f (ball c r) u = {F u} := fun u hu =>
    clusterSetOn_eq_singleton_of_tendsto (by rwa [closure_ball c hr.ne'])
      (Filter.Tendsto.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin hFf)
        ((hFc u hu).mono ball_subset_closedBall))
  refine ⟨δ / 2, by linarith, closedBall (F ζ) (ε / 2), isBounded_closedBall, fun p hp => ?_, ?_⟩
  · obtain ⟨u, hu, hpu⟩ := mem_iUnion₂.mp
      (frontier_image_inter_frontier_image_subset_biUnion_clusterSetOn hd hinj hp)
    have hucl : u ∈ closedBall c r := sphere_subset_closedBall hu.1
    rw [hcl u hucl, mem_singleton_iff] at hpu
    subst hpu
    exact hnear u hucl (mem_closedBall.mp hu.2)
  · have hsub : f '' (ball c r ∩ sphere ζ (δ / 2)) ∪ closedBall (F ζ) (ε / 2)
        ⊆ closedBall (F ζ) (ε / 2) := by
      refine union_subset (fun p hp => ?_) Subset.rfl
      obtain ⟨x, ⟨hx, hxs⟩, rfl⟩ := hp
      have hxc := hnear x (ball_subset_closedBall hx) (mem_sphere.mp hxs).le
      rwa [hFf hx] at hxc
    refine (diam_mono hsub isBounded_closedBall).trans
      ((diam_closedBall (by linarith)).trans ?_)
    linarith

/-- **The crosscut criterion characterizes continuous extendability.** For `f` holomorphic and
injective on `ball c r` with bounded image, the hypothesis of
`TauCeti.exists_continuousOn_closure_eqOn_of_forall_exists_diam_union_le`, read on the disc — at
every boundary point and every tolerance, a crosscut radius and a bounded set enclosing the cut-off
piece, small together with the image crosscut — holds **exactly** when `f` extends continuously to
the closed disc.

The forward direction is that criterion; the converse is
`TauCeti.exists_diam_union_le_of_continuousOn_closedBall_eqOn`. So the criterion is not stronger
than the conclusion it is aimed at, and the remaining geometric work for the Carathéodory boundary
correspondence — producing the enclosing sets `E` from local connectedness of `∂Ω` — is aimed at a
condition that the desired extension itself satisfies. -/
theorem forall_exists_diam_union_le_iff_exists_continuousOn_closedBall_eqOn (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : Bornology.IsBounded (f '' ball c r)) :
    (∀ w ∈ sphere c r, ∀ ε > 0, ∃ ρ > 0, ∃ E : Set ℂ, Bornology.IsBounded E ∧
        frontier (f '' ball c r) ∩ frontier (f '' (ball c r ∩ ball w ρ)) ⊆ E ∧
        diam (f '' (ball c r ∩ sphere w ρ) ∪ E) ≤ ε) ↔
      ∃ F : ℂ → ℂ, ContinuousOn F (closedBall c r) ∧ EqOn F f (ball c r) := by
  refine ⟨fun h => ?_, fun ⟨_, hFc, hFf⟩ _ hw _ hε =>
    exists_diam_union_le_of_continuousOn_closedBall_eqOn hr hd hinj hFc hFf hw hε⟩
  obtain ⟨F, hFc, hFf⟩ :=
    exists_continuousOn_closure_eqOn_of_forall_exists_diam_union_le isOpen_ball hd hinj hb
      fun w hw => h w (by rwa [frontier_ball c hr.ne'] at hw)
  exact ⟨F, closure_ball c hr.ne' ▸ hFc, hFf⟩

end TauCeti
