/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.BoundaryCorrespondence
public import TauCeti.Topology.ClusterSet
public import TauCeti.Topology.JordanCurve.Subcontinuum
import TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected
import TauCeti.Analysis.Convex.ClusterSet
import TauCeti.Topology.Frontier

/-!
# The boundary cluster set of a conformal map

The cluster set `TauCeti.clusterSetOn f U w` of a map `f` on `U` at a point `w`, and the criterion
`TauCeti.exists_continuousOn_closure_eqOn` turning subsingleton boundary cluster sets into a
continuous extension, use nothing about conformality and live in `TauCeti/Topology/ClusterSet.lean`:
the cluster set is defined over an arbitrary pair of topological spaces, and the criterion is a
compactness statement, holding for any map of a `T3` codomain taking its values in a compact set —
a bounded-image map into a proper metric space being the special case
`TauCeti.exists_continuousOn_closure_eqOn_of_isBounded`. This file adds what conformality
contributes.

`Conformal/BoundaryCorrespondence.lean` proves what a conformal map does *given* a continuous
extension to the closure. This file supplies the missing half of that interface: it removes the
extension from the hypotheses.

* **Unconditionally, the boundary cluster set of a conformal map lies on the frontier of the
  image.** This is the extension-free form of `TauCeti.notMem_image_of_mem_frontier`: no continuous
  extension is assumed, and the conclusion is about *every* cluster value. The mechanism is the
  properness of a conformal map, exactly as there — a cluster value inside the open set `f '' U`
  would be approached frequently inside a compact subset of `f '' U` that properness says `f`
  leaves eventually.
* **An extension injective on the frontier is injective on the closure.** This supplies the
  injectivity hypothesis of `TauCeti.closureHomeomorph`, reducing it to a condition on the boundary
  alone, because the boundary values have just been shown to avoid the image.
* **Conversely, the boundary cluster sets exhaust the frontier of the image**, for a bounded
  domain: no boundary point of `f '' U` is missed. This is the surjectivity of the boundary
  correspondence, and it is what makes the inclusion of the first item an equality.
* **Relatively: the boundary piece a subdomain clings to is the union of its own boundary cluster
  sets.** For any `V ⊆ U` with compact closure,
  `frontier (f '' U) ∩ frontier (f '' V) = ⋃ e ∈ frontier U ∩ closure V, clusterSetOn f V e`, the
  cluster sets being taken *along `V`*. The previous item is the case `V = U`. The point of the
  relative form is that `V` may be shrunk: taking `V` to be the ball neighbourhood
  `U ∩ ball w ρ` of a boundary point identifies the boundary piece that neighbourhood clings to —
  the piece the circle `sphere w ρ` cuts off, in the case where `U ∩ sphere w ρ` is a crosscut —
  and letting `ρ` fall shrinks those pieces exactly to `clusterSetOn f U w`.

A third ingredient is again not about conformality and is proved upstream, in
`TauCeti/Analysis/Convex/ClusterSet.lean`: on a **convex** domain — the unit disc, in the
Riemann-mapping application — the cluster set of a continuous map with bounded image is a
*continuum*, by `TauCeti.isConnected_clusterSetOn_of_convex_of_isBounded`. Combining it with the
first item above, the boundary cluster set of a conformal map of the disc onto a bounded region is
a nonempty compact connected subset of the frontier of the image, and Carathéodory's theorem is
exactly the assertion that this continuum degenerates to a point.

Together with the extension criterion these are the two halves of the vocabulary that layer **L5**
of the conformal-mapping roadmap — Carathéodory's boundary correspondence — is stated in.
Carathéodory's theorem asserts that for a Riemann map of a Jordan domain every boundary cluster set
is a singleton; feeding that into `TauCeti.exists_continuousOn_closure_eqOn` gives a continuous
extension to `closure U`, and upgrading it to a homeomorphism of closures needs one further input,
namely injectivity of the extension on `frontier U`, which `TauCeti.injOn_closure_of_injOn_frontier`
then propagates to `closure U` for `TauCeti.closureHomeomorph`. Boundary injectivity is not proved
here, and neither is the singleton property — but the last section reduces it.

The relative form is what connects that vocabulary to the *geometric* criterion of
`Conformal/CutDiameter.lean`. There,
`TauCeti.exists_continuousOn_closure_eqOn_of_forall_exists_diam_union_le` produces the continuous
extension from a bound on the diameter of `f '' (U ∩ sphere w ρ)` together with a bounded set
enclosing `frontier (f '' U) ∩ frontier (f '' (U ∩ ball w ρ))`. The first of those two data is what
the length–area method of `Conformal/LengthArea.lean` supplies; the second is the input still
missing at layer L5, and what the relative form does is *name* it — as a union of cluster sets over
the boundary points of `U` inside the closed disc — and show that these sets are precisely what the
cluster set at `w` is the limit of. No estimate on them is claimed here.

## The singleton property on a Jordan image boundary

For a **convex** domain the three facts above compose into a structural description of the boundary
cluster set. It is compact, it is a continuum, and it lies on `frontier (f '' U)`; so if that
frontier is a Jordan curve — the Carathéodory hypothesis — the cluster set is a *compact connected
subset of a Jordan curve*, and `TauCeti/Topology/JordanCurve/Subcontinuum.lean` classifies those:
each is a point, an arc, or the whole curve. That is
`TauCeti.subsingleton_or_exists_injective_path_clusterSetOn`.

The classification comes with a criterion excluding the two nondegenerate cases at once: a compact
connected subset of a Jordan curve that is *nowhere dense* in it — every point of it adherent to the
rest of the curve — is a subsingleton, so a single point for a cluster set, which is nonempty.
Feeding that criterion to the extension theorem
`TauCeti.exists_continuousOn_closure_eqOn_of_isBounded` gives
`TauCeti.exists_continuousOn_closure_eqOn_of_forall_subset_closure_sdiff`: **a conformal map of a
convex domain onto a bounded region with Jordan boundary, none of whose boundary cluster sets has
interior in that boundary curve, extends continuously to the closure.** The hypothesis is not a
property of the curve on its own: `clusterSetOn f U w` depends on the map, the domain and the
boundary point, and what is asked of it is *relative nowhere density* — each of those cluster sets,
one for every `w ∈ frontier U`, is to be nowhere dense in the curve. What the criterion does is
trade the analytic content of the milestone for that purely topological condition on where the
cluster sets sit; what it does not do is *verify* the condition for a Riemann map, which the
crosscut and length–area files are aimed at. The L5 milestone is now complete via
`Conformal/Jordan/Approach.lean`, which takes the Janiszewski route (preconnected approach
regions) rather than verifying the nowhere-density condition directly.

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0–L6, the results below are stated for maps of `ℂ`, as in
`Conformal/BoundaryCorrespondence.lean`.

## Main results

* `TauCeti.notMem_image_of_mem_clusterSetOn` and `TauCeti.clusterSetOn_subset_frontier_image` — a
  boundary cluster value of a conformal map lies on the frontier of the image.
* `TauCeti.injOn_closure_of_injOn_frontier` — an extension injective on the frontier is injective
  on the closure.
* `TauCeti.exists_mem_frontier_mem_clusterSetOn` and
  `TauCeti.biUnion_clusterSetOn_eq_frontier_image` — **the boundary correspondence is onto**: on a
  bounded domain the boundary cluster sets cover, hence exactly exhaust, the frontier of the image.
  The case a Riemann map presents is the unit disc, where `frontier_ball` rewrites `frontier U` to
  the unit circle.
* `TauCeti.frontier_inter_closure_image_eq_biUnion_clusterSetOn` and
  `TauCeti.frontier_inter_frontier_image_eq_biUnion_clusterSetOn` — **the relative form**: the
  boundary piece a subdomain `V ⊆ U` clings to is the union of the cluster sets along `V` over the
  boundary points of `U` adherent to `V`, whether that piece is read off `closure (f '' V)` or off
  `frontier (f '' V)`.
* `TauCeti.frontier_inter_frontier_image_inter_ball_eq_biUnion_clusterSetOn` and
  `TauCeti.iInter_frontier_inter_frontier_image_inter_ball_eq_clusterSetOn` — **the boundary piece
  at a point**: its identification for the ball neighbourhood `U ∩ ball w ρ`, and the fact that
  these pieces shrink, as `ρ` falls, exactly to `clusterSetOn f U w`.
* `TauCeti.subsingleton_or_exists_injective_path_clusterSetOn` — on a convex domain whose image has
  Jordan frontier, a boundary cluster set other than the whole frontier is a point or an arc.
* `TauCeti.subsingleton_clusterSetOn_of_subset_closure_sdiff` — such a cluster set that is nowhere
  dense in the frontier is a single point.
* `TauCeti.exists_continuousOn_closure_eqOn_of_forall_subset_closure_sdiff` — **a nowhere-density
  criterion for the Carathéodory extension**: if no boundary cluster set has interior in the Jordan
  frontier of the image, the map extends continuously to `closure U`.

## Coordination with upstream Mathlib

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself, and
Mathlib has no boundary correspondence for conformal maps. So this file is new Lean formalization
rather than a temporary shim. It consumes the L0–L3 shim
`TauCeti.isOpen_image_of_differentiableOn_of_injOn` through
`Conformal/BoundaryCorrespondence.lean`, to be refactored onto Mathlib once the upstream work
lands.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* E. F. Collingwood and A. J. Lohwater, *The Theory of Cluster Sets*, Ch. 1.
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
-/

public section

namespace TauCeti

open Filter Metric Set Topology

variable {U : Set ℂ} {f F : ℂ → ℂ} {v w : ℂ}

/-- **A boundary cluster value of a conformal map is not attained.** If `f` is holomorphic and
injective on an open `U` and `w` is a boundary point of `U`, then no value approached by `f` near
`w` lies in `f '' U`.

This is `TauCeti.notMem_image_of_mem_frontier` with the continuous extension removed from the
hypotheses: there, the boundary value is `F w` for a given extension `F`; here it is an arbitrary
cluster value, and the same properness argument applies. A cluster value inside the *open* set
`f '' U` would be approached frequently inside a compact ball contained in `f '' U`, which
properness says `f` leaves eventually along `𝓝[U] w`. -/
theorem notMem_image_of_mem_clusterSetOn (hUo : IsOpen U) (hfd : DifferentiableOn ℂ f U)
    (hfi : InjOn f U) (hw : w ∈ frontier U) (hv : v ∈ clusterSetOn f U w) : v ∉ f '' U := by
  intro hmem
  have hVo : IsOpen (f '' U) := isOpen_image_of_differentiableOn_of_injOn hUo hfd hfi
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hVo _ hmem
  have hwU : w ∉ U := (hUo.frontier_eq.subset hw).2
  have hlim : Tendsto (fun z : ℂ => z) (𝓝[U] w) (𝓝 w) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hesc : ∀ᶠ z in 𝓝[U] w, f z ∉ closedBall v (δ / 2) :=
    eventually_notMem_of_tendsto_of_notMem hUo hfd hfi self_mem_nhdsWithin hlim hwU
      (isCompact_closedBall _ _) ((closedBall_subset_ball (by linarith)).trans hball)
  have hfreq : ∃ᶠ z in 𝓝[U] w, f z ∈ closedBall v (δ / 2) :=
    mem_clusterSetOn_iff_frequently.mp hv _ (closedBall_mem_nhds v (by linarith))
  obtain ⟨z, hz1, hz2⟩ := (hfreq.and_eventually hesc).exists
  exact hz2 hz1

/-- **The boundary cluster set of a conformal map lies on the frontier of the image.** Combining
`TauCeti.clusterSetOn_subset_closure_image` with `TauCeti.notMem_image_of_mem_clusterSetOn`:
cluster values are limits of image points, and the image is open, so its frontier is
`closure (f '' U) \ f '' U`. -/
theorem clusterSetOn_subset_frontier_image (hUo : IsOpen U) (hfd : DifferentiableOn ℂ f U)
    (hfi : InjOn f U) (hw : w ∈ frontier U) :
    clusterSetOn f U w ⊆ frontier (f '' U) := by
  intro v hv
  rw [(isOpen_image_of_differentiableOn_of_injOn hUo hfd hfi).frontier_eq]
  exact ⟨clusterSetOn_subset_closure_image hv, notMem_image_of_mem_clusterSetOn hUo hfd hfi hw hv⟩

/-- **An extension injective on the frontier is injective on the closure.** For a conformal `f` on
an open `U`, a continuous extension `F` to `closure U` that is injective on `frontier U` is
injective on all of `closure U`.

The two halves of `closure U = U ∪ frontier U` cannot interfere: on `U` the map is the injective
`f`, on `frontier U` it is injective by hypothesis, and a boundary value lies outside `f '' U` by
`TauCeti.notMem_image_of_mem_frontier`. This supplies the injectivity hypothesis of
`TauCeti.closureHomeomorph`, reducing it to a condition on the boundary alone. -/
theorem injOn_closure_of_injOn_frontier (hUo : IsOpen U) (hfd : DifferentiableOn ℂ f U)
    (hfi : InjOn f U) (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U)
    (hFfr : InjOn F (frontier U)) : InjOn F (closure U) := by
  have hsplit : ∀ z ∈ closure U, z ∈ U ∨ z ∈ frontier U := by
    intro z hz
    by_cases hzU : z ∈ U
    · exact Or.inl hzU
    · exact Or.inr (by rw [hUo.frontier_eq]; exact ⟨hz, hzU⟩)
  have hout : ∀ z ∈ frontier U, F z ∉ f '' U := fun z hz =>
    notMem_image_of_mem_frontier hUo hfd hfi hFc hFf hz
  intro a ha b hb hab
  rcases hsplit a ha with haU | haF <;> rcases hsplit b hb with hbU | hbF
  · refine hfi haU hbU ?_
    rw [← hFf haU, ← hFf hbU]
    exact hab
  · refine absurd ?_ (hout b hbF)
    rw [← hab, hFf haU]
    exact ⟨a, haU, rfl⟩
  · refine absurd ?_ (hout a haF)
    rw [hab, hFf hbU]
    exact ⟨b, hbU, rfl⟩
  · exact hFfr haF hbF hab

/-! ## The boundary correspondence is onto -/

/-- **Every boundary point of the image is a boundary cluster value.** If `f` is holomorphic and
injective on a bounded open `U`, then each point of `frontier (f '' U)` is approached by `f` at some
point of `frontier U`.

All the work is done by the general covering theorem
`TauCeti.exists_mem_frontier_mem_clusterSetOn_of_notMem_image`, which needs only that `closure U` be
compact — here, boundedness of `U` — and that `f` be continuous on `U`. What conformality
contributes is that `f '' U` is *open*, so that `frontier (f '' U)` is `closure (f '' U) \ f '' U`
and the boundary value `v` is an adherent value of the image that is not attained.

This is the converse of `TauCeti.clusterSetOn_subset_frontier_image`, and the two together say that
the boundary correspondence `w ↦ clusterSetOn f U w` is onto `frontier (f '' U)`. Carathéodory's
theorem — layer **L5** of the conformal-mapping roadmap — refines this for a Riemann map of a Jordan
domain by showing each of these cluster sets to be a singleton, which turns the correspondence into
a continuous *map* of `frontier U` onto `frontier (f '' U)`; that this map is moreover *injective*
is a further assertion of Carathéodory's theorem, and does not follow from the singleton property.
The surjectivity below holds with no hypothesis on `frontier U` whatever. -/
theorem exists_mem_frontier_mem_clusterSetOn (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U) (hv : v ∈ frontier (f '' U)) :
    ∃ w ∈ frontier U, v ∈ clusterSetOn f U w := by
  rw [(isOpen_image_of_differentiableOn_of_injOn hUo hfd hfi).frontier_eq] at hv
  exact exists_mem_frontier_mem_clusterSetOn_of_notMem_image hUb.isCompact_closure hfd.continuousOn
    hv.1 hv.2

/-- **The boundary piece a subdomain clings to is the union of its own boundary cluster sets.** For
`f` holomorphic and injective on an open `U` and any `V ⊆ U` with compact closure,

> `frontier (f '' U) ∩ closure (f '' V) = ⋃ e ∈ frontier U ∩ closure V, clusterSetOn f V e`.

So the part of the image boundary that the image of `V` reaches is not merely covered by cluster
sets: it *is* the union of the cluster sets of `f` **along `V`** at the boundary points of `U`
adherent to `V`. Taking `V = U` recovers
`TauCeti.biUnion_clusterSetOn_eq_frontier_image`; the content of the relative form is that shrinking
`V` shrinks both sides in step, which is what makes the boundary piece an object one can estimate.

Both inclusions come from the same source. Closing `f '' V` adds exactly the cluster values along
`V` over `frontier V` (`TauCeti.closure_image_eq_image_union_biUnion_clusterSetOn`, which is why
`closure V` is asked to be compact); a value *taken* on `V` lies in the open set `f '' U`, which is
disjoint from its own frontier, so only cluster values survive on the left; and a cluster value at
a point `e` of `frontier V` lying in `U` would be `f e` by continuity, which is again a taken
value, so the surviving `e` are exactly those outside `U`, that is on `frontier U`. Conversely a
cluster set along `V` at a point of `frontier U` sits inside `clusterSetOn f U e`, hence on
`frontier (f '' U)` by `TauCeti.clusterSetOn_subset_frontier_image`, and inside `closure (f '' V)`
by construction.

Neither `V` nor `U` is asked to be connected, and `V` need not be open. What layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md` consumes are the two sides a circle cuts `U` into:
`V = U ∩ ball ζ ρ`, whose closure is compact for every `U`, lying as it does in `closedBall ζ ρ`,
and `V = U \ closedBall ζ ρ`, for which the compactness hypothesis is a real restriction — it
holds when `U` is bounded, but for unbounded `U` that side has unbounded closure. -/
theorem frontier_inter_closure_image_eq_biUnion_clusterSetOn (hUo : IsOpen U)
    (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U) {V : Set ℂ} (hVU : V ⊆ U)
    (hVc : IsCompact (closure V)) :
    frontier (f '' U) ∩ closure (f '' V) = ⋃ e ∈ frontier U ∩ closure V, clusterSetOn f V e := by
  have hopen : IsOpen (f '' U) := isOpen_image_of_differentiableOn_of_injOn hUo hfd hfi
  refine subset_antisymm ?_ (iUnion₂_subset fun e he => subset_inter
    (fun _ hv => clusterSetOn_subset_frontier_image hUo hfd hfi he.1 (clusterSetOn_mono hVU hv))
    fun _ hv => clusterSetOn_subset_closure_image hv)
  rintro u ⟨hufr, hucl⟩
  have hunot : u ∉ f '' U := fun h =>
    eq_empty_iff_forall_notMem.mp hopen.inter_frontier_eq u ⟨h, hufr⟩
  rw [closure_image_eq_image_union_biUnion_clusterSetOn hVc (hfd.continuousOn.mono hVU)] at hucl
  rcases hucl with hu | hu
  · exact absurd (image_mono hVU hu) hunot
  obtain ⟨e, he, hue⟩ := mem_iUnion₂.mp hu
  have hecl : e ∈ closure V := frontier_subset_closure he
  refine mem_iUnion₂.mpr ⟨e, ⟨?_, hecl⟩, hue⟩
  rw [hUo.frontier_eq]
  refine ⟨closure_mono hVU hecl, fun heU => ?_⟩
  rw [clusterSetOn_eq_singleton_of_tendsto hecl
    ((hfd.differentiableAt (hUo.mem_nhds heU)).continuousAt.continuousWithinAt),
    mem_singleton_iff] at hue
  exact hunot ⟨e, heU, hue.symm⟩

/-- **The boundary piece a subdomain clings to, read on the frontier of its image.** The form of
`TauCeti.frontier_inter_closure_image_eq_biUnion_clusterSetOn` that a domain-splitting estimate
consumes:

> `frontier (f '' U) ∩ frontier (f '' V) = ⋃ e ∈ frontier U ∩ closure V, clusterSetOn f V e`.

The left-hand sides of the two statements agree because `f '' V` lies in the open set `f '' U`, so
the boundary of `f '' U` reaches `closure (f '' V)` only through `frontier (f '' V)` — that is
`TauCeti.frontier_inter_closure_eq_frontier_inter_frontier`, a fact of pure topology.

The distinction matters because the two descriptions arise on opposite sides of the argument. The
cluster-set description is produced by a *limit* argument, which naturally speaks of closures;
`TauCeti.diam_image_inter_ball_le` of `Conformal/CutDiameter.lean` — which bounds the width of one
side of a crosscut by the width of the crosscut together with the boundary piece it cuts off — asks
for the *frontier* form, this being the shape in which the splitting lemma
`TauCeti.frontier_image_subset_image_union_frontier_image` delivers it. -/
theorem frontier_inter_frontier_image_eq_biUnion_clusterSetOn (hUo : IsOpen U)
    (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U) {V : Set ℂ} (hVU : V ⊆ U)
    (hVc : IsCompact (closure V)) :
    frontier (f '' U) ∩ frontier (f '' V) = ⋃ e ∈ frontier U ∩ closure V, clusterSetOn f V e := by
  rw [← frontier_inter_closure_eq_frontier_inter_frontier (image_mono hVU),
    frontier_inter_closure_image_eq_biUnion_clusterSetOn hUo hfd hfi hVU hVc]

/-- **The boundary cluster sets exhaust the frontier of the image.** For a conformal map of a
bounded open set, the union of the cluster sets over `frontier U` is exactly `frontier (f '' U)`.

This is the case `V = U` of `TauCeti.frontier_inter_closure_image_eq_biUnion_clusterSetOn`, where
both intersections collapse: `frontier s ⊆ closure s` on each side. Neither connectedness nor
simple connectedness of `U` is used, and nothing is assumed about `frontier U`. -/
theorem biUnion_clusterSetOn_eq_frontier_image (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U) :
    ⋃ w ∈ frontier U, clusterSetOn f U w = frontier (f '' U) := by
  have h := frontier_inter_closure_image_eq_biUnion_clusterSetOn hUo hfd hfi (subset_refl U)
    hUb.isCompact_closure
  rwa [inter_eq_self_of_subset_left (frontier_subset_closure (s := f '' U)),
    inter_eq_self_of_subset_left (frontier_subset_closure (s := U)), eq_comm] at h

/-! ## The boundary piece at a point -/

/-- **The boundary piece the ball neighbourhood of a point clings to.** The instance of
`TauCeti.frontier_inter_frontier_image_eq_biUnion_clusterSetOn` at `V = U ∩ ball w ρ`, whose closure
is compact because it lies in `closedBall w ρ`:

> `frontier (f '' U) ∩ frontier (f '' (U ∩ ball w ρ))`
> `= ⋃ e ∈ frontier U ∩ closure (U ∩ ball w ρ), clusterSetOn f (U ∩ ball w ρ) e`.

The left-hand side is exactly the set that
`TauCeti.exists_continuousOn_closure_eqOn_of_forall_exists_diam_union_le` of
`Conformal/CutDiameter.lean` asks to be enclosed in a small bounded set: what that criterion
needs made small at each boundary point of `U`, alongside the image of the circle `sphere w ρ`. So
this identifies its second geometric input — the first being the length–area estimate, which makes
the image of that circle short — as a union of cluster sets *along the ball neighbourhood*, indexed
by the boundary points of `U` that the neighbourhood reaches. Nothing here asks `U ∩ sphere w ρ` to
be a crosscut; when it is one, `U ∩ ball w ρ` is the side of that crosscut towards `w` and the set
below is the boundary piece it cuts off.

It is not the middle piece `frontier (f '' U) ∩ closure (f '' (U ∩ sphere w ρ))` of
`Conformal/Crosscut/Image.lean`, which is indexed by the boundary points *on the circle* and is
small as soon as the image of that circle is. The piece here is indexed by the boundary points
*inside* the closed disc, and making it small is the step layer **L5** still lacks. -/
theorem frontier_inter_frontier_image_inter_ball_eq_biUnion_clusterSetOn (hUo : IsOpen U)
    (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U) (w : ℂ) (ρ : ℝ) :
    frontier (f '' U) ∩ frontier (f '' (U ∩ ball w ρ)) =
      ⋃ e ∈ frontier U ∩ closure (U ∩ ball w ρ), clusterSetOn f (U ∩ ball w ρ) e :=
  frontier_inter_frontier_image_eq_biUnion_clusterSetOn hUo hfd hfi inter_subset_left
    ((isCompact_closedBall w ρ).of_isClosed_subset isClosed_closure
      (closure_minimal (inter_subset_right.trans ball_subset_closedBall) isClosed_closedBall))

/-- **The boundary pieces at a point shrink exactly to its cluster set.** At a boundary
point `w` of `U`,

> `⋂ ρ > 0, frontier (f '' U) ∩ frontier (f '' (U ∩ ball w ρ)) = clusterSetOn f U w`.

The pieces decrease as `ρ` does — the ball neighbourhoods are nested, so by
`TauCeti.frontier_inter_closure_eq_frontier_inter_frontier` and monotonicity of `closure` so are the
pieces — and what they decrease to is precisely the set of values `f` approaches at `w`. So
Carathéodory's assertion that a boundary cluster set is a singleton is
equivalent to the boundary pieces at `w` shrinking to a point, which is the form the
crosscut estimates of layer **L5** of `TauCetiRoadmap/ConformalMapping/README.md` aim at: they bound
the *diameter* of a piece at a well-chosen radius rather than describe the pieces individually.

The inclusion `⊇` is `TauCeti.clusterSetOn_subset_frontier_image` together with
`TauCeti.clusterSetOn_inter_of_mem_nhds`, which says a cluster set may be computed inside any ball
about the point, so the cluster set is adherent to the image of every ball neighbourhood. The
inclusion `⊆` is `TauCeti.clusterSetOn_eq_iInter`: every approach region in `𝓝[U] w` contains some
`U ∩ ball w ρ`, so a point adherent to the image of each of those is adherent to the image of each
approach region. -/
theorem iInter_frontier_inter_frontier_image_inter_ball_eq_clusterSetOn (hUo : IsOpen U)
    (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U) (hw : w ∈ frontier U) :
    ⋂ ρ > (0 : ℝ), frontier (f '' U) ∩ frontier (f '' (U ∩ ball w ρ)) = clusterSetOn f U w := by
  refine subset_antisymm (fun u hu => ?_) (subset_iInter₂ fun ρ hρ => ?_)
  · rw [clusterSetOn_eq_iInter]
    refine mem_iInter₂.mpr fun s hs => ?_
    obtain ⟨t, hto, hwt, hts⟩ := mem_nhdsWithin.mp hs
    obtain ⟨ρ, hρ, hρt⟩ := Metric.isOpen_iff.mp hto w hwt
    refine closure_mono (image_mono ?_) (frontier_subset_closure (mem_iInter₂.mp hu ρ hρ).2)
    exact fun z hz => hts ⟨hρt hz.2, hz.1⟩
  · have hwcl : w ∈ closure (U ∩ ball w ρ) := by
      rw [mem_closure_iff_nhdsWithin_neBot,
        nhdsWithin_inter_of_mem' (nhdsWithin_le_nhds (ball_mem_nhds w hρ))]
      exact mem_closure_iff_nhdsWithin_neBot.mp (frontier_subset_closure hw)
    rw [frontier_inter_frontier_image_inter_ball_eq_biUnion_clusterSetOn hUo hfd hfi w ρ,
      ← clusterSetOn_inter_of_mem_nhds (f := f) (U := U) (ball_mem_nhds w hρ)]
    exact subset_biUnion_of_mem ⟨hw, hwcl⟩

/-! ## The singleton property on a Jordan image boundary

The hypotheses of this section are those of Carathéodory's theorem apart from simple connectivity,
which plays no role once the map is given: `U` is open and convex — the disc of a Riemann map is the
case of interest, and convexity is what makes the cluster sets connected — the image is bounded, and
its frontier is a Jordan curve. -/

/-- **A boundary cluster set on a Jordan image boundary is a point, an arc, or the whole curve.**
For a conformal map of a convex domain whose image has Jordan frontier, a boundary cluster set other
than that whole frontier is either a subsingleton or the range of an injective path.

This is `TauCeti.IsJordanCurve.subsingleton_or_exists_injective_path` applied to the cluster set,
which `TauCeti.isCompact_clusterSetOn_of_isBounded`,
`TauCeti.isConnected_clusterSetOn_of_convex_of_isBounded` and
`TauCeti.clusterSetOn_subset_frontier_image` together exhibit as a compact connected subset of the
curve. Carathéodory's theorem — layer **L5** of the conformal-mapping
roadmap — is the assertion that for a Riemann map of a Jordan domain the first case always
holds. -/
theorem subsingleton_or_exists_injective_path_clusterSetOn (hUo : IsOpen U) (hUc : Convex ℝ U)
    (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U) (hfb : Bornology.IsBounded (f '' U))
    (hJ : IsJordanCurve (frontier (f '' U))) (hw : w ∈ frontier U)
    (hne : clusterSetOn f U w ≠ frontier (f '' U)) :
    (clusterSetOn f U w).Subsingleton ∨
      ∃ (p q : ℂ) (γ : Path p q), Function.Injective γ ∧ range γ = clusterSetOn f U w :=
  hJ.subsingleton_or_exists_injective_path (clusterSetOn_subset_frontier_image hUo hfd hfi hw)
    (isCompact_clusterSetOn_of_isBounded hfb)
    (isConnected_clusterSetOn_of_convex_of_isBounded hUc hfd.continuousOn hfb
      (frontier_subset_closure hw)).isPreconnected hne

/-- **A boundary cluster set that is nowhere dense in a Jordan image boundary is a single point.**
If every value the conformal map clusters at over the boundary point `w` is adherent to the rest of
`frontier (f '' U)`, then there is only one such value: the conclusion is that the cluster set is a
subsingleton, and under these hypotheses it is nonempty, being a continuum by
`TauCeti.isConnected_clusterSetOn_of_convex_of_isBounded`.

This is the nondegeneracy criterion
`TauCeti.IsJordanCurve.subsingleton_of_subset_closure_sdiff` for subcontinua of a Jordan curve, and
it is the whole content of the reduction: the cluster set is a continuum on the curve, and a
continuum on a Jordan curve that occupies no relatively open piece of it can only be a point. -/
theorem subsingleton_clusterSetOn_of_subset_closure_sdiff (hUo : IsOpen U) (hUc : Convex ℝ U)
    (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U) (hfb : Bornology.IsBounded (f '' U))
    (hJ : IsJordanCurve (frontier (f '' U))) (hw : w ∈ frontier U)
    (hnwd : clusterSetOn f U w ⊆ closure (frontier (f '' U) \ clusterSetOn f U w)) :
    (clusterSetOn f U w).Subsingleton :=
  hJ.subsingleton_of_subset_closure_sdiff (clusterSetOn_subset_frontier_image hUo hfd hfi hw)
    (isCompact_clusterSetOn_of_isBounded hfb)
    (isConnected_clusterSetOn_of_convex_of_isBounded hUc hfd.continuousOn hfb
      (frontier_subset_closure hw)).isPreconnected hnwd

/-- **A nowhere-density criterion for the Carathéodory extension.** A holomorphic injection of a
convex open set onto a bounded region whose frontier is a Jordan curve extends continuously to the
closure of the domain, provided no boundary cluster set occupies a relatively open piece of that
frontier. Boundedness is asked of the image `f '' U`, not of the domain.

This is the sufficient condition for the layer-**L5** milestone that the classification of
subcontinua supplies: the extension criterion
`TauCeti.exists_continuousOn_closure_eqOn_of_isBounded` asks exactly that every boundary cluster set
be a subsingleton, and `TauCeti.subsingleton_clusterSetOn_of_subset_closure_sdiff` weakens that to
relative nowhere density of each of those sets in the curve. The hypothesis `hnwd` remains a
condition on the cluster sets, which depend on `f`, `U` and the boundary point, and not one on
`frontier (f '' U)` by itself; what has gone is the analytic content, not the map.
Verifying the hypothesis for a Riemann map is what
the crosscut and length–area material is aimed at, and is not done here; nor is injectivity of the
extension on `frontier U`, which `TauCeti.injOn_closure_of_injOn_frontier` still asks for
separately. -/
theorem exists_continuousOn_closure_eqOn_of_forall_subset_closure_sdiff (hUo : IsOpen U)
    (hUc : Convex ℝ U) (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U)
    (hfb : Bornology.IsBounded (f '' U)) (hJ : IsJordanCurve (frontier (f '' U)))
    (hnwd : ∀ w ∈ frontier U,
      clusterSetOn f U w ⊆ closure (frontier (f '' U) \ clusterSetOn f U w)) :
    ∃ F : ℂ → ℂ, ContinuousOn F (closure U) ∧ EqOn F f U :=
  exists_continuousOn_closure_eqOn_of_isBounded hUo hfd.continuousOn hfb fun w hw =>
    subsingleton_clusterSetOn_of_subset_closure_sdiff hUo hUc hfd hfi hfb hJ hw (hnwd w hw)

end TauCeti
