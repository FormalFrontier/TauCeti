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
interior in that boundary curve, extends continuously to the closure.** This is a sufficient
condition for the L5 milestone stated entirely in terms of the boundary curve; what it does not do
is *verify* the nowhere-density hypothesis for a Riemann map, which is the step still separating L5
from its milestone and which the crosscut and length–area files are aimed at.

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

/-- **The boundary cluster sets exhaust the frontier of the image.** For a conformal map of a
bounded open set, the union of the cluster sets over `frontier U` is exactly `frontier (f '' U)`.

One inclusion is `TauCeti.clusterSetOn_subset_frontier_image` — no boundary cluster value is
attained, and none escapes the closure of the image — and the other is
`TauCeti.exists_mem_frontier_mem_clusterSetOn`. Neither connectedness nor simple connectedness of
`U` is used, and nothing is assumed about `frontier U`. -/
theorem biUnion_clusterSetOn_eq_frontier_image (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U) :
    ⋃ w ∈ frontier U, clusterSetOn f U w = frontier (f '' U) :=
  subset_antisymm (iUnion₂_subset fun _ hw => clusterSetOn_subset_frontier_image hUo hfd hfi hw)
    fun _ hv => by
      obtain ⟨w, hw, hvw⟩ := exists_mem_frontier_mem_clusterSetOn hUo hUb hfd hfi hv
      exact mem_biUnion hw hvw

/-! ## The singleton property on a Jordan image boundary

The hypotheses of this section are those of Carathéodory's theorem apart from simple connectivity,
which plays no role once the map is given: `U` is open and convex — the disc of a Riemann map is the
case of interest, and convexity is what makes the cluster sets connected — the image is bounded, and
its frontier is a Jordan curve. -/

/-- A boundary cluster set of a conformal map on a convex domain is a compact continuum lying on
the frontier of the image. This packages, for the two theorems below, the three inputs the
classification of
`TauCeti/Topology/JordanCurve/Subcontinuum.lean` consumes: compactness from boundedness of the
image, connectedness from convexity of the domain
(`TauCeti.isConnected_clusterSetOn_of_convex_of_isBounded`), and the location from
`TauCeti.clusterSetOn_subset_frontier_image`. -/
private theorem isCompact_isConnected_clusterSetOn_subset_frontier_image (hUo : IsOpen U)
    (hUc : Convex ℝ U)
    (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U) (hfb : Bornology.IsBounded (f '' U))
    (hw : w ∈ frontier U) :
    IsCompact (clusterSetOn f U w) ∧ IsConnected (clusterSetOn f U w) ∧
      clusterSetOn f U w ⊆ frontier (f '' U) :=
  ⟨isCompact_clusterSetOn_of_isBounded hfb,
    isConnected_clusterSetOn_of_convex_of_isBounded hUc hfd.continuousOn hfb
      (frontier_subset_closure hw),
    clusterSetOn_subset_frontier_image hUo hfd hfi hw⟩

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
  have h := isCompact_isConnected_clusterSetOn_subset_frontier_image hUo hUc hfd hfi hfb hw
  hJ.subsingleton_or_exists_injective_path h.2.2 h.1 h.2.1.isPreconnected hne

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
  have h := isCompact_isConnected_clusterSetOn_subset_frontier_image hUo hUc hfd hfi hfb hw
  hJ.subsingleton_of_subset_closure_sdiff h.2.2 h.1 h.2.1.isPreconnected hnwd

/-- **A nowhere-density criterion for the Carathéodory extension.** A holomorphic injection of a
convex open set onto a bounded region whose frontier is a Jordan curve extends continuously to the
closure of the domain, provided no boundary cluster set occupies a relatively open piece of that
frontier. Boundedness is asked of the image `f '' U`, not of the domain.

This is the sufficient condition for the layer-**L5** milestone that the classification of
subcontinua supplies: the extension criterion
`TauCeti.exists_continuousOn_closure_eqOn_of_isBounded` asks exactly that every boundary cluster set
be a subsingleton, and `TauCeti.subsingleton_clusterSetOn_of_subset_closure_sdiff` converts that
into a statement about the image boundary alone. Verifying the hypothesis for a Riemann map is what
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
