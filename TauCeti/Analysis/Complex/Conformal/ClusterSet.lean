/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.BoundaryCorrespondence
public import TauCeti.Topology.ClusterSet
import TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected

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
then propagates to `closure U` for `TauCeti.closureHomeomorph`. Neither the singleton property nor
boundary injectivity is proved here.

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0–L6, the results below are stated for maps of `ℂ`, as in
`Conformal/BoundaryCorrespondence.lean`.

## Main results

* `TauCeti.notMem_image_of_mem_clusterSetOn` and `TauCeti.clusterSetOn_subset_frontier_image` — a
  boundary cluster value of a conformal map lies on the frontier of the image.
* `TauCeti.injOn_closure_of_injOn_frontier` — an extension injective on the frontier is injective
  on the closure.

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

end TauCeti
