/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ClusterPt
public import Mathlib.Topology.ExtendFrom
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Cluster sets and the continuous extension they produce

The **cluster set** of a map `f` on `U` at a point `w` is the set of values approached by `f z` as
`z → w` inside `U`. It is the standard tool for reading off boundary behaviour: `f` extends
continuously across `w` exactly when it has a limit along `𝓝[U] w`, and — *once the values of `f`
are confined to a compact set* — that happens as soon as the cluster set at `w` has at most one
element. The compactness is not decoration: the cluster set of `z ↦ 1 / z` on `ball 0 1 \ {0}` at
`0` is empty, so it is a subsingleton while the map has no limit.

Nothing in this file is specific to one geometry. The definition and its basic API live over an
arbitrary pair of topological spaces, the `ε`-`δ` characterization over metric spaces, and the
extension theorem over an arbitrary `T3` codomain, into a compact subset of which the map is
assumed to take its values; a proper metric codomain with a bounded image is the special case in
which that compact set is supplied by the boundedness. The complex-analytic consequences — that the
boundary cluster set of a conformal map lies on the frontier of the image — are in
`TauCeti/Analysis/Complex/Conformal/ClusterSet.lean`, the consumer this file was written for:
Carathéodory's boundary correspondence, layer **L5** of the conformal-mapping roadmap, is applied
by checking that the boundary cluster sets of a Riemann map are singletons and feeding that into
`TauCeti.exists_continuousOn_closure_eqOn`.

The cluster set is `{v | MapClusterPt v (𝓝[U] w) f}`; Mathlib has the `ClusterPt`/`MapClusterPt`
API, on which everything below is built, but no name for this set. The extension itself is
Mathlib's `extendFrom U f`, whose continuity comes from `continuousOn_extendFrom`: all the
criterion adds is the production of the pointwise limits that theorem asks for.

## Main definitions

* `TauCeti.clusterSetOn` — the cluster set of `f` on `U` at `w`.

## Main results

* `TauCeti.clusterSetOn_eq_iInter` and `TauCeti.mem_clusterSetOn_iff_forall_exists` — the two
  textbook characterizations, as a nested intersection and in `ε`-`δ` form.
* `TauCeti.isClosed_clusterSetOn`, `TauCeti.clusterSetOn_subset_closure_image`,
  `TauCeti.isCompact_clusterSetOn` and `TauCeti.clusterSetOn_nonempty` — the cluster set is a closed
  subset of `closure (f '' U)`, and is compact and nonempty at every point of `closure U` once `f`
  maps `U` into a compact set.
* `TauCeti.clusterSetOn_eq_singleton_of_tendsto` and
  `TauCeti.exists_tendsto_of_clusterSetOn_subsingleton` — a limit along `𝓝[U] w` makes the cluster
  set a singleton; conversely a subsingleton cluster set at a point of `closure U` produces a limit,
  provided `f` maps `U` into a compact set.
* `TauCeti.exists_continuousOn_closure_eqOn` — **the extension criterion**: a continuous map into a
  compact set, with subsingleton boundary cluster sets, extends continuously to `closure U`;
  `TauCeti.exists_continuousOn_closure_eqOn_of_isBounded` is the proper-metric form, where the
  compact set is the closure of the bounded image.

## References

* E. F. Collingwood and A. J. Lohwater, *The Theory of Cluster Sets*, Ch. 1.
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
-/

public section

namespace TauCeti

open Filter Metric Set Topology

/-! ## The cluster set -/

section TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {U : Set X} {K : Set Y}
  {f : X → Y} {v : Y} {w : X}

/-- The **cluster set** of `f` on `U` at `w`: the set of values approached by `f z` as `z` tends to
`w` from inside `U`. Equivalently, the set of cluster points of the filter `𝓝[U] w` pushed forward
by `f`.

The point `w` is not required to lie in `U`, and the interesting case is `w ∈ frontier U`, where
the cluster set records the boundary behaviour of `f`. If `w ∉ closure U` the filter `𝓝[U] w` is
trivial and the cluster set is empty. -/
def clusterSetOn (f : X → Y) (U : Set X) (w : X) : Set Y := {v | MapClusterPt v (𝓝[U] w) f}

/-- Membership in the cluster set is exactly Mathlib's `MapClusterPt` for the filter `𝓝[U] w`. This
is the normal form: the alternative characterizations below are deliberately left untagged. -/
@[simp]
lemma mem_clusterSetOn_iff : v ∈ clusterSetOn f U w ↔ MapClusterPt v (𝓝[U] w) f := Iff.rfl

/-- Membership in the cluster set, unfolded: every neighbourhood of `v` is hit by `f` frequently
along `𝓝[U] w`. -/
lemma mem_clusterSetOn_iff_frequently :
    v ∈ clusterSetOn f U w ↔ ∀ s ∈ 𝓝 v, ∃ᶠ z in 𝓝[U] w, f z ∈ s :=
  mapClusterPt_iff_frequently

/-- **The cluster set as a nested intersection**, the form in which it is usually defined: the
values that cannot be separated from `f` on any approach region. -/
lemma clusterSetOn_eq_iInter : clusterSetOn f U w = ⋂ s ∈ 𝓝[U] w, closure (f '' s) := by
  ext v
  rw [mem_clusterSetOn_iff, MapClusterPt, clusterPt_iff_forall_mem_closure, mem_iInter₂]
  refine ⟨fun h s hs => h _ (image_mem_map hs), fun h t ht => ?_⟩
  exact closure_mono (image_preimage_subset f t) (h _ (mem_map.mp ht))

/-- The cluster set is closed: it is a set of cluster points of a filter. -/
lemma isClosed_clusterSetOn : IsClosed (clusterSetOn f U w) := isClosed_setOfPred_clusterPt

/-- Enlarging the set along which `f` is followed enlarges the cluster set. -/
lemma clusterSetOn_mono {V : Set X} (h : U ⊆ V) : clusterSetOn f U w ⊆ clusterSetOn f V w :=
  fun _ hv => hv.mono (nhdsWithin_mono w h)

/-- Every cluster value is a limit of image points: the cluster set sits inside
`closure (f '' U)`. -/
lemma clusterSetOn_subset_closure_image : clusterSetOn f U w ⊆ closure (f '' U) :=
  fun _ hv => hv.clusterPt.mem_closure_of_mem _ (image_mem_map self_mem_nhdsWithin)

/-- The cluster set is compact whenever `f` maps `U` into a compact set: it is a closed subset of
that set. -/
lemma isCompact_clusterSetOn [T2Space Y] (hK : IsCompact K) (hfK : MapsTo f U K) :
    IsCompact (clusterSetOn f U w) :=
  hK.of_isClosed_subset isClosed_clusterSetOn <|
    clusterSetOn_subset_closure_image.trans <|
      hK.isClosed.closure_subset_iff.mpr hfK.image_subset

/-- **The cluster set is nonempty at every point of the closure**, provided `f` maps `U` into a
compact set. Some such hypothesis is needed: the cluster set of `z ↦ 1 / z` on
`ball 0 1 \ {0}` at `0` is empty, the values escaping to infinity. -/
lemma clusterSetOn_nonempty (hK : IsCompact K) (hfK : MapsTo f U K) (hw : w ∈ closure U) :
    (clusterSetOn f U w).Nonempty := by
  haveI : (𝓝[U] w).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hw
  have hle : map f (𝓝[U] w) ≤ 𝓟 K :=
    le_principal_iff.mpr (mem_map.mpr (mem_of_superset self_mem_nhdsWithin hfK))
  obtain ⟨v, -, hv⟩ := hK.exists_mapClusterPt hle
  exact ⟨v, hv⟩

/-! ## Cluster sets and limits -/

/-- If `f` has a limit `v` along `𝓝[U] w`, the cluster set is exactly `{v}`. -/
lemma clusterSetOn_eq_singleton_of_tendsto [T2Space Y] (hw : w ∈ closure U)
    (hv : Tendsto f (𝓝[U] w) (𝓝 v)) : clusterSetOn f U w = {v} := by
  haveI : (𝓝[U] w).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hw
  have hv' : map f (𝓝[U] w) ≤ 𝓝 v := hv
  refine subset_antisymm (fun u hu => ?_) (singleton_subset_iff.mpr hv.mapClusterPt)
  -- Both `u` and `v` are limits of the identity along the nontrivial filter `𝓝 u ⊓ map f (𝓝[U] w)`.
  haveI : (𝓝 u ⊓ map f (𝓝[U] w)).NeBot := hu.clusterPt
  exact mem_singleton_iff.mpr
    (tendsto_nhds_unique (f := id) (tendsto_id.mono_left inf_le_left)
      (tendsto_id.mono_left (inf_le_right.trans hv')))

/-- **A subsingleton cluster set is an honest limit.** If `f` maps `U` into a compact set and the
cluster set at `w ∈ closure U` has at most one element, then `f` converges along `𝓝[U] w`.

The compactness hypothesis is what makes this a genuine converse to
`TauCeti.clusterSetOn_eq_singleton_of_tendsto` rather than a vacuous one: it forces the cluster set
to be nonempty, by `TauCeti.clusterSetOn_nonempty`, and a filter with values in a compact set and a
unique cluster point converges to it. -/
theorem exists_tendsto_of_clusterSetOn_subsingleton (hK : IsCompact K) (hfK : MapsTo f U K)
    (hw : w ∈ closure U) (hsub : (clusterSetOn f U w).Subsingleton) :
    ∃ v, Tendsto f (𝓝[U] w) (𝓝 v) := by
  haveI : (𝓝[U] w).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hw
  obtain ⟨v, hv⟩ := clusterSetOn_nonempty hK hfK hw
  exact ⟨v, hK.tendsto_nhds_of_unique_mapClusterPt
    (mem_of_superset self_mem_nhdsWithin hfK) fun _ _ hu => hsub hu hv⟩

end TopologicalSpace

/-! ## The metric picture -/

section PseudoMetricSpace

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {U : Set X} {f : X → Y}
  {v : Y} {w : X}

/-- The `ε`-`δ` form of membership in the cluster set: `f` takes values arbitrarily close to `v` at
points of `U` arbitrarily close to `w`. -/
lemma mem_clusterSetOn_iff_forall_exists :
    v ∈ clusterSetOn f U w ↔ ∀ ε > 0, ∀ δ > 0, ∃ z ∈ U, dist z w < δ ∧ dist (f z) v < ε := by
  rw [mem_clusterSetOn_iff_frequently]
  constructor
  · intro h ε hε δ hδ
    obtain ⟨z, hz, hzU, hzd⟩ :=
      ((h _ (ball_mem_nhds v hε)).and_eventually
        (inter_mem_nhdsWithin U (ball_mem_nhds w hδ))).exists
    exact ⟨z, hzU, mem_ball.mp hzd, mem_ball.mp hz⟩
  · intro h s hs
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
    rw [(nhdsWithin_basis_ball (x := w) (s := U)).frequently_iff]
    intro δ hδ
    obtain ⟨z, hzU, hzd, hfz⟩ := h ε hε δ hδ
    exact ⟨z, ⟨mem_ball.mpr hzd, hzU⟩, hball (mem_ball.mpr hfz)⟩

end PseudoMetricSpace

/-! ## The extension criterion -/

section Extension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T3Space Y] {U : Set X}
  {K : Set Y} {f : X → Y}

/-- **The extension criterion.** A continuous function on an open `U`, taking values in a compact
set and whose cluster set at each boundary point has at most one element, extends continuously to
`closure U`.

The compactness is what `TauCeti.exists_tendsto_of_clusterSetOn_subsingleton` consumes to turn each
subsingleton boundary cluster set into a limit; at an interior point continuity already supplies
the limit. Having a limit at every point of `closure U`, the map extends by Mathlib's `extendFrom`,
which is continuous on `closure U` by `continuousOn_extendFrom` and agrees with `f` on `U` by
`extendFrom_extends`. `TauCeti.exists_continuousOn_closure_eqOn_of_isBounded` is the common special
case of a bounded-image map into a proper metric space.

This is the form in which a boundary-correspondence theorem is applied: whatever geometric
hypothesis one places on `frontier U`, it is used only to check that the boundary cluster sets are
singletons, and this theorem converts that check into a continuous extension. No cluster-set
hypothesis is needed at the *interior* points of `U`, where continuity already makes the cluster
set the singleton `{f w}`.

The conclusion is exactly a continuous extension: `F` is continuous on `closure U` and agrees with
`f` on `U`. Nothing is claimed about injectivity of `F` on `closure U`; that is an independent
matter, requiring a separate proof that `F` is injective on `frontier U`. -/
theorem exists_continuousOn_closure_eqOn (hUo : IsOpen U) (hfc : ContinuousOn f U)
    (hK : IsCompact K) (hfK : MapsTo f U K)
    (hsub : ∀ w ∈ frontier U, (clusterSetOn f U w).Subsingleton) :
    ∃ F : X → Y, ContinuousOn F (closure U) ∧ EqOn F f U := by
  have hall : ∀ w ∈ closure U, ∃ v, Tendsto f (𝓝[U] w) (𝓝 v) := by
    intro w hw
    by_cases hwU : w ∈ U
    · exact ⟨f w, hfc w hwU⟩
    · exact exists_tendsto_of_clusterSetOn_subsingleton hK hfK hw
        (hsub w (by rw [hUo.frontier_eq]; exact ⟨hw, hwU⟩))
  exact ⟨extendFrom U f, continuousOn_extendFrom subset_rfl hall, extendFrom_extends hfc⟩

end Extension

section ProperExtension

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y] [ProperSpace Y] {U : Set X} {f : X → Y}

/-- **The extension criterion for a bounded map into a proper metric space.** The special case of
`TauCeti.exists_continuousOn_closure_eqOn` in which the compact set containing the values of `f` is
the closure of a bounded image, properness of the codomain being what makes that closure compact. -/
theorem exists_continuousOn_closure_eqOn_of_isBounded (hUo : IsOpen U) (hfc : ContinuousOn f U)
    (hfb : Bornology.IsBounded (f '' U))
    (hsub : ∀ w ∈ frontier U, (clusterSetOn f U w).Subsingleton) :
    ∃ F : X → Y, ContinuousOn F (closure U) ∧ EqOn F f U :=
  exists_continuousOn_closure_eqOn hUo hfc hfb.isCompact_closure
    (fun z hz => subset_closure ⟨z, hz, rfl⟩) hsub

end ProperExtension

end TauCeti
