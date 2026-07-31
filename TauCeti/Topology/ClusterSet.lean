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
public import TauCeti.Topology.Continuum

/-!
# Cluster sets and the continuous extension they produce

The **cluster set** of a map `f` on `U` at a point `w` is the set of values approached by `f z` as
`z → w` inside `U`. It is the standard tool for reading off boundary behaviour: `f` extends
continuously across `w` exactly when it has a limit along `𝓝[U] w`, and — *once the values of `f`
are confined to a compact set* — that happens as soon as the cluster set at `w` has at most one
element. The compactness is not decoration: the cluster set of `z ↦ 1 / z` on `ball 0 1 \ {0}` at
`0` is empty, so it is a subsingleton while the map has no limit.

The second classical property of a cluster set, in the same spirit, is that it is a **continuum**:
when the approach regions `U ∩ t` are connected along a neighbourhood basis of `w` — as they are at
every boundary point of a convex domain — a cluster set with compact ambient values is nonempty,
compact and connected. So a boundary cluster set is either a single point or a nondegenerate
connected set; it is never a scattered pair of values, and a boundary correspondence theorem has
only to rule out the nondegenerate case.

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
* `TauCeti.clusterSetOn_eq_singleton_of_tendsto`,
  `TauCeti.clusterSetOn_eq_singleton_of_continuousWithinAt` and
  `TauCeti.exists_tendsto_of_clusterSetOn_subsingleton` — a limit along `𝓝[U] w` makes the cluster
  set a singleton, in particular at a point of `U` where `f` is continuous; conversely a
  subsingleton cluster set at a point of `closure U` produces a limit, provided `f` maps `U` into a
  compact set.
* `TauCeti.exists_mem_closure_mem_clusterSetOn`,
  `TauCeti.closure_image_eq_biUnion_clusterSetOn` and
  `TauCeti.closure_image_eq_image_union_biUnion_clusterSetOn` — **the cluster sets cover the closure
  of the image** once `closure U` is compact: every adherent value of `f '' U` is a cluster value at
  some point of `closure U`, so `closure (f '' U)` is the union of the cluster sets, and — for
  continuous `f` — is the image together with the *boundary* cluster values.
* `TauCeti.exists_continuousOn_closure_eqOn` — **the extension criterion**: a continuous map into a
  compact set, with subsingleton boundary cluster sets, extends continuously to `closure U`;
  `TauCeti.exists_continuousOn_closure_eqOn_of_isBounded` is the proper-metric form, where the
  compact set is the closure of the bounded image.
* `TauCeti.isPreconnected_clusterSetOn` and `TauCeti.isConnected_clusterSetOn` — **the cluster set
  is a continuum** once the approach regions `U ∩ t` are preconnected along a neighbourhood basis
  of `w`; `TauCeti.isCompact_clusterSetOn_of_isBounded` and
  `TauCeti.isConnected_clusterSetOn_of_isBounded` are again the proper-metric forms.

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
values that cannot be separated from `f` on any approach region.

Since `closure (f '' ·)` is monotone, `Filter.HasBasis.biInter_mem` cuts the intersection down to
any basis of `𝓝[U] w`; that is how the cluster set is exhibited as a *directed* intersection in
`TauCeti.isPreconnected_clusterSetOn`, a basis being directed by design. -/
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

/-- **At a point of `U` where `f` is continuous the cluster set is the value.** Nothing but `f w`
is approached, so a cluster set carries information only at points off `U` — which is why a
boundary-correspondence theorem never has to say anything about the interior. -/
lemma clusterSetOn_eq_singleton_of_continuousWithinAt [T2Space Y] (hw : w ∈ U)
    (hfc : ContinuousWithinAt f U w) : clusterSetOn f U w = {f w} :=
  clusterSetOn_eq_singleton_of_tendsto (subset_closure hw) hfc

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

/-! ## The cluster sets cover the closure of the image -/

/-- **Every adherent value of the image is a cluster value at some point of `closure U`**, provided
`closure U` is compact.

Aggregated over `w`, this is the converse of `TauCeti.clusterSetOn_subset_closure_image`, and it is
where compactness of the *domain* side enters. That hypothesis cannot be dropped: on
`U = Set.Ici (0 : ℝ)`, whose closure is not compact, the map `f x = 1 / (1 + x)` has image
`Set.Ioc 0 1` and so has `0` adherent to it, yet `0` is a cluster value of `f` at no point at all —
the approach points have escaped to infinity.

No continuity is needed, and the proof is pure filter theory. The filter
`comap f (𝓝 v) ⊓ 𝓟 U` — "inside `U`, with image near `v`" — is nontrivial *because* `v` is adherent
to `f '' U`, and it is carried by `𝓟 (closure U)`; compactness supplies a cluster point `w` of it,
and the witnessing filter `𝓝 w ⊓ (comap f (𝓝 v) ⊓ 𝓟 U)` is a nontrivial filter refining `𝓝[U] w`
whose image under `f` refines `𝓝 v`, which is exactly what `v ∈ clusterSetOn f U w` asserts. -/
theorem exists_mem_closure_mem_clusterSetOn (hU : IsCompact (closure U))
    (hv : v ∈ closure (f '' U)) : ∃ w ∈ closure U, v ∈ clusterSetOn f U w := by
  haveI : (comap f (𝓝 v) ⊓ 𝓟 U).NeBot := by
    refine Filter.inf_principal_neBot_iff.mpr fun t ht => ?_
    obtain ⟨s, hs, hst⟩ := ht
    obtain ⟨y, hys, z, hzU, rfl⟩ := mem_closure_iff_nhds.mp hv s hs
    exact ⟨z, hst hys, hzU⟩
  have hle : comap f (𝓝 v) ⊓ 𝓟 U ≤ 𝓟 (closure U) :=
    inf_le_right.trans (principal_mono.mpr subset_closure)
  obtain ⟨w, hw, hcp⟩ := hU.exists_clusterPt hle
  refine ⟨w, hw, ?_⟩
  have hnb : (𝓝 w ⊓ (comap f (𝓝 v) ⊓ 𝓟 U)).NeBot := hcp
  have hv' : map f (𝓝 w ⊓ (comap f (𝓝 v) ⊓ 𝓟 U)) ≤ 𝓝 v :=
    (map_mono (inf_le_right.trans inf_le_left)).trans map_comap_le
  have hw' : 𝓝 w ⊓ (comap f (𝓝 v) ⊓ 𝓟 U) ≤ 𝓝[U] w :=
    le_inf inf_le_left (inf_le_right.trans inf_le_right)
  exact (hnb.map f).mono (le_inf hv' (map_mono hw'))

/-- **The cluster sets cover the closure of the image.** For a compact `closure U`, the closure of
`f '' U` is exactly the union of the cluster sets of `f` on `U` over the points of `closure U`.

Both inclusions have already been recorded: `TauCeti.clusterSetOn_subset_closure_image` gives one
and `TauCeti.exists_mem_closure_mem_clusterSetOn` the other. -/
theorem closure_image_eq_biUnion_clusterSetOn (hU : IsCompact (closure U)) :
    closure (f '' U) = ⋃ w ∈ closure U, clusterSetOn f U w :=
  subset_antisymm
    (fun _ hv => by
      obtain ⟨w, hw, hvw⟩ := exists_mem_closure_mem_clusterSetOn hU hv
      exact mem_biUnion hw hvw)
    (iUnion₂_subset fun _ _ => clusterSetOn_subset_closure_image)

/-- **The closure of the image is the image together with the boundary cluster values.** The
refinement of `TauCeti.closure_image_eq_biUnion_clusterSetOn` for a continuous `f`: the points of
`U` contribute only the values `f w` themselves, by
`TauCeti.clusterSetOn_eq_singleton_of_continuousWithinAt`, so the whole of the new material sits
over `frontier U`.

This is the form in which the covering is used: subtracting `f '' U` from both sides identifies the
*frontier* of the image with the union of the boundary cluster sets, as soon as one knows that the
boundary cluster values avoid `f '' U`. -/
theorem closure_image_eq_image_union_biUnion_clusterSetOn [T2Space Y] (hU : IsCompact (closure U))
    (hfc : ContinuousOn f U) :
    closure (f '' U) = f '' U ∪ ⋃ w ∈ frontier U, clusterSetOn f U w := by
  have hint : ⋃ w ∈ U, clusterSetOn f U w = f '' U := by
    ext v
    simp only [mem_iUnion₂, mem_image]
    refine ⟨fun ⟨w, hw, hv⟩ => ⟨w, hw, ?_⟩, fun ⟨w, hw, hv⟩ => ⟨w, hw, ?_⟩⟩
    · rw [clusterSetOn_eq_singleton_of_continuousWithinAt hw (hfc w hw),
        mem_singleton_iff] at hv
      exact hv.symm
    · rw [clusterSetOn_eq_singleton_of_continuousWithinAt hw (hfc w hw), mem_singleton_iff]
      exact hv.symm
  rw [closure_image_eq_biUnion_clusterSetOn hU, closure_eq_self_union_frontier, biUnion_union,
    hint]

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

/-! ## The cluster set as a continuum -/

section Continuum

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {U : Set X}
  {K : Set Y} {f : X → Y} {w : X}

/-- **The cluster set is preconnected when the approach regions are.** If `f` is continuous on `U`
with values in a compact set, and `w` has a neighbourhood basis of sets `t` whose trace `U ∩ t` on
`U` is preconnected, then the cluster set of `f` on `U` at `w` is preconnected.

The basis hypothesis is what a domain contributes: it holds at every point of the closure of a
convex `U`, and more generally whenever `U` is locally connected along its boundary. It cannot be
dropped — the cluster set of a map on a disconnected `U` is a union of the cluster sets along the
pieces, which have no reason to meet.

The proof writes the cluster set as `⋂ t, closure (f '' (U ∩ t))` over such a basis, by
`TauCeti.clusterSetOn_eq_iInter` and `Filter.HasBasis.biInter_mem`, whose monotonicity hypothesis
is met by `closure (f '' ·)`. Each member is a compact preconnected set — the continuous image of a
preconnected set, closed up, inside the compact `K` — and the family is directed downwards because
the basis is. So `TauCeti.isPreconnected_iInter_of_directed` applies. -/
theorem isPreconnected_clusterSetOn (hK : IsCompact K) (hfK : MapsTo f U K)
    (hfc : ContinuousOn f U)
    (hconn : ∀ s ∈ 𝓝 w, ∃ t ∈ 𝓝 w, t ⊆ s ∧ IsPreconnected (U ∩ t)) :
    IsPreconnected (clusterSetOn f U w) := by
  have hp : ∀ s ∈ 𝓝 w, ∃ t, (t ∈ 𝓝 w ∧ IsPreconnected (t ∩ U)) ∧ t ⊆ s := by
    intro s hs
    obtain ⟨t, htw, hts, htp⟩ := hconn s hs
    exact ⟨t, ⟨htw, by rwa [inter_comm]⟩, hts⟩
  have hbasis : (𝓝 w).HasBasis (fun t => t ∈ 𝓝 w ∧ IsPreconnected (t ∩ U)) (fun t => t) :=
    ⟨fun s => ⟨hp s, fun ⟨t, ht, hts⟩ => mem_of_superset ht.1 hts⟩⟩
  have hEq : clusterSetOn f U w =
      ⋂ t : {t : Set X // t ∈ 𝓝 w ∧ IsPreconnected (t ∩ U)}, closure (f '' (t.1 ∩ U)) := by
    rw [clusterSetOn_eq_iInter, (nhdsWithin_hasBasis hbasis U).biInter_mem
      (fun _ _ hst => closure_mono (image_mono hst)), iInter_subtype]
  have : Nonempty {t : Set X // t ∈ 𝓝 w ∧ IsPreconnected (t ∩ U)} := by
    obtain ⟨t, ht, -⟩ := hp univ univ_mem
    exact ⟨⟨t, ht⟩⟩
  rw [hEq]
  refine isPreconnected_iInter_of_directed (fun t₁ t₂ => ?_) (fun t => ?_) (fun t => ?_)
  · obtain ⟨t₃, ht₃, hsub⟩ := hp (t₁.1 ∩ t₂.1) (inter_mem t₁.2.1 t₂.2.1)
    exact ⟨⟨t₃, ht₃⟩,
      closure_mono (image_mono (inter_subset_inter_left U (hsub.trans inter_subset_left))),
      closure_mono (image_mono (inter_subset_inter_left U (hsub.trans inter_subset_right)))⟩
  · exact hK.of_isClosed_subset isClosed_closure
      (closure_minimal ((image_mono inter_subset_right).trans hfK.image_subset) hK.isClosed)
  · exact (t.2.2.image f (hfc.mono inter_subset_right)).closure

/-- **The cluster set is a continuum**: nonempty, compact and connected. This is the classical
statement of Collingwood–Lohwater, under the hypotheses of
`TauCeti.isPreconnected_clusterSetOn` together with `w ∈ closure U`, which is what makes the
approach filter `𝓝[U] w` nontrivial and hence the cluster set nonempty.

Compactness is `TauCeti.isCompact_clusterSetOn` and is not repeated here. -/
theorem isConnected_clusterSetOn (hK : IsCompact K) (hfK : MapsTo f U K) (hfc : ContinuousOn f U)
    (hw : w ∈ closure U)
    (hconn : ∀ s ∈ 𝓝 w, ∃ t ∈ 𝓝 w, t ⊆ s ∧ IsPreconnected (U ∩ t)) :
    IsConnected (clusterSetOn f U w) :=
  ⟨clusterSetOn_nonempty hK hfK hw, isPreconnected_clusterSetOn hK hfK hfc hconn⟩

end Continuum

section ProperContinuum

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y] [ProperSpace Y] {U : Set X}
  {f : X → Y} {w : X}

/-- The cluster set of a map with bounded image into a proper metric space is compact: the special
case of `TauCeti.isCompact_clusterSetOn` in which the compact set containing the values is the
closure of the bounded image. -/
lemma isCompact_clusterSetOn_of_isBounded (hfb : Bornology.IsBounded (f '' U)) :
    IsCompact (clusterSetOn f U w) :=
  isCompact_clusterSetOn hfb.isCompact_closure fun z hz => subset_closure ⟨z, hz, rfl⟩

/-- **The continuum form for a bounded map into a proper metric space**, the special case of
`TauCeti.isConnected_clusterSetOn` in which the compact set containing the values is the closure of
the bounded image. -/
theorem isConnected_clusterSetOn_of_isBounded (hfc : ContinuousOn f U)
    (hfb : Bornology.IsBounded (f '' U)) (hw : w ∈ closure U)
    (hconn : ∀ s ∈ 𝓝 w, ∃ t ∈ 𝓝 w, t ⊆ s ∧ IsPreconnected (U ∩ t)) :
    IsConnected (clusterSetOn f U w) :=
  isConnected_clusterSetOn hfb.isCompact_closure (fun z hz => subset_closure ⟨z, hz, rfl⟩) hfc hw
    hconn

end ProperContinuum

end TauCeti
