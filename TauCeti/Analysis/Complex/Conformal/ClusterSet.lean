/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ClusterPt
public import TauCeti.Analysis.Complex.Conformal.BoundaryCorrespondence
import TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected

/-!
# Cluster sets and the extension criterion for the boundary correspondence

The **cluster set** of a map `f` on `U` at a point `w` is the set of values approached by `f z` as
`z → w` inside `U`. It is the standard tool of boundary behaviour in geometric function theory:
`f` extends continuously to `w` exactly when the cluster set there degenerates to a single point,
so Carathéodory's boundary correspondence — layer **L5** of the conformal-mapping roadmap — is the
assertion that for a Riemann map of a Jordan domain every boundary cluster set is a singleton.

`Conformal/BoundaryCorrespondence.lean` proves what a conformal map does *given* a continuous
extension to the closure. This file supplies the missing half of that interface: it removes the
extension from the hypotheses, and gives back the criterion that produces one.

Two things are proved, and they meet in `TauCeti.exists_continuousOn_closure_eqOn`.

* **Unconditionally, the boundary cluster set of a conformal map lies on the frontier of the
  image.** This is the extension-free form of `TauCeti.notMem_image_of_mem_frontier`: no continuous
  extension is assumed, and the conclusion is about *every* cluster value. The mechanism is the
  properness of a conformal map, exactly as there — a cluster value inside the open set `f '' U`
  would be approached frequently inside a compact subset of `f '' U` that properness says `f`
  leaves eventually.
* **A map with bounded image and subsingleton boundary cluster sets extends continuously to the
  closure.** Compactness turns "the cluster set is a subsingleton" into an honest limit
  `Tendsto f (𝓝[U] w) (𝓝 (F w))` at each `w ∈ closure U`, and a pointwise limit at every point of
  the closure is automatically a *continuous* function of the point: if `f` is within `ε / 2` of
  `F w` on `U ∩ ball w δ`, then for `w'` within `δ / 2` of `w` the values of `f` near `w'` are
  still that close, and `F w'`, being their limit, is too.

The second bullet is the shape in which Carathéodory's theorem is used: whatever geometric
hypothesis one places on the boundary (a Jordan curve, local connectivity), it is discharged by
checking that the cluster sets are singletons, and this file converts that check into the
continuous extension that `Conformal/BoundaryCorrespondence.lean` turns into a homeomorphism of
closures. The last result here supplies the injectivity that packaging needs: an extension
injective on `frontier U` is automatically injective on `closure U`, because the boundary values
have just been shown to avoid the image.

The cluster set is `{v | MapClusterPt v (𝓝[U] w) f}`; Mathlib has the `ClusterPt` API but no name
for this set. In accordance with the generality bar of `ConformalMapping/README.md`, which fixes
scalar `ℂ` for every theorem added in layers L0–L6, everything is stated for maps of `ℂ`, as in
`Conformal/BoundaryCorrespondence.lean`; the definition and its purely topological lemmas would
read the same over an arbitrary pair of topological spaces.

## Main definitions and results

* `TauCeti.clusterSetOn` — the cluster set of `f` on `U` at `w`, with
  `TauCeti.clusterSetOn_eq_iInter` and `TauCeti.mem_clusterSetOn_iff_forall_exists` as its
  textbook characterizations.
* `TauCeti.isClosed_clusterSetOn`, `TauCeti.clusterSetOn_subset_closure_image`,
  `TauCeti.isCompact_clusterSetOn` and `TauCeti.clusterSetOn_nonempty` — it is a compact subset of
  `closure (f '' U)`, nonempty at every point of `closure U` when the image is bounded.
* `TauCeti.clusterSetOn_eq_singleton_of_tendsto` and `TauCeti.exists_tendsto_of_subsingleton` — the
  cluster set is a singleton exactly when `f` has a limit along `𝓝[U] w`.
* `TauCeti.notMem_image_of_mem_clusterSetOn` and `TauCeti.clusterSetOn_subset_frontier_image` — a
  boundary cluster value of a conformal map lies on the frontier of the image.
* `TauCeti.continuousOn_closure_of_forall_tendsto` — a pointwise limit at every point of
  `closure U` is continuous there.
* `TauCeti.exists_continuousOn_closure_eqOn` — **the extension criterion**: subsingleton boundary
  cluster sets and a bounded image give a continuous extension to `closure U`.
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

variable {U K : Set ℂ} {f F : ℂ → ℂ} {v w : ℂ}

/-! ## The cluster set -/

/-- The **cluster set** of `f` on `U` at `w`: the set of values approached by `f z` as `z` tends to
`w` from inside `U`. Equivalently, the set of cluster points of the filter `𝓝[U] w` pushed forward
by `f`.

The point `w` is not required to lie in `U`, and the interesting case is `w ∈ frontier U`, where
the cluster set records the boundary behaviour of `f`. If `w ∉ closure U` the filter `𝓝[U] w` is
trivial and the cluster set is empty. -/
def clusterSetOn (f : ℂ → ℂ) (U : Set ℂ) (w : ℂ) : Set ℂ := {v | MapClusterPt v (𝓝[U] w) f}

/-- Membership in the cluster set is exactly Mathlib's `MapClusterPt` for the filter `𝓝[U] w`. -/
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

/-- The cluster set is closed: it is an intersection of closures. -/
lemma isClosed_clusterSetOn : IsClosed (clusterSetOn f U w) :=
  clusterSetOn_eq_iInter ▸ isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_closure

/-- Enlarging the set along which `f` is followed enlarges the cluster set. -/
lemma clusterSetOn_mono {V : Set ℂ} (h : U ⊆ V) : clusterSetOn f U w ⊆ clusterSetOn f V w :=
  fun _ hv => hv.mono (nhdsWithin_mono w h)

/-- Every cluster value is a limit of image points: the cluster set sits inside
`closure (f '' U)`. -/
lemma clusterSetOn_subset_closure_image : clusterSetOn f U w ⊆ closure (f '' U) :=
  fun _ hv => hv.clusterPt.mem_closure_of_mem _ (image_mem_map self_mem_nhdsWithin)

/-- If `f` maps `U` into `K`, then `K` belongs to the filter `f` pushes `𝓝[U] w` forward to. This
is the hypothesis the two compactness arguments below both feed on. -/
private lemma mem_map_of_mapsTo (hfK : MapsTo f U K) : K ∈ map f (𝓝[U] w) :=
  mem_map.mpr (mem_of_superset self_mem_nhdsWithin hfK)

/-- The cluster set is compact whenever `f` maps `U` into a compact set: it is a closed subset of
that set. -/
lemma isCompact_clusterSetOn (hK : IsCompact K) (hfK : MapsTo f U K) :
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
  obtain ⟨v, -, hv⟩ :=
    hK.exists_clusterPt (f := map f (𝓝[U] w)) (le_principal_iff.mpr (mem_map_of_mapsTo hfK))
  exact ⟨v, hv⟩

/-! ## Cluster sets and limits -/

/-- If `f` has a limit `v` along `𝓝[U] w`, the cluster set is exactly `{v}`. -/
lemma clusterSetOn_eq_singleton_of_tendsto (hw : w ∈ closure U)
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

This is the compactness step of the extension criterion: the cluster set is a singleton by
`TauCeti.clusterSetOn_nonempty`, and a filter with values in a compact set and a unique cluster
point converges to it. -/
theorem exists_tendsto_of_subsingleton (hK : IsCompact K) (hfK : MapsTo f U K)
    (hw : w ∈ closure U) (hsub : (clusterSetOn f U w).Subsingleton) :
    ∃ v, Tendsto f (𝓝[U] w) (𝓝 v) := by
  haveI : (𝓝[U] w).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hw
  obtain ⟨v, hv⟩ := clusterSetOn_nonempty hK hfK hw
  exact ⟨v, hK.le_nhds_of_unique_clusterPt (mem_map_of_mapsTo hfK) fun _ _ hu => hsub hu hv⟩

/-! ## The cluster set of a conformal map at a boundary point -/

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

/-! ## From pointwise limits to a continuous extension -/

/-- **A pointwise limit at every point of the closure is continuous on the closure.** If `F w` is
the limit of `f` along `𝓝[U] w` for every `w ∈ closure U`, then `F` is continuous on `closure U`.

No continuity of `F` is assumed anywhere; it is forced by the limits. Given `ε > 0`, pick `δ` with
`dist (f z) (F w) < ε / 2` for `z ∈ U ∩ ball w δ`. A point `w' ∈ closure U` within `δ / 2` of `w`
has `U ∩ ball w' (δ / 2) ⊆ U ∩ ball w δ`, so `f` stays in the *closed* ball of radius `ε / 2`
about `F w` along the nontrivial filter `𝓝[U] w'`, and therefore so does its limit `F w'`.

This is the step that upgrades Carathéodory's boundary limits to a continuous extension. It is
purely metric: nothing about `f` beyond the hypothesis is used. -/
theorem continuousOn_closure_of_forall_tendsto
    (hF : ∀ w ∈ closure U, Tendsto f (𝓝[U] w) (𝓝 (F w))) : ContinuousOn F (closure U) := by
  intro w hw
  rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.tendsto_nhdsWithin_nhds.mp (hF w hw) (ε / 2) (by linarith)
  refine ⟨δ / 2, by linarith, fun {w'} hw' hw'd => ?_⟩
  haveI : (𝓝[U] w').NeBot := mem_closure_iff_nhdsWithin_neBot.mp hw'
  -- Near `w'`, the values of `f` are within `ε / 2` of `F w`, because they are also near `w`.
  have hmem : ∀ᶠ z in 𝓝[U] w', f z ∈ closedBall (F w) (ε / 2) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds w' (show (0 : ℝ) < δ / 2 by linarith))]
      with z hzU hzb
    refine mem_closedBall.mpr (hclose hzU ?_).le
    calc dist z w ≤ dist z w' + dist w' w := dist_triangle z w' w
      _ < δ / 2 + δ / 2 := add_lt_add (mem_ball.mp hzb) hw'd
      _ = δ := by ring
  have hlim : F w' ∈ closedBall (F w) (ε / 2) :=
    isClosed_closedBall.mem_of_tendsto (hF w' hw') hmem
  exact lt_of_le_of_lt (mem_closedBall.mp hlim) (by linarith)

/-- **The extension criterion for the boundary correspondence.** A continuous function on an open
`U` with bounded image whose cluster set at each boundary point has at most one element extends
continuously to `closure U`.

This is the form in which Carathéodory's theorem (layer **L5**) is applied: the geometric
hypothesis on `frontier U` is used only to check that the boundary cluster sets are singletons, and
this theorem converts that check into the continuous extension that
`Conformal/BoundaryCorrespondence.lean` turns into a homeomorphism of the closures. No cluster-set
hypothesis is needed at the *interior* points of `U`, where continuity already makes the cluster
set the singleton `{f w}`.

Holomorphy is not among the hypotheses because the proof does not use it; the conformal content
sits in the companion `TauCeti.clusterSetOn_subset_frontier_image`, which says the boundary values
produced here land on `frontier (f '' U)`. -/
theorem exists_continuousOn_closure_eqOn (hUo : IsOpen U) (hfc : ContinuousOn f U)
    (hfb : Bornology.IsBounded (f '' U))
    (hsub : ∀ w ∈ frontier U, (clusterSetOn f U w).Subsingleton) :
    ∃ F : ℂ → ℂ, ContinuousOn F (closure U) ∧ EqOn F f U := by
  have hK : IsCompact (closure (f '' U)) := hfb.isCompact_closure
  have hfK : MapsTo f U (closure (f '' U)) := fun z hz => subset_closure ⟨z, hz, rfl⟩
  -- At an interior point continuity already supplies the limit.
  have hlim : ∀ w ∈ U, Tendsto f (𝓝[U] w) (𝓝 (f w)) := fun w hw => hfc w hw
  have hall : ∀ w ∈ closure U, ∃ v, Tendsto f (𝓝[U] w) (𝓝 v) := by
    intro w hw
    by_cases hwU : w ∈ U
    · exact ⟨f w, hlim w hwU⟩
    · exact exists_tendsto_of_subsingleton hK hfK hw
        (hsub w (by rw [hUo.frontier_eq]; exact ⟨hw, hwU⟩))
  choose! F hF using hall
  refine ⟨F, continuousOn_closure_of_forall_tendsto hF, fun w hw => ?_⟩
  haveI : (𝓝[U] w).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (subset_closure hw)
  exact tendsto_nhds_unique (hF w (subset_closure hw)) (hlim w hw)

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
