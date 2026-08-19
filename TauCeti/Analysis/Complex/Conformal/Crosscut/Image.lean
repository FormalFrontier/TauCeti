/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.CutDiameter
public import TauCeti.Topology.UniformlyLocallyConnected
import TauCeti.Analysis.Complex.Conformal.ClusterSet
import TauCeti.Analysis.Complex.Conformal.Crosscut.Endpoints

/-!
# How a circle splits the image of a domain, and its boundary

`Conformal/Crosscut/Basic.lean` cuts a disc `ball c r` at a boundary point `ζ` by the circle
`sphere ζ ρ` and proves that the two sides `ball c r ∩ ball ζ ρ` and `ball c r \ closedBall ζ ρ`
are the two connected components of what is left; for `0 < ρ < 2 * r` the piece
`ball c r ∩ sphere ζ ρ` left over is then a genuine *crosscut*, the single arc that
`Conformal/Crosscut/Endpoints.lean` describes. `Conformal/CutDiameter.lean` transports such a cut
of an *arbitrary* open `U` to a conformal image and bounds the width of the two sides by the width
of the image of the cut together with the boundary piece cut off. This file completes that picture
on the image side: it splits `frontier (f '' U)`, identifies the middle piece of that splitting as
a union of cluster sets of `f` along the cut, and supplies — from local connectedness of that
frontier — a small connected boundary set enclosing that middle piece.

Nothing below assumes that `U ∩ sphere ζ ρ` *is* a crosscut. For an arbitrary `U` it may be empty,
disconnected, or the whole circle, and it need not separate `U`; the statements are about that
intersection as it stands, and the words *crosscut*, *arc* and *endpoint* are used only where a
hypothesis puts them there — for a disc, in `TauCeti.isConnected_clusterSetOn_ball_inter_sphere`.

## The decomposition

Write `Ω = f '' U`, `A = f '' (U ∩ ball ζ ρ)`, `B = f '' (U \ closedBall ζ ρ)` for the images of
the parts of `U` inside and outside the circle, and `γ = f '' (U ∩ sphere ζ ρ)` for the image of the
part on it, `f` being holomorphic and injective on the open set `U`. The three parts cover `U` —
the two sides cover `U \ sphere ζ ρ` by
`TauCeti.sdiff_sphere_eq_inter_ball_union_sdiff_closedBall` — so `Ω = A ∪ γ ∪ B`, and the frontier
of a union is covered by the frontiers of its parts, so a frontier point of `Ω` is a frontier point
of `A`, a frontier point of `B`, or an adherent point of `γ`:

> `frontier Ω ⊆ frontier A ∪ closure γ ∪ frontier B`

This is the sense in which the circle *cuts the image boundary in two*: the two boundary pieces
`frontier Ω ∩ frontier A` and `frontier Ω ∩ frontier B` cover `frontier Ω` apart from the *middle
piece* `frontier Ω ∩ closure γ`, which for a bounded `γ` — `Ω` itself need not be bounded — is no
wider than `γ` itself (`TauCeti.diam_frontier_inter_closure_image_inter_sphere_le`) and by the
length–area estimate of `Conformal/ShortCrosscut.lean` can be made as small as desired. That
covering is elementary set theory and is not recorded as a lemma: nothing below consumes it, every
result here being about the middle piece itself. The covering that *is* consumed runs the other
way, bounding the frontier of one side by the cut and the frontier of the whole
(`TauCeti.frontier_image_inter_ball_subset` of `Conformal/CutDiameter.lean`, whose topological core
`TauCeti.frontier_image_subset_image_union_frontier_image` is in `TauCeti/Topology/Frontier.lean`).

## The middle piece, and the connected boundary set enclosing it

The middle piece is not merely small, it is *exactly the values `f` clusters at along the cut, at
the points of `frontier U` on the circle*
(`TauCeti.frontier_inter_closure_image_inter_sphere_eq_biUnion_clusterSetOn`):

> `frontier Ω ∩ closure γ = ⋃ e ∈ frontier U ∩ sphere ζ ρ, clusterSetOn f S e`

for `S = U ∩ sphere ζ ρ` the cut itself. For a crosscut of a disc the index set is the two
endpoints of the crosscut arc (`TauCeti.sphere_inter_sphere_eq_pair_circleMap`); for a general
domain it is the whole trace of `frontier U` on the cutting circle, which is where `S` can run out
of the domain, and the cluster sets at points of it not adherent to `S` are empty. The equality
itself allows all of those cluster sets to be empty; as soon as `γ` is bounded, each point of the
index set adherent to `S` carries one (`TauCeti.clusterSetOn_nonempty`), and for a crosscut of a
disc each is in fact a continuum (`TauCeti.isConnected_clusterSetOn_ball_inter_sphere`), so `γ`
clings to the boundary of the image wherever the cut leaves the domain, and the middle piece is
where it does so.

Both inclusions come from the same source. The closure of `γ` is `γ` together with those cluster
sets (`TauCeti.closure_image_inter_sphere_eq_union_biUnion_clusterSetOn`), because closing
`U ∩ sphere ζ ρ` adds only points of `frontier U` on the circle — that intersection has empty
interior in the plane, so its frontier is its whole closure — and a continuous `f` contributes only
its own values over the cut itself. A value taken *on* the cut lies in the open set `Ω`, which is
disjoint from `frontier Ω`, so the middle piece can only consist of cluster values; conversely each
cluster value lies on `frontier Ω`, since a conformal map is proper
(`TauCeti.clusterSetOn_subset_frontier_image`), and is adherent to `γ` by construction.

What this does *not* say is that those cluster sets are joined to one another: the identification is
of the middle piece with a union of cluster sets, not with a connected subset of `frontier Ω`
running between them.

That nonemptiness is what the enclosure theorem consumes. If `frontier Ω` is uniformly locally
connected — which by `TauCeti.IsCompact.isUniformlyLocallyConnected` is exactly local
connectedness, `frontier Ω` being compact — then for every `ε > 0` there is a single `δ > 0`,
independent of the centre `ζ` and the radius `ρ` of the cutting circle, such that a `γ` of diameter
less than `δ` has its whole middle piece enclosed in a *connected* subset of `frontier Ω`
of diameter at most `ε` (`TauCeti.exists_isConnected_subset_frontier_image_of_diam_lt`), the general
enclosure statement `TauCeti.IsUniformlyLocallyConnected.exists_isConnected_superset` applied to the
middle piece. This is where the local connectedness of `∂Ω` that `Conformal/CutDiameter.lean` names
as one of its two geometric inputs enters, the other being the length–area estimate.

What is **not** proved here, and is what still separates layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md` from its milestone, is that the resulting connected set
encloses the boundary piece: that `frontier Ω ∩ frontier A` is contained in it together with `γ`.
Classically that is a separation argument about the closed curve formed by the image of the cut and
the boundary set, and no part of it is claimed below.

## Generality

The domain `U` is an arbitrary open set rather than a disc, matching
`Conformal/CutDiameter.lean`, whose criterion
`TauCeti.exists_continuousOn_closure_eqOn_of_forall_exists_diam_union_le` these results feed: a
disc-shaped input cannot be handed to a criterion stated for a general domain without first
specialising the criterion, and the Carathéodory correspondence is a statement about a Jordan
domain and the disc it is mapped from at once, so both directions of it are served only by the
general form. Nothing below uses the shape of `U`; the two endpoints of a crosscut of a disc become
the trace of `frontier U` on the cutting circle, and the disc hypotheses `dist ζ c = r` and
`ρ < 2 * r`, which made the cut a crosscut spanning less than a half turn, disappear. The one
statement that does use the disc is the continuum theorem
`TauCeti.isConnected_clusterSetOn_ball_inter_sphere`, whose input is that small balls meet the
crosscut in a subarc.

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0–L6, everything here is stated for maps of `ℂ`. The inputs that are
not about conformality are stated at their own generality elsewhere: `TauCeti.diam_frontier` for an
arbitrary real normed space, `TauCeti.IsUniformlyLocallyConnected` for an arbitrary pseudometric
space, and the splitting of the domain by the cutting sphere
(`TauCeti.sdiff_sphere_eq_inter_ball_union_sdiff_closedBall`) for an arbitrary set in an arbitrary
pseudometric space, in `TauCeti/Topology/MetricSpace/Cut.lean`.

## Main results

* `TauCeti.closure_image_inter_sphere_eq_union_biUnion_clusterSetOn` — the closure of the image of
  the cut is that image together with the cluster sets of `f` along it.
* `TauCeti.closure_image_inter_sphere_subset_union_frontier_image` — an image crosscut is
  relatively closed in the image domain, and
  `TauCeti.disjoint_image_of_subset_closure_image_inter_sphere_union_frontier_image`
  — so a set disjoint from the crosscut has image disjoint from anything on its closure and the
  image boundary.
* `TauCeti.isConnected_clusterSetOn_ball_inter_sphere` — at an endpoint of a crosscut of a disc a
  cluster set is a continuum once `f` is continuous along the crosscut with bounded image; its
  nonemptiness for a general domain is the generic `TauCeti.clusterSetOn_nonempty`, applied to the
  cut.
* `TauCeti.frontier_inter_closure_image_inter_sphere_eq_biUnion_clusterSetOn` — the middle
  piece is *exactly* the union of those cluster sets, its one-sided inclusion being
  `TauCeti.clusterSetOn_inter_sphere_subset_frontier_inter_closure_image`.
* `TauCeti.diam_frontier_inter_closure_image_inter_sphere_le` and
  `TauCeti.nonempty_frontier_inter_closure_image_inter_sphere` — for a bounded image of the cut,
  the middle piece is nonempty and no wider than that image. For a disc,
  `TauCeti.nonempty_frontier_ball_inter_closure_ball_inter_sphere` in
  `Conformal/Crosscut/Endpoints.lean` discharges the nonemptiness hypothesis of the second.
* `TauCeti.exists_isConnected_subset_frontier_image_of_diam_lt` — a uniformly locally connected
  image boundary encloses the middle piece of every small cut in a small connected boundary set, at
  a rate independent of the centre and radius of the cutting circle.

## Coordination with upstream Mathlib

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself, and the
pinned Mathlib has no boundary correspondence for conformal maps. So this file is new Lean
formalization rather than a temporary shim.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2–2.3.
* P. L. Duren, *Univalent Functions*, Ch. 3.
-/

public section

namespace TauCeti

open Bornology Complex Filter Metric Set Topology

variable {f : ℂ → ℂ} {U K V : Set ℂ} {c ζ e : ℂ} {r ρ : ℝ}

/-! ## Where the cut leaves the domain -/

/-- The frontier of the intersection of a set with a circle is contained in that intersection
together with the points of the frontier of the set lying on the circle. This is
`frontier_inter_subset` with the circle's own frontier and closure — both the circle itself —
filled in, and `closure U` split as `U ∪ frontier U`.

Kept private: it is the elementary topological step of
`TauCeti.closure_image_inter_sphere_eq_union_biUnion_clusterSetOn`, phrased for the one shape of
cut this file uses. -/
private lemma frontier_inter_sphere_subset (U : Set ℂ) (ζ : ℂ) (ρ : ℝ) :
    frontier (U ∩ sphere ζ ρ) ⊆ U ∩ sphere ζ ρ ∪ frontier U ∩ sphere ζ ρ := by
  refine (frontier_inter_subset U (sphere ζ ρ)).trans ?_
  rw [isClosed_sphere.closure_eq, frontier_sphere' ζ ρ, closure_eq_self_union_frontier,
    union_inter_distrib_right]
  exact union_subset subset_union_right subset_rfl

/-- **The closure of the image of `U ∩ sphere ζ ρ` is that image together with the cluster sets of
`f` at the points of `frontier U` on the circle.** The set `U ∩ sphere ζ ρ` has empty interior in
the plane, so its frontier is its whole closure, and closing it adds only points of `frontier U`
lying on the circle; a continuous `f` contributes nothing new over `U ∩ sphere ζ ρ` itself, so all
of `closure (f '' (U ∩ sphere ζ ρ))` beyond `f '' (U ∩ sphere ζ ρ)` is cluster values there. The
cluster-set content is `TauCeti.closure_image_eq_image_union_biUnion_clusterSetOn`, applied to
`U ∩ sphere ζ ρ`, whose closure is compact because the circle is.

Only continuity of `f` on `U ∩ sphere ζ ρ` is used; `f` need be neither holomorphic nor injective,
`U` need not be open, the image need not be bounded, and the radius is unrestricted. Points of the
index set not adherent to `U ∩ sphere ζ ρ` contribute an empty cluster set, so nothing is claimed
about how many of them are met. -/
theorem closure_image_inter_sphere_eq_union_biUnion_clusterSetOn
    (hfc : ContinuousOn f (U ∩ sphere ζ ρ)) :
    closure (f '' (U ∩ sphere ζ ρ)) =
      f '' (U ∩ sphere ζ ρ) ∪
        ⋃ e ∈ frontier U ∩ sphere ζ ρ, clusterSetOn f (U ∩ sphere ζ ρ) e := by
  have hcomp : IsCompact (closure (U ∩ sphere ζ ρ)) :=
    (isCompact_sphere ζ ρ).of_isClosed_subset isClosed_closure
      (closure_minimal inter_subset_right isClosed_sphere)
  refine subset_antisymm ?_
    (union_subset subset_closure
      (iUnion₂_subset fun _ _ => clusterSetOn_subset_closure_image))
  rw [closure_image_eq_image_union_biUnion_clusterSetOn hcomp hfc]
  refine union_subset subset_union_left (iUnion₂_subset fun w hw => ?_)
  rcases frontier_inter_sphere_subset U ζ ρ hw with hwcut | hwend
  · rw [clusterSetOn_eq_singleton_of_continuousWithinAt hwcut (hfc w hwcut)]
    exact singleton_subset_iff.mpr (subset_union_left (mem_image_of_mem f hwcut))
  · exact subset_union_right.trans' (subset_biUnion_of_mem hwend)

/-- **A cluster set along `U ∩ sphere ζ ρ` lies in the middle piece.** For `f` holomorphic and
injective on an open `U` and a point `e` of `frontier U`, every value `f` clusters at along
`U ∩ sphere ζ ρ` as `e` is approached is a boundary value of the image adherent to
`f '' (U ∩ sphere ζ ρ)`.

Both halves are already available: the cluster set along `U ∩ sphere ζ ρ` is contained in the
cluster set along the whole domain, which `TauCeti.clusterSetOn_subset_frontier_image` — properness
of a conformal map — puts on `frontier (f '' U)`; and cluster values are adherent to the image of
the approach set by `TauCeti.clusterSetOn_subset_closure_image`. -/
theorem clusterSetOn_inter_sphere_subset_frontier_inter_closure_image (hUo : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U) (he : e ∈ frontier U) :
    clusterSetOn f (U ∩ sphere ζ ρ) e ⊆
      frontier (f '' U) ∩ closure (f '' (U ∩ sphere ζ ρ)) :=
  subset_inter
    (fun _ hv => clusterSetOn_subset_frontier_image hUo hd hinj he
      (clusterSetOn_mono inter_subset_left hv))
    fun _ hv => clusterSetOn_subset_closure_image hv

/-- **Taking the closure of an image crosscut adds only boundary points of the image domain.** For
`f` holomorphic and injective on an open `U`, a point adherent to the image crosscut
`f '' (U ∩ sphere ζ ρ)` either lies on it or lies on `frontier (f '' U)`: the image crosscut is
relatively closed in the image domain.

The closure decomposition is
`TauCeti.closure_image_inter_sphere_eq_union_biUnion_clusterSetOn`, and
`TauCeti.clusterSetOn_inter_sphere_subset_frontier_inter_closure_image` puts every added cluster
value on `frontier (f '' U)`. -/
theorem closure_image_inter_sphere_subset_union_frontier_image (hUo : IsOpen U)
    (hd : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) :
    closure (f '' (U ∩ sphere ζ ρ)) ⊆ f '' (U ∩ sphere ζ ρ) ∪ frontier (f '' U) := by
  rw [closure_image_inter_sphere_eq_union_biUnion_clusterSetOn
    (hd.continuousOn.mono inter_subset_left)]
  exact union_subset_union_right _ (iUnion₂_subset fun _ he =>
    (clusterSetOn_inter_sphere_subset_frontier_inter_closure_image hUo hd hinj he.1).trans
      inter_subset_left)

/-- **A set following neither side of a crosscut has image disjoint from its closed image and the
image boundary.** If `V ⊆ U` is disjoint from `U ∩ sphere ζ ρ`, then `f '' V` avoids every `K`
contained in the closed image crosscut and `frontier (f '' U)`. Injectivity separates it from the
crosscut, relative closedness handles the closure, and openness of `f '' U` handles the image
boundary. -/
theorem disjoint_image_of_subset_closure_image_inter_sphere_union_frontier_image
    (hUo : IsOpen U) (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U) (hVU : V ⊆ U)
    (hV : Disjoint V (U ∩ sphere ζ ρ))
    (hK : K ⊆ closure (f '' (U ∩ sphere ζ ρ)) ∪ frontier (f '' U)) : Disjoint (f '' V) K := by
  have hΩo : IsOpen (f '' U) := isOpen_image_of_differentiableOn_of_injOn hUo hd hinj
  have hcross : Disjoint (f '' V) (f '' (U ∩ sphere ζ ρ)) :=
    hV.image hinj hVU inter_subset_left
  refine Set.disjoint_left.mpr fun w hw hwK => ?_
  rcases hK hwK with h | h
  · exact Set.disjoint_left.mp hcross hw
      (((closure_image_inter_sphere_subset_union_frontier_image hUo hd hinj) h).resolve_right
        fun hfr =>
        (hΩo.inter_frontier_eq.subset ⟨image_mono hVU hw, hfr⟩).elim)
  · exact (hΩo.inter_frontier_eq.subset ⟨image_mono hVU hw, h⟩).elim

/-- **Each end of an image crosscut of a disc is a continuum.** For `f` continuous along a genuine
circular crosscut of a disc and with bounded image *of the crosscut*, the cluster set at either
endpoint is nonempty and connected; it is compact by
`TauCeti.isCompact_clusterSetOn_of_isBounded`. This is the Collingwood–Lohwater continuum theorem
`TauCeti.isConnected_clusterSetOn`, whose local hypothesis — that arbitrarily small neighbourhoods
of the endpoint meet the crosscut in a preconnected set — is exactly
`TauCeti.isPreconnected_ball_inter_sphere_inter_ball`, a crosscut spanning less than a half turn and
so meeting each ball centred on it in a subarc. That input is what keeps this statement about a
disc while its neighbours above are about an arbitrary domain: a general `U ∩ sphere ζ ρ` may meet
a small ball in many pieces. -/
theorem isConnected_clusterSetOn_ball_inter_sphere
    (hfc : ContinuousOn f (ball c r ∩ sphere ζ ρ)) (hb : IsBounded (f '' (ball c r ∩ sphere ζ ρ)))
    (hζ : dist ζ c = r) (hρ : 0 < ρ) (hρr : ρ < 2 * r) (he : e ∈ sphere c r ∩ sphere ζ ρ) :
    IsConnected (clusterSetOn f (ball c r ∩ sphere ζ ρ) e) := by
  have hecl : e ∈ closedBall c r ∩ sphere ζ ρ := ⟨sphere_subset_closedBall he.1, he.2⟩
  refine isConnected_clusterSetOn_of_isBounded hfc hb
    (by rw [closure_ball_inter_sphere hζ hρ hρr]; exact hecl) fun s hs => ?_
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
  exact ⟨ball e δ, ball_mem_nhds e hδ, hball,
    isPreconnected_ball_inter_sphere_inter_ball hζ hρ hρr hecl δ⟩

/-! ## The middle piece -/

/-- **The middle piece is exactly the cluster sets along `U ∩ sphere ζ ρ`.** For `f` holomorphic
and injective on an open `U`,

> `frontier (f '' U) ∩ closure (f '' (U ∩ sphere ζ ρ))`
> `= ⋃ e ∈ frontier U ∩ sphere ζ ρ, clusterSetOn f (U ∩ sphere ζ ρ) e`,

the index set being, for a crosscut of a disc, the two endpoints of the crosscut arc
(`TauCeti.sphere_inter_sphere_eq_pair_circleMap`). So the part of the image boundary that
`f '' (U ∩ sphere ζ ρ)` clings to is not merely small: it is the union of those cluster sets. That
image is not assumed bounded here, so the equality by itself leaves the cluster sets possibly
empty; add that boundedness and every point of the index set adherent to `U ∩ sphere ζ ρ` carries
one by `TauCeti.clusterSetOn_nonempty`, which is what a small connected boundary set enclosing the
middle piece — `TauCeti.exists_isConnected_subset_frontier_image_of_diam_lt` — has to *join*.

One inclusion is `TauCeti.clusterSetOn_inter_sphere_subset_frontier_inter_closure_image`. For the
other, `TauCeti.closure_image_inter_sphere_eq_union_biUnion_clusterSetOn` splits a point of
`closure (f '' (U ∩ sphere ζ ρ))` into a value taken on `U ∩ sphere ζ ρ` and a cluster value, and a
value taken there lies in the *open* image `f '' U`, which is disjoint from its own frontier. -/
theorem frontier_inter_closure_image_inter_sphere_eq_biUnion_clusterSetOn (hUo : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U) :
    frontier (f '' U) ∩ closure (f '' (U ∩ sphere ζ ρ)) =
      ⋃ e ∈ frontier U ∩ sphere ζ ρ, clusterSetOn f (U ∩ sphere ζ ρ) e := by
  refine subset_antisymm ?_ (iUnion₂_subset fun e he =>
    clusterSetOn_inter_sphere_subset_frontier_inter_closure_image hUo hd hinj he.1)
  rintro v ⟨hvfr, hvcl⟩
  rw [closure_image_inter_sphere_eq_union_biUnion_clusterSetOn
    (hd.continuousOn.mono inter_subset_left)] at hvcl
  refine hvcl.resolve_left fun hv => ?_
  have hopen : IsOpen (f '' U) := isOpen_image_of_differentiableOn_of_injOn hUo hd hinj
  exact (hopen.frontier_eq ▸ hvfr).2 (image_mono inter_subset_left hv)

/-- **The middle piece is no wider than the image of `U ∩ sphere ζ ρ`.** It is contained in the
closure of that image, and closing a set does not change its diameter. Only that image is asked to
be bounded; the image of `U` itself need not be. -/
theorem diam_frontier_inter_closure_image_inter_sphere_le
    (hb : IsBounded (f '' (U ∩ sphere ζ ρ))) :
    diam (frontier (f '' U) ∩ closure (f '' (U ∩ sphere ζ ρ)))
      ≤ diam (f '' (U ∩ sphere ζ ρ)) :=
  calc diam (frontier (f '' U) ∩ closure (f '' (U ∩ sphere ζ ρ)))
      ≤ diam (closure (f '' (U ∩ sphere ζ ρ))) := diam_mono inter_subset_right hb.closure
    _ = diam (f '' (U ∩ sphere ζ ρ)) := diam_closure _

/-- **The middle piece is nonempty**: for `f` holomorphic and injective on an open `U`, a bounded
image of `U ∩ sphere ζ ρ` and a point `e` of `frontier U` adherent to `U ∩ sphere ζ ρ`, the set
`frontier (f '' U) ∩ closure (f '' (U ∩ sphere ζ ρ))` has a point. So the image of `U ∩ sphere ζ ρ`
does cling to the boundary of the image, and — by
`TauCeti.frontier_inter_closure_image_inter_sphere_eq_biUnion_clusterSetOn` — it does so at each
such `e`.

The cluster set of `f` along `U ∩ sphere ζ ρ` at `e` is nonempty and contained in the middle
piece. As for the diameter bound, only the image of `U ∩ sphere ζ ρ` is asked to be bounded. -/
theorem nonempty_frontier_inter_closure_image_inter_sphere (hUo : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U) (hb : IsBounded (f '' (U ∩ sphere ζ ρ)))
    (he : e ∈ frontier U ∩ closure (U ∩ sphere ζ ρ)) :
    (frontier (f '' U) ∩ closure (f '' (U ∩ sphere ζ ρ))).Nonempty := by
  obtain ⟨v, hv⟩ := clusterSetOn_nonempty hb.isCompact_closure
    (fun _ hz => subset_closure (mem_image_of_mem f hz)) he.2
  exact ⟨v, clusterSetOn_inter_sphere_subset_frontier_inter_closure_image hUo hd hinj he.1 hv⟩

/-! ## The small connected set enclosing the middle piece -/

/-- **A uniformly locally connected image boundary encloses the middle piece of every small cut in
a small connected boundary set.** For `f` holomorphic and injective on an open `U` with bounded
image and `frontier (f '' U)` uniformly locally connected, every `ε > 0` admits a single `δ > 0` —
independent of the centre `ζ` and the radius `ρ` of the cutting circle — such that whenever
`f '' (U ∩ sphere ζ ρ)` has diameter less than `δ`, the middle piece is contained in a connected
subset of `frontier (f '' U)` of diameter at most `ε`. The cut is asked to reach `frontier U`,
which for a circular crosscut of a disc is
`TauCeti.nonempty_frontier_ball_inter_closure_ball_inter_sphere`; a cut missing `frontier U`
altogether has an empty middle piece and nothing to enclose.

This is where the local connectedness of `∂Ω` that
`TauCeti.exists_continuousOn_closure_eqOn_of_forall_exists_diam_union_le` needs enters, the other
of its two geometric inputs being the length–area estimate
`TauCeti.exists_diam_image_ball_inter_sphere_le`. It does not by itself discharge that criterion,
whose enclosing set has to contain the whole boundary piece
`frontier (f '' U) ∩ frontier (f '' (U ∩ ball ζ ρ))` and not only the middle piece.

Everything topological is in `TauCeti.IsUniformlyLocallyConnected.exists_isConnected_superset`, the
statement that a uniformly locally connected set encloses each of its small subsets in a small
connected subset. What remains is that the middle piece is a subset of `frontier (f '' U)` that is
bounded, nonempty by `TauCeti.nonempty_frontier_inter_closure_image_inter_sphere`, and of diameter
less than `δ` by `TauCeti.diam_frontier_inter_closure_image_inter_sphere_le`. -/
theorem exists_isConnected_subset_frontier_image_of_diam_lt (hUo : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U) (hb : IsBounded (f '' U))
    (hulc : IsUniformlyLocallyConnected (frontier (f '' U))) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ζ : ℂ, ∀ ρ : ℝ, (frontier U ∩ closure (U ∩ sphere ζ ρ)).Nonempty →
      diam (f '' (U ∩ sphere ζ ρ)) < δ →
        ∃ S ⊆ frontier (f '' U), IsConnected S ∧
          frontier (f '' U) ∩ closure (f '' (U ∩ sphere ζ ρ)) ⊆ S ∧ diam S ≤ ε := by
  obtain ⟨δ, hδ, hencl⟩ := hulc.exists_isConnected_superset hε
  refine ⟨δ, hδ, fun ζ ρ ⟨w, hw⟩ hdiam => ?_⟩
  have hcut : IsBounded (f '' (U ∩ sphere ζ ρ)) := hb.subset (image_mono inter_subset_left)
  exact hencl _ inter_subset_left (hcut.closure.subset inter_subset_right)
    (nonempty_frontier_inter_closure_image_inter_sphere hUo hd hinj hcut hw)
    (lt_of_le_of_lt (diam_frontier_inter_closure_image_inter_sphere_le hcut) hdiam)

end TauCeti
