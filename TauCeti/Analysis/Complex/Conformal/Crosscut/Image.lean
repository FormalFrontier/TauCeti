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
# How a circular crosscut splits the image of a disc, and its boundary

`Conformal/Crosscut/Basic.lean` cuts a disc `ball c r` at a boundary point `ζ` by the circle
`sphere ζ ρ` and proves that the two sides `ball c r ∩ ball ζ ρ` and `ball c r \ closedBall ζ ρ`
are the two connected components of what is left. `Conformal/CutDiameter.lean` transports the
two sides to a conformal image and bounds their width by the width of the image crosscut together
with the boundary piece cut off. This file completes that picture on the image side: it splits
`frontier (f '' ball c r)`, identifies the middle piece of that splitting as the two ends of the
image crosscut, and supplies — from local connectedness of that frontier — a small connected
boundary set enclosing that middle piece.

## The decomposition

Write `Ω = f '' ball c r`, `A = f '' (ball c r ∩ ball ζ ρ)`, `B = f '' (ball c r \ closedBall ζ ρ)`
for the images of the two sides, and `γ = f '' (ball c r ∩ sphere ζ ρ)` for the image crosscut, `f`
being holomorphic and injective on the disc. Then `Ω = A ∪ γ ∪ B`
(`TauCeti.image_ball_eq_union_image_crosscut`), and the frontier of a union is covered by the
frontiers of its parts, so a frontier point of `Ω` is a frontier point of `A`, a frontier point of
`B`, or an adherent point of `γ`:

> `frontier Ω = frontier Ω ∩ frontier A ∪ frontier Ω ∩ closure γ ∪ frontier Ω ∩ frontier B`

(`TauCeti.frontier_image_ball_eq_union`). This is the sense in which a crosscut *cuts the image
boundary in two*: the two boundary pieces `frontier Ω ∩ frontier A` and `frontier Ω ∩ frontier B`
cover `frontier Ω` apart from a middle piece no wider than the image crosscut itself
(`TauCeti.diam_frontier_inter_closure_image_ball_inter_sphere_le`), which by the length–area
estimate of `Conformal/ShortCrosscut.lean` can be made as small as desired.

## The middle piece, and the connected boundary set enclosing it

The middle piece is not merely small, it is *exactly the two ends of the image crosscut*
(`TauCeti.frontier_inter_closure_image_ball_inter_sphere_eq_biUnion_clusterSetOn`):

> `frontier Ω ∩ closure γ = ⋃ e ∈ sphere c r ∩ sphere ζ ρ, clusterSetOn f S e`

for `S = ball c r ∩ sphere ζ ρ` the crosscut itself, the index set being its two endpoints
(`TauCeti.sphere_inter_sphere_eq_pair_circleMap`). The equality itself allows the two cluster sets
to be empty; as soon as the image crosscut `γ` is bounded each of them is nonempty
(`TauCeti.nonempty_clusterSetOn_ball_inter_sphere`) and in fact a continuum
(`TauCeti.isConnected_clusterSetOn_ball_inter_sphere`), and then the crosscut clings to the boundary
of the image at *each* of its ends and the middle piece is where those two ends sit.

Both inclusions come from the same source. The closure of an image crosscut is the image crosscut
together with its two end cluster sets
(`TauCeti.closure_image_ball_inter_sphere_eq_union_biUnion_clusterSetOn`), because closing the open
arc `ball c r ∩ sphere ζ ρ` adds exactly the two points of `sphere c r ∩ sphere ζ ρ` and a
continuous `f` contributes only its own values over the arc itself. A value taken *on* the crosscut
lies in the open set `Ω`, which is disjoint from `frontier Ω`, so the middle piece can only consist
of end cluster values; conversely each end cluster value lies on `frontier Ω`, since a conformal
map is proper (`TauCeti.clusterSetOn_subset_frontier_image`), and is adherent to `γ` by
construction.

What this does *not* say is that the two ends are joined: the identification is of the middle piece
with the union of two cluster sets, not with a connected subset of `frontier Ω` running between
them.

That nonemptiness is what the enclosure theorem consumes. If `frontier Ω` is uniformly locally
connected — which by `TauCeti.IsCompact.isUniformlyLocallyConnected` is exactly local
connectedness, `frontier Ω` being compact — then for every `ε > 0` there is a single `δ > 0`,
independent of the
boundary point `ζ` and of the crosscut radius `ρ`, such that an image crosscut of diameter less than
`δ` has its whole middle piece enclosed in a *connected* subset of `frontier Ω` of diameter at most
`ε` (`TauCeti.exists_isConnected_subset_frontier_image_ball_of_diam_lt`), the general enclosure
statement `TauCeti.IsUniformlyLocallyConnected.exists_isConnected_superset` applied to the middle
piece. This is where the local connectedness of `∂Ω` that `Conformal/CutDiameter.lean` names as one
of its two geometric inputs enters, the other being the length–area estimate.

What is **not** proved here, and is what still separates layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md` from its milestone, is that the resulting connected set
encloses the boundary piece: that `frontier Ω ∩ frontier A` is contained in it together with the
image crosscut. Classically that is a separation argument about the closed curve formed by the image
crosscut and the boundary set, and no part of it is claimed below.

## Generality

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0–L6, everything here is stated for maps of `ℂ`. The two inputs that
are not about conformality are stated at their own generality elsewhere: `TauCeti.diam_frontier`
for an arbitrary real normed space and `TauCeti.IsUniformlyLocallyConnected` for an arbitrary
pseudometric space.

## Main results

* `TauCeti.image_ball_eq_union_image_crosscut` — the image of the disc is the union of the images
  of the two sides of a crosscut and of the crosscut itself.
* `TauCeti.frontier_image_ball_subset_union` and `TauCeti.frontier_image_ball_eq_union` — a
  crosscut cuts the boundary of the image into two pieces and a middle piece adherent to the image
  crosscut.
* `TauCeti.closure_image_ball_inter_sphere_eq_union_biUnion_clusterSetOn` — the closure of an image
  crosscut is the image crosscut together with the cluster sets at its two endpoints.
* `TauCeti.nonempty_clusterSetOn_ball_inter_sphere` and
  `TauCeti.isConnected_clusterSetOn_ball_inter_sphere` — each of those two end cluster sets is
  nonempty once the image of the crosscut is bounded, and connected once `f` is in addition
  continuous along the crosscut.
* `TauCeti.frontier_inter_closure_image_ball_inter_sphere_eq_biUnion_clusterSetOn` — the middle
  piece is *exactly* the union of the two end cluster sets, its one-sided inclusion being
  `TauCeti.clusterSetOn_ball_inter_sphere_subset_frontier_inter_closure_image`.
* `TauCeti.diam_frontier_inter_closure_image_ball_inter_sphere_le` and
  `TauCeti.nonempty_frontier_inter_closure_image_ball_inter_sphere` — the middle piece is nonempty
  and no wider than the image crosscut.
* `TauCeti.exists_isConnected_subset_frontier_image_ball_of_diam_lt` — a uniformly locally
  connected image boundary encloses the middle piece of every short image crosscut in a small
  connected boundary set, at a rate independent of the boundary point and the crosscut radius.

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

variable {f : ℂ → ℂ} {c ζ e : ℂ} {r ρ : ℝ}

/-! ## The three pieces of the image -/

/-- **A circular crosscut splits the image of a disc into three pieces**: the images of the two
sides and the image crosscut. This is `TauCeti.sdiff_sphere_eq_inter_ball_union_sdiff_closedBall` —
the corresponding identity in the disc — pushed forward, and needs nothing of `f`. -/
theorem image_ball_eq_union_image_crosscut (f : ℂ → ℂ) (c ζ : ℂ) (r ρ : ℝ) :
    f '' ball c r =
      f '' (ball c r ∩ ball ζ ρ) ∪ f '' (ball c r ∩ sphere ζ ρ) ∪
        f '' (ball c r \ closedBall ζ ρ) := by
  rw [← image_union, ← image_union]
  congr 1
  rw [union_right_comm, ← sdiff_sphere_eq_inter_ball_union_sdiff_closedBall, sdiff_union_inter]

/-! ## The crosscut cuts the boundary of the image in two -/

/-- **The boundary of the image of a disc is covered by the boundaries of the two sides of a
crosscut together with the closure of the image crosscut.**

Like the decomposition itself this needs nothing of `f`: the image of the disc is the union of the
three pieces by `TauCeti.image_ball_eq_union_image_crosscut`, the frontier of a union is covered by
the frontiers of the two parts by `frontier_union_subset`, and the frontier of the image crosscut
lies in its closure. -/
theorem frontier_image_ball_subset_union (f : ℂ → ℂ) (c ζ : ℂ) (r ρ : ℝ) :
    frontier (f '' ball c r) ⊆
      frontier (f '' (ball c r ∩ ball ζ ρ)) ∪ closure (f '' (ball c r ∩ sphere ζ ρ)) ∪
        frontier (f '' (ball c r \ closedBall ζ ρ)) := by
  have hunion : ∀ s t : Set ℂ, frontier (s ∪ t) ⊆ frontier s ∪ frontier t := fun s t =>
    (frontier_union_subset s t).trans (union_subset_union inter_subset_left inter_subset_right)
  rw [image_ball_eq_union_image_crosscut f c ζ r ρ]
  exact (hunion _ _).trans (union_subset_union
    ((hunion _ _).trans (union_subset_union subset_rfl frontier_subset_closure)) subset_rfl)

/-- **A circular crosscut cuts the boundary of the image into two pieces and a middle piece.** The
equality form of `TauCeti.frontier_image_ball_subset_union`: `frontier (f '' ball c r)` is the union
of the two *boundary pieces* the crosscut determines — its intersections with the frontiers of the
images of the two sides — and of the part of it adherent to the image crosscut, which
`TauCeti.diam_frontier_inter_closure_image_ball_inter_sphere_le` shows to be no wider than the
image crosscut itself. -/
theorem frontier_image_ball_eq_union (f : ℂ → ℂ) (c ζ : ℂ) (r ρ : ℝ) :
    frontier (f '' ball c r) =
      frontier (f '' ball c r) ∩ frontier (f '' (ball c r ∩ ball ζ ρ)) ∪
        frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)) ∪
        frontier (f '' ball c r) ∩ frontier (f '' (ball c r \ closedBall ζ ρ)) := by
  rw [← inter_union_distrib_left, ← inter_union_distrib_left]
  exact (inter_eq_left.mpr (frontier_image_ball_subset_union f c ζ r ρ)).symm

/-! ## The two ends of the image crosscut -/

/-- **The closure of an image crosscut is the image crosscut together with its two end cluster
sets.** The crosscut `ball c r ∩ sphere ζ ρ` is an open arc whose closure adds exactly the two
points of `sphere c r ∩ sphere ζ ρ`
(`TauCeti.closure_ball_inter_sphere`, `TauCeti.sphere_inter_sphere_eq_pair_circleMap`), and a
continuous `f` contributes nothing new over the arc itself, so all of `closure (f '' arc)` beyond
`f '' arc` is cluster values at the two ends. The cluster-set content is
`TauCeti.closure_image_eq_image_union_biUnion_clusterSetOn`, applied to the arc, whose frontier is
its whole closure because an arc has empty interior in the plane.

Only continuity along the arc is used; `f` need be neither holomorphic nor injective, and the
image need not be bounded. -/
theorem closure_image_ball_inter_sphere_eq_union_biUnion_clusterSetOn
    (hfc : ContinuousOn f (ball c r ∩ sphere ζ ρ)) (hζ : dist ζ c = r) (hρ : 0 < ρ)
    (hρr : ρ < 2 * r) :
    closure (f '' (ball c r ∩ sphere ζ ρ)) =
      f '' (ball c r ∩ sphere ζ ρ) ∪
        ⋃ e ∈ sphere c r ∩ sphere ζ ρ, clusterSetOn f (ball c r ∩ sphere ζ ρ) e := by
  have hcl : closure (ball c r ∩ sphere ζ ρ) = closedBall c r ∩ sphere ζ ρ :=
    closure_ball_inter_sphere hζ hρ hρr
  have hcomp : IsCompact (closure (ball c r ∩ sphere ζ ρ)) := by
    rw [hcl]
    exact (isCompact_closedBall c r).inter_right isClosed_sphere
  -- the crosscut is an arc, so it has empty interior and its frontier is its whole closure
  have hint : interior (ball c r ∩ sphere ζ ρ) = ∅ := by
    rw [← subset_empty_iff, ← interior_sphere ζ hρ.ne']
    exact interior_mono inter_subset_right
  have hfr : frontier (ball c r ∩ sphere ζ ρ) =
      (ball c r ∩ sphere ζ ρ) ∪ (sphere c r ∩ sphere ζ ρ) := by
    rw [← closure_sdiff_interior, hint, sdiff_empty, hcl, ← ball_union_sphere,
      union_inter_distrib_right]
  have harc : ⋃ w ∈ ball c r ∩ sphere ζ ρ, clusterSetOn f (ball c r ∩ sphere ζ ρ) w
      ⊆ f '' (ball c r ∩ sphere ζ ρ) := by
    refine iUnion₂_subset fun w hw => ?_
    rw [clusterSetOn_eq_singleton_of_continuousWithinAt hw (hfc w hw)]
    exact singleton_subset_iff.mpr (mem_image_of_mem f hw)
  rw [closure_image_eq_image_union_biUnion_clusterSetOn hcomp hfc, hfr, biUnion_union,
    ← union_assoc, union_eq_self_of_subset_right harc]

/-- **An end cluster set of an image crosscut lies in the middle piece.** For `f` holomorphic and
injective on `ball c r` and an endpoint `e` of a circular crosscut, every value `f` clusters at
along the crosscut as `e` is approached is a boundary value of the image adherent to the image
crosscut.

Both halves are already available: the cluster set along the crosscut is contained in the cluster
set along the whole disc, which `TauCeti.clusterSetOn_subset_frontier_image` — properness of a
conformal map — puts on `frontier (f '' ball c r)`; and cluster values are adherent to the image
of the approach set by `TauCeti.clusterSetOn_subset_closure_image`. -/
theorem clusterSetOn_ball_inter_sphere_subset_frontier_inter_closure_image
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r)) (hr : 0 < r)
    (he : e ∈ sphere c r ∩ sphere ζ ρ) :
    clusterSetOn f (ball c r ∩ sphere ζ ρ) e ⊆
      frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)) := by
  refine subset_inter (fun v hv => ?_) fun v hv => clusterSetOn_subset_closure_image hv
  refine clusterSetOn_subset_frontier_image isOpen_ball hd hinj ?_
    (clusterSetOn_mono inter_subset_left hv)
  rw [frontier_ball c hr.ne']
  exact he.1

/-- **Each end of a circular crosscut carries a cluster value.** The crosscut is adherent to each
of its two endpoints and `f` is confined along it to the compact
`closure (f '' (ball c r ∩ sphere ζ ρ))`, so the cluster set there is nonempty; only the image of
the crosscut need be bounded, and no holomorphy is needed. -/
theorem nonempty_clusterSetOn_ball_inter_sphere (hb : IsBounded (f '' (ball c r ∩ sphere ζ ρ)))
    (hζ : dist ζ c = r) (hρ : 0 < ρ) (hρr : ρ < 2 * r) (he : e ∈ sphere c r ∩ sphere ζ ρ) :
    (clusterSetOn f (ball c r ∩ sphere ζ ρ) e).Nonempty := by
  refine clusterSetOn_nonempty hb.isCompact_closure
    (fun z hz => subset_closure (mem_image_of_mem f hz)) ?_
  rw [closure_ball_inter_sphere hζ hρ hρr]
  exact ⟨sphere_subset_closedBall he.1, he.2⟩

/-- **Each end of an image crosscut is a continuum.** For `f` continuous along a genuine circular
crosscut and with bounded image *of the crosscut*, the cluster set at either endpoint is nonempty
and connected; it is compact by `TauCeti.isCompact_clusterSetOn_of_isBounded`. This is the
Collingwood–Lohwater continuum theorem `TauCeti.isConnected_clusterSetOn`, whose local hypothesis —
that arbitrarily small neighbourhoods of the endpoint meet the crosscut in a preconnected set — is
exactly `TauCeti.isPreconnected_ball_inter_sphere_inter_ball`, a crosscut spanning less than a half
turn and so meeting each ball centred on it in a subarc. -/
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

/-- **The middle piece is exactly the two end cluster sets of the image crosscut.** For `f`
holomorphic and injective on `ball c r` and a genuine circular crosscut at a boundary point `ζ`,

> `frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ))`
> `= ⋃ e ∈ sphere c r ∩ sphere ζ ρ, clusterSetOn f (ball c r ∩ sphere ζ ρ) e`,

the index set being the two endpoints of the crosscut by
`TauCeti.sphere_inter_sphere_eq_pair_circleMap`. So the part of the image boundary that the
crosscut clings to is not merely small: it is the union of the cluster sets at the two ends. The
image of the crosscut is not assumed bounded here, so the equality by itself leaves those two
cluster sets possibly empty; add that boundedness and each of them is nonempty by
`TauCeti.nonempty_clusterSetOn_ball_inter_sphere`, which is what a small connected boundary set
enclosing the middle piece —
`TauCeti.exists_isConnected_subset_frontier_image_ball_of_diam_lt` — has to *join*.

One inclusion is `TauCeti.clusterSetOn_ball_inter_sphere_subset_frontier_inter_closure_image`. For
the other, `TauCeti.closure_image_ball_inter_sphere_eq_union_biUnion_clusterSetOn` splits a point
of the closure of the image crosscut into a value on the crosscut and a cluster value at an end,
and a value on the crosscut lies in the *open* image `f '' ball c r`, which is disjoint from its
own frontier. -/
theorem frontier_inter_closure_image_ball_inter_sphere_eq_biUnion_clusterSetOn
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r)) (hζ : dist ζ c = r)
    (hρ : 0 < ρ) (hρr : ρ < 2 * r) :
    frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)) =
      ⋃ e ∈ sphere c r ∩ sphere ζ ρ, clusterSetOn f (ball c r ∩ sphere ζ ρ) e := by
  have hr : 0 < r := by linarith
  refine subset_antisymm ?_ (iUnion₂_subset fun e he =>
    clusterSetOn_ball_inter_sphere_subset_frontier_inter_closure_image hd hinj hr he)
  rintro v ⟨hvfr, hvcl⟩
  rw [closure_image_ball_inter_sphere_eq_union_biUnion_clusterSetOn
    (hd.continuousOn.mono inter_subset_left) hζ hρ hρr] at hvcl
  refine hvcl.resolve_left fun hv => ?_
  have hopen : IsOpen (f '' ball c r) :=
    isOpen_image_of_differentiableOn_of_injOn isOpen_ball hd hinj
  exact (hopen.frontier_eq ▸ hvfr).2 (image_mono inter_subset_left hv)

/-- **The middle piece is no wider than the image crosscut.** It is contained in the closure of the
image crosscut, and closing a set does not change its diameter. -/
theorem diam_frontier_inter_closure_image_ball_inter_sphere_le (hb : IsBounded (f '' ball c r))
    (ζ : ℂ) (ρ : ℝ) :
    diam (frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)))
      ≤ diam (f '' (ball c r ∩ sphere ζ ρ)) := by
  have harc : IsBounded (f '' (ball c r ∩ sphere ζ ρ)) := hb.subset (image_mono inter_subset_left)
  calc diam (frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)))
      ≤ diam (closure (f '' (ball c r ∩ sphere ζ ρ))) := diam_mono inter_subset_right harc.closure
    _ = diam (f '' (ball c r ∩ sphere ζ ρ)) := diam_closure _

/-- **The middle piece is nonempty**: for `f` holomorphic and injective on `ball c r` with bounded
image, and a genuine circular crosscut at a boundary point `ζ`, the set
`frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ))` has a point. So the image
crosscut does cling to the boundary of the image, and — by
`TauCeti.frontier_inter_closure_image_ball_inter_sphere_eq_biUnion_clusterSetOn` and
`TauCeti.nonempty_clusterSetOn_ball_inter_sphere` — at *each* of its two ends.

The crosscut has an endpoint on `sphere c r`, and the cluster set of `f` along the crosscut there
is nonempty and contained in the middle piece. -/
theorem nonempty_frontier_inter_closure_image_ball_inter_sphere
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r)) (hζ : dist ζ c = r) (hρ : 0 < ρ) (hρr : ρ < 2 * r) :
    (frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ))).Nonempty := by
  have hr : 0 < r := by linarith
  -- one of the two endpoints of the crosscut
  have hemem : circleMap ζ ρ ((c - ζ).arg - Real.arccos (ρ / (2 * r)))
      ∈ sphere c r ∩ sphere ζ ρ := by
    rw [sphere_inter_sphere_eq_pair_circleMap hζ hρ hρr]
    exact Or.inl rfl
  obtain ⟨v, hv⟩ :=
    nonempty_clusterSetOn_ball_inter_sphere (hb.subset (image_mono inter_subset_left))
      hζ hρ hρr hemem
  exact ⟨v, clusterSetOn_ball_inter_sphere_subset_frontier_inter_closure_image hd hinj hr hemem hv⟩

/-! ## The small connected set enclosing the middle piece -/

/-- **A uniformly locally connected image boundary encloses the middle piece of every short image
crosscut in a small connected boundary set.** For `f` holomorphic and injective on `ball c r` with
bounded image and `frontier (f '' ball c r)` uniformly locally connected, every `ε > 0` admits a
single `δ > 0` — independent of the boundary point `ζ` and of the crosscut radius `ρ` — such that
an image crosscut of diameter less than `δ` has its middle piece contained in a connected subset of
`frontier (f '' ball c r)` of diameter at most `ε`.

This is where the local connectedness of `∂Ω` that
`TauCeti.exists_continuousOn_closure_eqOn_of_forall_exists_diam_union_le` needs enters, the other
of its two geometric inputs being the length–area estimate
`TauCeti.exists_diam_image_ball_inter_sphere_le`. It does not by itself discharge that criterion,
whose enclosing set has to contain the whole boundary piece
`frontier (f '' ball c r) ∩ frontier (f '' (ball c r ∩ ball ζ ρ))` and not only the middle piece.

Everything topological is in `TauCeti.IsUniformlyLocallyConnected.exists_isConnected_superset`, the
statement that a uniformly locally connected set encloses each of its small subsets in a small
connected subset. What remains is that the middle piece is a subset of `frontier (f '' ball c r)`
that is bounded, nonempty by
`TauCeti.nonempty_frontier_inter_closure_image_ball_inter_sphere`, and of diameter less than `δ` by
`TauCeti.diam_frontier_inter_closure_image_ball_inter_sphere_le`. -/
theorem exists_isConnected_subset_frontier_image_ball_of_diam_lt
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r))
    (hulc : IsUniformlyLocallyConnected (frontier (f '' ball c r))) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ζ : ℂ, dist ζ c = r → ∀ ρ : ℝ, 0 < ρ → ρ < 2 * r →
      diam (f '' (ball c r ∩ sphere ζ ρ)) < δ →
        ∃ S ⊆ frontier (f '' ball c r), IsConnected S ∧
          frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)) ⊆ S ∧ diam S ≤ ε := by
  obtain ⟨δ, hδ, hencl⟩ := hulc.exists_isConnected_superset hε
  refine ⟨δ, hδ, fun ζ hζ ρ hρ hρr hdiam => ?_⟩
  refine hencl _ inter_subset_left
    (((hb.subset (image_mono inter_subset_left)).closure).subset inter_subset_right)
    (nonempty_frontier_inter_closure_image_ball_inter_sphere hd hinj hb hζ hρ hρr) ?_
  exact lt_of_le_of_lt (diam_frontier_inter_closure_image_ball_inter_sphere_le hb ζ ρ) hdiam

end TauCeti
