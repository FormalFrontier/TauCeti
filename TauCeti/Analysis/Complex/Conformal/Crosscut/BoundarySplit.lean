/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.ClusterSet
import TauCeti.Analysis.Normed.Module.Ball.Cut

/-!
# The two boundary pieces of a crosscut, and choosing between them

Write `Ω = f '' U` for the image of an open `U ⊆ ℂ` under a conformal map, and cut `U` by a circle
`sphere ζ ρ` into the near side `U ∩ ball ζ ρ`, the far side `U \ closedBall ζ ρ` and the cut
`U ∩ sphere ζ ρ` itself, with images `A`, `B` and `γ`. `Conformal/Crosscut/Image.lean` observes that
`frontier Ω` is then covered by `frontier A`, `frontier B` and `closure γ`, and studies the *middle
piece* `frontier Ω ∩ closure γ`. This file studies the other two pieces,

> `P = frontier Ω ∩ closure A` and `Q = frontier Ω ∩ closure B`,

and proves two facts about them that the Carathéodory boundary correspondence — layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md` — needs of the cut:

* **the two pieces already cover, with no leftover**: `frontier Ω = P ∪ Q`
  (`TauCeti.frontier_image_eq_union_inter_closure_image`). There is no third piece to account for,
  because the cut clings to *both* sides — in a normed space the cutting sphere is adherent to the
  ball it bounds and to the exterior of the closed ball alike — so the middle piece lies inside
  `P ∩ Q` rather than beside them;
* **a preconnected complement chooses between them**: if a set `S ⊆ ℂ` contains `P ∩ Q` and
  `frontier Ω \ S` is preconnected, then `P ⊆ S` or `Q ⊆ S`
  (`TauCeti.subset_or_subset_of_isPreconnected_frontier_image_sdiff`).

## What is settled here, and what is not

Both facts are proved outright: no statement below takes an unproved input as a hypothesis, and
none asks for a Jordan curve theorem, for local connectedness of `Ω` at its boundary, or for an
estimate on `f`. The dichotomy is a statement about an arbitrary set `S`, and its hypotheses —
that `S` swallows `P ∩ Q` and that what is left of the image boundary is preconnected — are
conditions on `S`, discharged by whoever supplies one.

What is *not* settled here is the *choice of boundary arc* that `Conformal/Crosscut/Jordan.lean`
and `Conformal/Crosscut/Arc.lean` both name as the step left open, namely which arc of `frontier Ω`
a short image crosscut cuts off. Feeding a boundary arc to the dichotomy needs `P ∩ Q` to be no
larger than the middle piece, `frontier Ω ∩ closure A ∩ closure B ⊆ closure γ` — the assertion that
the two sides of the crosscut cling to the image boundary only along the crosscut. That is a
planar-separation statement this development does not have, and it is a prerequisite to be proved
on its own, not something to assume; so no theorem here is stated in a shape that presumes it.

The two pieces are stated with `closure A` rather than `frontier A`, the shape the crosscut
criterion `TauCeti.exists_continuousOn_closure_eqOn_of_forall_exists_diam_union_le` of
`Conformal/CutDiameter.lean` consumes being the latter. A consumer converts between the two with
`TauCeti.frontier_inter_closure_eq_frontier_inter_frontier` of `TauCeti/Topology/Frontier.lean`,
applied to `Set.image_mono Set.inter_subset_left` on the near side and to
`Set.image_mono Set.sdiff_subset` on the far side: on the frontier of a set, adherence to a subset
is membership of that subset's frontier, for any subset and with no hypothesis on `f`. The closure
shape is used throughout because it needs nothing more than continuity of `f`.

## Which piece is which

Each piece captures the boundary behaviour of `f` over its own side of the cutting circle: a value
`f` clusters at over a boundary point of `U` strictly inside the circle lies in `P`, and one over a
boundary point strictly outside lies in `Q`
(`TauCeti.clusterSetOn_subset_frontier_inter_closure_image_inter_ball` and its far-side companion).
Together with the surjectivity of the boundary correspondence
(`TauCeti.biUnion_clusterSetOn_eq_frontier_image`) this says which part of `frontier Ω` each piece
is responsible for, and it is how a caller who has confined one piece to a small `S` tells which of
the two alternatives of the dichotomy it is in.

## Generality

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0–L6, everything below is stated for maps of `ℂ` on an arbitrary open
`U`, as in `Conformal/CutDiameter.lean`; nothing asks `U ∩ sphere ζ ρ` to be a crosscut, or `ζ` to
lie on `frontier U`. The metric step that never mentions a map — that both sides of a cut cling to
the cutting sphere — is stated for a seminormed real vector space in
`TauCeti/Analysis/Normed/Module/Ball/Cut.lean` and consumed here. Only the cluster-set lemmas ask
`f` to be holomorphic and injective; the splitting and the dichotomy need no more than continuity,
and the radius is unrestricted apart from `ρ ≠ 0`, which is what makes the cutting sphere adherent
to the ball.

## Main results

* `TauCeti.image_inter_sphere_subset_closure_image_inter_ball` and
  `TauCeti.image_inter_sphere_subset_closure_image_sdiff_closedBall` — the image of the cut is
  adherent to the images of both sides, and hence
  `TauCeti.frontier_inter_closure_image_inter_sphere_subset_inter` — the middle piece lies in both
  boundary pieces.
* `TauCeti.frontier_image_subset_union_closure_image` and
  `TauCeti.frontier_image_eq_union_inter_closure_image` — **the splitting**: the two boundary
  pieces cover the boundary of the image, with no third piece.
* `TauCeti.clusterSetOn_subset_frontier_inter_closure_image_inter_ball` and
  `TauCeti.clusterSetOn_subset_frontier_inter_closure_image_sdiff_closedBall` — each piece captures
  the values `f` clusters at over the boundary points of `U` on its own side of the circle.
* `TauCeti.subset_or_subset_of_isPreconnected_frontier_image_sdiff` — **the dichotomy**: a set
  containing the intersection of the two pieces and with preconnected complement in the image
  boundary contains one of the two pieces.

## Coordination with upstream Mathlib

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself, and the
pinned Mathlib has no boundary correspondence for conformal maps. So this file is new Lean
formalization rather than a temporary shim. It consumes, through
`Conformal/ClusterSet.lean`, the L0–L3 shim
`TauCeti.isOpen_image_of_differentiableOn_of_injOn`, to be refactored onto Mathlib's open mapping
API once the upstream work lands.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2–2.3.
* P. L. Duren, *Univalent Functions*, Ch. 3.
-/

public section

namespace TauCeti

open Metric Set Topology

variable {f : ℂ → ℂ} {U : Set ℂ} {ζ w : ℂ} {ρ : ℝ}

/-! ## The cut clings to both sides -/

/-- **The image of the cut is adherent to the image of the near side.** For `f` continuous on an
open `U` and a cutting circle of nonzero radius, `f '' (U ∩ sphere ζ ρ)` lies in the closure of
`f '' (U ∩ ball ζ ρ)`.

The metric content is `TauCeti.inter_sphere_subset_closure_inter_ball`: the part of the cutting
sphere inside an open set is adherent to the near side of the cut. Continuity of `f` along the near
side carries that adherence to the images, by `ContinuousWithinAt.mem_closure_image`. Neither
holomorphy nor injectivity is used. -/
theorem image_inter_sphere_subset_closure_image_inter_ball (hUo : IsOpen U)
    (hfc : ContinuousOn f U) (hρ : ρ ≠ 0) :
    f '' (U ∩ sphere ζ ρ) ⊆ closure (f '' (U ∩ ball ζ ρ)) := by
  rintro _ ⟨z, hz, rfl⟩
  exact ((hfc z hz.1).mono inter_subset_left).mem_closure_image
    (inter_sphere_subset_closure_inter_ball hUo ζ hρ hz)

/-- **The image of the cut is adherent to the image of the far side.** The mirror of
`TauCeti.image_inter_sphere_subset_closure_image_inter_ball`, on
`TauCeti.inter_sphere_subset_closure_sdiff_closedBall`: in a normed space the cutting sphere is
adherent to the exterior of the closed ball as well as to the open one, so the cut is separated from
neither side. -/
theorem image_inter_sphere_subset_closure_image_sdiff_closedBall (hUo : IsOpen U)
    (hfc : ContinuousOn f U) (hρ : ρ ≠ 0) :
    f '' (U ∩ sphere ζ ρ) ⊆ closure (f '' (U \ closedBall ζ ρ)) := by
  rintro _ ⟨z, hz, rfl⟩
  exact ((hfc z hz.1).mono sdiff_subset).mem_closure_image
    (inter_sphere_subset_closure_sdiff_closedBall hUo ζ hρ hz)

/-- **The middle piece belongs to both boundary pieces.** The part
`frontier (f '' U) ∩ closure (f '' (U ∩ sphere ζ ρ))` of the image boundary that the image of the
cut clings to lies in `P` and in `Q` alike.

This is why the covering below has no leftover: the middle piece of
`Conformal/Crosscut/Image.lean` is not a third piece beside `P` and `Q` but a part of their
intersection, and it is the part that `TauCeti.diam_frontier_inter_closure_image_inter_sphere_le`
and the length--area method make small. -/
theorem frontier_inter_closure_image_inter_sphere_subset_inter (hUo : IsOpen U)
    (hfc : ContinuousOn f U) (hρ : ρ ≠ 0) :
    frontier (f '' U) ∩ closure (f '' (U ∩ sphere ζ ρ)) ⊆
      frontier (f '' U) ∩ closure (f '' (U ∩ ball ζ ρ)) ∩
        (frontier (f '' U) ∩ closure (f '' (U \ closedBall ζ ρ))) := by
  refine fun p hp => ⟨⟨hp.1, ?_⟩, hp.1, ?_⟩
  · exact closure_minimal (image_inter_sphere_subset_closure_image_inter_ball hUo hfc hρ)
      isClosed_closure hp.2
  · exact closure_minimal (image_inter_sphere_subset_closure_image_sdiff_closedBall hUo hfc hρ)
      isClosed_closure hp.2

/-! ## The splitting of the image boundary -/

/-- **The boundary of the image is covered by the closures of the images of the two sides.** No
third set is needed: the image of the cut is adherent to both sides, so its closure adds nothing.

The decomposition `U = (U ∩ ball ζ ρ) ∪ (U \ closedBall ζ ρ) ∪ (U ∩ sphere ζ ρ)` is
`TauCeti.sdiff_sphere_eq_inter_ball_union_sdiff_closedBall` together with `Set.sdiff_union_inter`;
taking images and closures, `frontier (f '' U) ⊆ closure (f '' U)` splits into the three closures,
and the third is absorbed by
`TauCeti.image_inter_sphere_subset_closure_image_inter_ball`. -/
theorem frontier_image_subset_union_closure_image (hUo : IsOpen U) (hfc : ContinuousOn f U)
    (hρ : ρ ≠ 0) :
    frontier (f '' U) ⊆
      closure (f '' (U ∩ ball ζ ρ)) ∪ closure (f '' (U \ closedBall ζ ρ)) := by
  have himg : f '' U =
      f '' (U ∩ ball ζ ρ) ∪ f '' (U \ closedBall ζ ρ) ∪ f '' (U ∩ sphere ζ ρ) :=
    image_eq_image_inter_ball_union_image_sdiff_closedBall_union_image_inter_sphere f
  have hγ : closure (f '' (U ∩ sphere ζ ρ)) ⊆ closure (f '' (U ∩ ball ζ ρ)) :=
    closure_minimal (image_inter_sphere_subset_closure_image_inter_ball hUo hfc hρ) isClosed_closure
  refine frontier_subset_closure.trans ?_
  rw [himg, closure_union, closure_union]
  exact union_subset (union_subset subset_union_left subset_union_right)
    (hγ.trans subset_union_left)

/-- **A circle splits the boundary of the image in two.** The two boundary pieces

> `P = frontier (f '' U) ∩ closure (f '' (U ∩ ball ζ ρ))` and
> `Q = frontier (f '' U) ∩ closure (f '' (U \ closedBall ζ ρ))`

cover `frontier (f '' U)` exactly, with the middle piece lying in both by
`TauCeti.frontier_inter_closure_image_inter_sphere_subset_inter`.

`Conformal/Crosscut/Image.lean` records the weaker covering by `frontier A`, `closure γ` and
`frontier B` as elementary set theory that nothing there consumes; the sharpening to a two-piece
cover is what the dichotomy below runs on, a third piece being exactly what would defeat a
connectivity argument. -/
theorem frontier_image_eq_union_inter_closure_image (hUo : IsOpen U) (hfc : ContinuousOn f U)
    (hρ : ρ ≠ 0) :
    frontier (f '' U) = frontier (f '' U) ∩ closure (f '' (U ∩ ball ζ ρ)) ∪
      frontier (f '' U) ∩ closure (f '' (U \ closedBall ζ ρ)) := by
  rw [← inter_union_distrib_left]
  exact (inter_eq_left.mpr (frontier_image_subset_union_closure_image hUo hfc hρ)).symm

/-! ## Which piece a boundary point falls in -/

/-- **A boundary value reached from inside the cutting circle lies in the near piece.** For `f`
holomorphic and injective on an open `U` and a point `w` of `frontier U` strictly inside
`sphere ζ ρ`, every value `f` clusters at when `w` is approached along `U` lies in
`frontier (f '' U) ∩ closure (f '' (U ∩ ball ζ ρ))`.

The cluster set is local (`TauCeti.clusterSetOn_inter_of_mem_nhds`), so the approach set may be cut
down to `U ∩ ball ζ ρ`, the trace on `U` of a neighbourhood of `w`; cluster values along a set are
adherent to its image, and they lie on `frontier (f '' U)` by properness of a conformal map. -/
theorem clusterSetOn_subset_frontier_inter_closure_image_inter_ball (hUo : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U) (hw : w ∈ frontier U) (hwρ : dist w ζ < ρ) :
    clusterSetOn f U w ⊆ frontier (f '' U) ∩ closure (f '' (U ∩ ball ζ ρ)) := by
  refine subset_inter (clusterSetOn_subset_frontier_image hUo hd hinj hw) ?_
  rw [← clusterSetOn_inter_of_mem_nhds (f := f) (U := U) (isOpen_ball.mem_nhds (mem_ball.mpr hwρ))]
  exact clusterSetOn_subset_closure_image

/-- **A boundary value reached from outside the cutting circle lies in the far piece.** The mirror
of `TauCeti.clusterSetOn_subset_frontier_inter_closure_image_inter_ball`: for `w` on `frontier U`
strictly outside `sphere ζ ρ`, the complement of `closedBall ζ ρ` is the neighbourhood of `w` the
approach set is cut down to.

Together with the surjectivity of the boundary correspondence
(`TauCeti.biUnion_clusterSetOn_eq_frontier_image`) the two statements say which part of
`frontier (f '' U)` each piece is responsible for: everything reached from the far arc of
`frontier U` lies in the far piece, so a caller who knows two such values far apart knows that the
far piece is not the small one. -/
theorem clusterSetOn_subset_frontier_inter_closure_image_sdiff_closedBall (hUo : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U) (hw : w ∈ frontier U) (hwρ : ρ < dist w ζ) :
    clusterSetOn f U w ⊆ frontier (f '' U) ∩ closure (f '' (U \ closedBall ζ ρ)) := by
  refine subset_inter (clusterSetOn_subset_frontier_image hUo hd hinj hw) ?_
  have hmem : (closedBall ζ ρ)ᶜ ∈ 𝓝 w :=
    isClosed_closedBall.isOpen_compl.mem_nhds (by simpa [mem_closedBall] using not_le.mpr hwρ)
  rw [sdiff_eq, ← clusterSetOn_inter_of_mem_nhds (f := f) (U := U) hmem]
  exact clusterSetOn_subset_closure_image

/-! ## Choosing between the two pieces -/

/-- **A preconnected complement chooses between the two boundary pieces.** If a set `S` contains the
intersection `P ∩ Q` of the two pieces and `frontier (f '' U) \ S` is preconnected, then `P ⊆ S` or
`Q ⊆ S`.

It is pure connectivity: the two pieces are closed and cover `frontier (f '' U)` by
`TauCeti.frontier_image_eq_union_inter_closure_image`, so they cover `frontier (f '' U) \ S`, on
which they are disjoint because their intersection was put into `S`;
`isPreconnected_iff_subset_of_disjoint_closed` therefore confines that difference to one of them,
and the *other* piece is then trapped inside `S`.

Both hypotheses are conditions on `S` alone, so a caller supplies them for the `S` it has in hand;
a small `S` then makes one of the two pieces small. Nothing here says which sets `S` a crosscut
admits: that needs `P ∩ Q` to be no larger than the middle piece
(`TauCeti.frontier_inter_closure_image_inter_sphere_subset_inter` gives only the other inclusion),
which is the planar-separation prerequisite this development does not yet have. -/
theorem subset_or_subset_of_isPreconnected_frontier_image_sdiff (hUo : IsOpen U)
    (hfc : ContinuousOn f U) (hρ : ρ ≠ 0) {S : Set ℂ}
    (hS : frontier (f '' U) ∩ closure (f '' (U ∩ ball ζ ρ)) ∩
        closure (f '' (U \ closedBall ζ ρ)) ⊆ S)
    (hpre : IsPreconnected (frontier (f '' U) \ S)) :
    frontier (f '' U) ∩ closure (f '' (U ∩ ball ζ ρ)) ⊆ S ∨
      frontier (f '' U) ∩ closure (f '' (U \ closedBall ζ ρ)) ⊆ S := by
  have hcov : frontier (f '' U) \ S ⊆ frontier (f '' U) ∩ closure (f '' (U ∩ ball ζ ρ)) ∪
      frontier (f '' U) ∩ closure (f '' (U \ closedBall ζ ρ)) := by
    intro p hp
    rw [← frontier_image_eq_union_inter_closure_image hUo hfc hρ]
    exact hp.1
  have hdisj : (frontier (f '' U) \ S) ∩
      (frontier (f '' U) ∩ closure (f '' (U ∩ ball ζ ρ)) ∩
        (frontier (f '' U) ∩ closure (f '' (U \ closedBall ζ ρ)))) = ∅ := by
    refine eq_empty_of_forall_notMem fun p hp => ?_
    exact hp.1.2 (hS ⟨hp.2.1, hp.2.2.2⟩)
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hpre _ _
    (isClosed_frontier.inter isClosed_closure) (isClosed_frontier.inter isClosed_closure)
    hcov hdisj with h | h
  · refine Or.inr fun p hp => ?_
    by_contra hpS
    exact hpS (hS ⟨h ⟨hp.1, hpS⟩, hp.2⟩)
  · refine Or.inl fun p hp => ?_
    by_contra hpS
    exact hpS (hS ⟨hp, (h ⟨hp.1, hpS⟩).2⟩)

end TauCeti
