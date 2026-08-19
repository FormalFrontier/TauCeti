/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Crosscut.Image
public import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Topology.MetricSpace.Cut

/-!
# Which side of a crosscut a curve encloses

Write `Ω = f '' U` for the image of an open `U ⊆ ℂ` under a conformal map, cut at `ζ` by the circle
`sphere ζ ρ` into the near side `U ∩ ball ζ ρ`, the far side `U \ closedBall ζ ρ` and the crosscut
`U ∩ sphere ζ ρ`, with images `A`, `B` and `γ`. `Conformal/CutDiameter.lean` bounds the width of a
side by *anything containing its whole frontier*; this file bounds it instead by *anything that cuts
it off from infinity*, that is, by a bounded `K` with `A ⊆ filledHull K`. The filled hull — `K`
together with the bounded connected components of `Kᶜ` — is `TauCeti.filledHull` of
`TauCeti/Topology/FilledHull.lean`, and `TauCeti.diam_le_diam_of_subset_filledHull` is what makes
the enclosure a width bound.

The point of the change is which datum has to be produced. The frontier route asks for the piece
`frontier Ω ∩ frontier A` of the image boundary that the near side clings to, and asks it to be
small — but *which* piece of the image boundary that is, is exactly the choice
`Conformal/Crosscut/BoundarySplit.lean` leaves open. The enclosure route asks only that the near
side fall inside a small curve running along the crosscut, and `Conformal/Crosscut/Jordan.lean` and
`Conformal/Crosscut/Arc.lean` already build such curves: a short image crosscut closes up into an
arbitrarily small Jordan curve
(`TauCeti.exists_isJordanCurve_superset_closure_image_ball_inter_sphere_diam_le`).

## The two sides against one curve

Everything below runs on a bounded `K` lying on the closed image crosscut and the image boundary,

> `f '' (U ∩ sphere ζ ρ) ⊆ K ⊆ closure (f '' (U ∩ sphere ζ ρ)) ∪ frontier Ω`,

the shape in which a curve joining the two ends of the image crosscut along `frontier Ω` arrives.
The first inclusion is what makes `K` cut `Ω`; the second is what keeps `K` off the two sides, by
`TauCeti.closure_image_inter_sphere_subset`: the image crosscut is *relatively closed* in the image
domain, being its complement in the two open image sides, so its closure adds only boundary points.
Three facts follow, and together they say that such a `K` encloses exactly one of the two sides.

* **An enclosed side is trapped**: each side is preconnected and disjoint from `K`, so if it meets
  `filledHull K` it lies inside (`TauCeti.image_subset_filledHull_of_nonempty_inter`) and is
  therefore no wider than `K`.
* **Not both sides**: if `K` encloses both, it encloses the whole image domain
  (`TauCeti.image_subset_filledHull`), so a `K` narrower than one side cannot enclose that side.
* **At least one side**, as soon as some point of the image crosscut is a limit of points inside
  `K` (`TauCeti.nonempty_inter_filledHull_or_nonempty_inter_filledHull`): a point of the inside
  close enough to it lies in the image domain and off `K`, hence on one of the two sides.

Combining them, `TauCeti.image_inter_ball_subset_filledHull_of_diam_lt` puts the *near* side inside
`K` once `K` is narrower than the far side — the situation at a small crosscut radius, where the far
side is nearly all of `Ω`.

## What is assumed, and what remains

No theorem here assumes plane separation. The third fact above takes as a hypothesis that one
*given* point `p` of the image crosscut satisfies `p ∈ closure (filledHull K \ K)`, a property of
the set `K` at the point `p`; it is not an unproved theorem in disguise, and nothing else in the
file mentions the inside of `K` at all.

What that hypothesis costs, when `K` is a Jordan curve, is exactly the open frontier item recorded
in the roadmap section of `TauCeti/Topology/FilledHull.lean`: that every point of a Jordan curve is
a limit of points inside it, `J ⊆ closure (filledHull J \ J)`. So the effect of this file is to
reduce the remaining gap in the Jordan-domain case of the boundary correspondence to that single
statement about Jordan curves, with the conformal side of the argument discharged: given it at one
point of one small Jordan curve per crosscut, the last criterion below delivers the continuous
extension to the closure.

That the enclosure route asks for no more than the frontier route does is
`TauCeti.image_inter_ball_subset_filledHull_of_frontier_subset`: a boundary piece `E` enclosing
`frontier Ω ∩ frontier A` puts the near side inside `f '' (U ∩ sphere ζ ρ) ∪ E`, so the hypothesis
of the criterion below is implied by the hypothesis of the criterion of
`Conformal/CutDiameter.lean` with the same `E`.

## Main results

* `TauCeti.closure_image_inter_sphere_subset` — an image crosscut is relatively closed in the image
  domain, and `TauCeti.disjoint_image_of_disjoint_inter_sphere` — so a curve running along it and
  along the image boundary misses both image sides.
* `TauCeti.image_subset_filledHull_of_nonempty_inter` — an image side meeting the inside of such a
  curve lies inside it, and `TauCeti.image_subset_filledHull` — a curve enclosing both sides
  encloses the whole image domain.
* `TauCeti.nonempty_inter_filledHull_or_nonempty_inter_filledHull` — a curve with inside points next
  to the image crosscut encloses one of the two sides.
* `TauCeti.image_inter_ball_subset_filledHull_of_diam_lt` — such a curve, if narrower than the far
  side, encloses the *near* side.
* `TauCeti.image_inter_ball_subset_filledHull_of_frontier_subset` — the enclosure hypothesis is
  implied by the boundary-piece hypothesis of `Conformal/CutDiameter.lean`.
* `TauCeti.subsingleton_clusterSetOn_of_forall_exists_subset_filledHull`,
  `TauCeti.exists_tendsto_nhdsWithin_of_forall_exists_subset_filledHull` and
  `TauCeti.exists_continuousOn_closure_eqOn_of_forall_exists_subset_filledHull` — arbitrarily narrow
  enclosures of the cut-off pieces give the boundary limit and the continuous extension.

## Roadmap role

This advances layer **L5** of `TauCetiRoadmap/ConformalMapping/README.md`, the Jordan-domain case of
the Carathéodory boundary correspondence, whose remaining step is to show that a short image
crosscut cuts off a piece of small diameter. It is the consumption of the filled hull that
`TauCeti/Analysis/Normed/Module/FilledHull.lean` was built for and names in its roadmap section.

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, and Mathlib has no boundary correspondence for
conformal maps, so this is new Lean formalization rather than a temporary shim.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2–2.3.
* P. L. Duren, *Univalent Functions*, Ch. 3.
-/

public section

namespace TauCeti

open Bornology Complex Filter Metric Set Topology

variable {f : ℂ → ℂ} {U K V : Set ℂ} {ζ p : ℂ} {ρ : ℝ}

/-- The image of a cut domain, split into the two image sides and the image crosscut. -/
private theorem image_eq_union_sides_union_crosscut :
    f '' U = f '' (U ∩ ball ζ ρ) ∪ f '' (U \ closedBall ζ ρ) ∪ f '' (U ∩ sphere ζ ρ) := by
  rw [← image_union, ← image_union, ← eq_inter_ball_union_sdiff_closedBall_union_inter_sphere]

/-! ## The image crosscut is relatively closed in the image domain -/

/-- **Taking the closure of an image crosscut adds only boundary points of the image domain.** For
`f` holomorphic and injective on an open `U`, a point adherent to the image crosscut
`f '' (U ∩ sphere ζ ρ)` either lies on it or lies on `frontier (f '' U)`: the image crosscut is
relatively closed in the image domain.

Both halves are already available. The closure is the image crosscut together with the cluster sets
of `f` at the points of `frontier U` on the circle, by
`TauCeti.closure_image_inter_sphere_eq_union_biUnion_clusterSetOn`, and
`TauCeti.clusterSetOn_inter_sphere_subset_frontier_inter_closure_image` — properness of a conformal
map — puts each of those cluster sets on `frontier (f '' U)`. -/
theorem closure_image_inter_sphere_subset (hUo : IsOpen U) (hd : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) :
    closure (f '' (U ∩ sphere ζ ρ)) ⊆ f '' (U ∩ sphere ζ ρ) ∪ frontier (f '' U) := by
  rw [closure_image_inter_sphere_eq_union_biUnion_clusterSetOn
    (hd.continuousOn.mono inter_subset_left)]
  exact union_subset_union_right _ (iUnion₂_subset fun _ he =>
    (clusterSetOn_inter_sphere_subset_frontier_inter_closure_image hUo hd hinj he.1).trans
      inter_subset_left)

/-- **A curve running along the image crosscut and the image boundary misses every image side.**
If `V ⊆ U` is disjoint from the crosscut `U ∩ sphere ζ ρ`, then `f '' V` avoids every set `K`
sitting on the closed image crosscut and the boundary of the image domain: it avoids the image
crosscut by injectivity, the rest of its closure by
`TauCeti.closure_image_inter_sphere_subset`, and `frontier (f '' U)` because it lies in the open
set `f '' U`. Both sides of a crosscut are of this shape. -/
theorem disjoint_image_of_disjoint_inter_sphere (hUo : IsOpen U) (hd : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) (hVU : V ⊆ U) (hV : Disjoint V (U ∩ sphere ζ ρ))
    (hK : K ⊆ closure (f '' (U ∩ sphere ζ ρ)) ∪ frontier (f '' U)) : Disjoint (f '' V) K := by
  have hΩo : IsOpen (f '' U) := isOpen_image_of_differentiableOn_of_injOn hUo hd hinj
  have hcross : Disjoint (f '' V) (f '' (U ∩ sphere ζ ρ)) :=
    hV.image hinj hVU inter_subset_left
  refine Set.disjoint_left.mpr fun w hw hwK => ?_
  rcases hK hwK with h | h
  · exact Set.disjoint_left.mp hcross hw
      (((closure_image_inter_sphere_subset hUo hd hinj) h).resolve_right fun hfr =>
        (hΩo.inter_frontier_eq.subset ⟨image_mono hVU hw, hfr⟩).elim)
  · exact (hΩo.inter_frontier_eq.subset ⟨image_mono hVU hw, h⟩).elim

/-! ## An enclosed side is trapped, and narrow -/

/-- **An image side that meets the inside of such a curve lies inside it.** The side is
preconnected as a continuous image of a preconnected set and disjoint from `K` by
`TauCeti.disjoint_image_of_disjoint_inter_sphere`, so `TauCeti.IsPreconnected.subset_filledHull`
traps it in the bounded component of `Kᶜ` it meets. Instantiate `V` at `U ∩ ball ζ ρ` for the near
side and at `U \ closedBall ζ ρ` for the far side. -/
theorem image_subset_filledHull_of_nonempty_inter (hUo : IsOpen U) (hd : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) (hVU : V ⊆ U) (hV : Disjoint V (U ∩ sphere ζ ρ)) (hVc : IsPreconnected V)
    (hK : K ⊆ closure (f '' (U ∩ sphere ζ ρ)) ∪ frontier (f '' U))
    (hne : (f '' V ∩ filledHull K).Nonempty) : f '' V ⊆ filledHull K :=
  IsPreconnected.subset_filledHull (hVc.image f (hd.continuousOn.mono hVU))
    (disjoint_image_of_disjoint_inter_sphere hUo hd hinj hVU hV hK) hne

/-- **A curve enclosing both sides of a crosscut encloses the whole image domain.** The image
domain is the two image sides together with the image crosscut, and the image crosscut lies in `K`,
hence in its filled hull. Nothing is asked of `f`. -/
theorem image_subset_filledHull (hγ : f '' (U ∩ sphere ζ ρ) ⊆ K)
    (hA : f '' (U ∩ ball ζ ρ) ⊆ filledHull K)
    (hB : f '' (U \ closedBall ζ ρ) ⊆ filledHull K) : f '' U ⊆ filledHull K := by
  rw [image_eq_union_sides_union_crosscut (f := f) (U := U) (ζ := ζ) (ρ := ρ)]
  exact union_subset (union_subset hA hB) (hγ.trans subset_filledHull)

/-! ## At least one side is enclosed -/

/-- **A curve with a point of its inside next to the image crosscut encloses one of the two sides.**
If a point `p` of the image crosscut is a limit of points of `filledHull K \ K`, then such a point
`q` close enough to `p` lies in the open image domain; being off `K` it is off the image crosscut,
so it lies on one of the two image sides, and it lies in `filledHull K`.

This is the only statement in the file about the inside of `K`, and it takes what it needs at one
point as a hypothesis: for a Jordan curve `K` the hypothesis is the plane-separation statement
`J ⊆ closure (filledHull J \ J)` recorded in the roadmap section of
`TauCeti/Topology/FilledHull.lean`, read at `p`. -/
theorem nonempty_inter_filledHull_or_nonempty_inter_filledHull (hUo : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U) (hγ : f '' (U ∩ sphere ζ ρ) ⊆ K)
    (hp : p ∈ f '' (U ∩ sphere ζ ρ)) (hin : p ∈ closure (filledHull K \ K)) :
    (f '' (U ∩ ball ζ ρ) ∩ filledHull K).Nonempty ∨
      (f '' (U \ closedBall ζ ρ) ∩ filledHull K).Nonempty := by
  have hΩo : IsOpen (f '' U) := isOpen_image_of_differentiableOn_of_injOn hUo hd hinj
  obtain ⟨q, hqΩ, hqH, hqK⟩ :=
    mem_closure_iff.mp hin _ hΩo (image_mono inter_subset_left hp)
  rw [image_eq_union_sides_union_crosscut (f := f) (U := U) (ζ := ζ) (ρ := ρ)] at hqΩ
  exact (hqΩ.resolve_right fun h => hqK (hγ h)).imp (fun h => ⟨q, h, hqH⟩) fun h => ⟨q, h, hqH⟩

/-- **A narrow curve next to a crosscut encloses the near side.** Let `K` be bounded, run from the
image crosscut along the boundary of the image domain, and have a point of its inside next to the
image crosscut. If `K` is narrower than the *far* image side — the situation at a small crosscut
radius, where the far side is nearly the whole image domain — then it is the *near* side that `K`
encloses, and by `TauCeti.diam_le_diam_of_subset_filledHull` that side is no wider than `K`.

Of the two alternatives `TauCeti.nonempty_inter_filledHull_or_nonempty_inter_filledHull` offers, the
far one is excluded: it would trap the far side inside `K` and so make it no wider than `K`. -/
theorem image_inter_ball_subset_filledHull_of_diam_lt (hUo : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    (hAc : IsPreconnected (U ∩ ball ζ ρ)) (hBc : IsPreconnected (U \ closedBall ζ ρ))
    (hKb : IsBounded K) (hγ : f '' (U ∩ sphere ζ ρ) ⊆ K)
    (hK : K ⊆ closure (f '' (U ∩ sphere ζ ρ)) ∪ frontier (f '' U))
    (hlt : diam K < diam (f '' (U \ closedBall ζ ρ)))
    (hp : p ∈ f '' (U ∩ sphere ζ ρ)) (hin : p ∈ closure (filledHull K \ K)) :
    f '' (U ∩ ball ζ ρ) ⊆ filledHull K := by
  rcases nonempty_inter_filledHull_or_nonempty_inter_filledHull hUo hd hinj hγ hp hin with h | h
  · exact image_subset_filledHull_of_nonempty_inter hUo hd hinj inter_subset_left
      disjoint_inter_ball_inter_sphere hAc hK h
  · exact absurd (diam_le_diam_of_subset_filledHull hKb
      (image_subset_filledHull_of_nonempty_inter hUo hd hinj sdiff_subset
        disjoint_sdiff_closedBall_inter_sphere hBc hK h)) (not_le.mpr hlt)

/-! ## Comparison with the frontier route -/

/-- **A boundary piece enclosing what the near side clings to encloses the near side.** If every
boundary point of the image domain on the frontier of the near image side lies in `E ⊆ frontier
(f '' U)`, then the frontier of that side lies in `f '' (U ∩ sphere ζ ρ) ∪ E` by
`TauCeti.frontier_image_inter_ball_subset`, so `TauCeti.subset_filledHull_of_frontier_subset`
encloses the side.

So the hypothesis of `TauCeti.exists_continuousOn_closure_eqOn_of_forall_exists_subset_filledHull`
below is implied by the hypothesis of
`TauCeti.exists_continuousOn_closure_eqOn_of_forall_exists_diam_union_le` of
`Conformal/CutDiameter.lean` read with the same `E`: the enclosure route asks for no more than the
frontier route. -/
theorem image_inter_ball_subset_filledHull_of_frontier_subset (hUo : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U) (hb : IsBounded (f '' U)) {E : Set ℂ}
    (hEsub : E ⊆ frontier (f '' U))
    (hE : frontier (f '' U) ∩ frontier (f '' (U ∩ ball ζ ρ)) ⊆ E) :
    f '' (U ∩ ball ζ ρ) ⊆ filledHull (f '' (U ∩ sphere ζ ρ) ∪ E) :=
  subset_filledHull_of_frontier_subset
    (isOpen_image_of_differentiableOn_of_injOn (hUo.inter isOpen_ball)
      (hd.mono inter_subset_left) (hinj.mono inter_subset_left))
    (hb.subset (image_mono inter_subset_left))
    (disjoint_image_of_disjoint_inter_sphere hUo hd hinj inter_subset_left
      disjoint_inter_ball_inter_sphere
      (union_subset (subset_closure.trans subset_union_left) (hEsub.trans subset_union_right)))
    fun _ hw => (frontier_image_inter_ball_subset hUo hd hinj hw).imp id fun h => hE ⟨h, hw⟩

/-! ## The boundary limit -/

/-- **The crosscut criterion in enclosure form, cluster-set version.** If for every `ε > 0` there is
a crosscut radius `ρ > 0` and a bounded set `K` of diameter at most `ε` that cuts the near image
side off from infinity, then `f` has at most one cluster value at `ζ` along `U`.

The near image side is no wider than `K` by `TauCeti.diam_le_diam_of_subset_filledHull`, and
`Metric.dist_le_diam_of_mem` reads that as a bound on the distance between two values of `f` on the
crosscut neighbourhood, which is the Cauchy criterion
`TauCeti.subsingleton_clusterSetOn_of_forall_exists`. Neither holomorphy nor injectivity is used:
the enclosure hypothesis already carries all the geometry. -/
theorem subsingleton_clusterSetOn_of_forall_exists_subset_filledHull
    (h : ∀ ε > 0, ∃ ρ > 0, ∃ K : Set ℂ, IsBounded K ∧
      f '' (U ∩ ball ζ ρ) ⊆ filledHull K ∧ diam K ≤ ε) :
    (clusterSetOn f U ζ).Subsingleton := by
  refine subsingleton_clusterSetOn_of_forall_exists fun ε hε => ?_
  obtain ⟨ρ, hρ, K, hKb, hsub, hdiam⟩ := h ε hε
  exact ⟨ρ, hρ, fun _ hx _ hy =>
    (dist_le_diam_of_mem ((isBounded_filledHull.mpr hKb).subset hsub) (mem_image_of_mem f hx)
      (mem_image_of_mem f hy)).trans ((diam_le_diam_of_subset_filledHull hKb hsub).trans hdiam)⟩

/-- **The crosscut criterion in enclosure form, boundary-limit version.** A map with bounded image
has a limit at a point `ζ` of the closure of its domain, along the domain, as soon as the pieces it
cuts off at `ζ` are enclosed by arbitrarily narrow bounded sets. -/
theorem exists_tendsto_nhdsWithin_of_forall_exists_subset_filledHull (hb : IsBounded (f '' U))
    (hζ : ζ ∈ closure U)
    (h : ∀ ε > 0, ∃ ρ > 0, ∃ K : Set ℂ, IsBounded K ∧
      f '' (U ∩ ball ζ ρ) ⊆ filledHull K ∧ diam K ≤ ε) :
    ∃ v, Tendsto f (𝓝[U] ζ) (𝓝 v) :=
  exists_tendsto_of_clusterSetOn_subsingleton hb.isCompact_closure
    (fun w hw => subset_closure ⟨w, hw, rfl⟩) hζ
    (subsingleton_clusterSetOn_of_forall_exists_subset_filledHull h)

/-- **The crosscut criterion in enclosure form, continuous-extension version.** If at *every*
boundary point of the domain the pieces cut off are enclosed by arbitrarily narrow bounded sets,
a continuous map with bounded image extends continuously to `closure U`.

This is the shape in which the Jordan-domain case of the Carathéodory boundary correspondence is to
be proved: the length–area method makes the image crosscut short and
`TauCeti.exists_isJordanCurve_superset_closure_image_ball_inter_sphere_diam_le` closes it into an
arbitrarily small Jordan curve `K`, and
`TauCeti.image_inter_ball_subset_filledHull_of_diam_lt` turns that curve into the enclosure asked
for here — given, at one point of the image crosscut, that `K` has inside points next to it.
Nothing here asserts that the extension is injective, which is an independent matter. For a disc,
`Metric.frontier_ball` and `Metric.closure_ball` turn the hypothesis and the conclusion into
statements about `sphere c r` and `closedBall c r`. -/
theorem exists_continuousOn_closure_eqOn_of_forall_exists_subset_filledHull (hUo : IsOpen U)
    (hfc : ContinuousOn f U) (hb : IsBounded (f '' U))
    (h : ∀ w ∈ frontier U, ∀ ε > 0, ∃ ρ > 0, ∃ K : Set ℂ, IsBounded K ∧
      f '' (U ∩ ball w ρ) ⊆ filledHull K ∧ diam K ≤ ε) :
    ∃ F : ℂ → ℂ, ContinuousOn F (closure U) ∧ EqOn F f U :=
  exists_continuousOn_closure_eqOn_of_isBounded hUo hfc hb fun w hw =>
    subsingleton_clusterSetOn_of_forall_exists_subset_filledHull (h w hw)

end TauCeti
