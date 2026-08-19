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
side fall inside a small curve running along the crosscut. The file
`Conformal/Crosscut/SmallJordanCurve.lean` builds such curves from the two cases supplied by
`Conformal/Crosscut/Jordan.lean` and `Conformal/Crosscut/Arc.lean`: a short image crosscut closes
up into an arbitrarily small Jordan curve
(`TauCeti.exists_isJordanCurve_superset_closure_image_ball_inter_sphere_diam_le`).

## The two sides against one curve

The diameter-selection theorem below runs on a bounded `K` lying on the closed image crosscut and
the image boundary,

> `f '' (U ∩ sphere ζ ρ) ⊆ K ⊆ closure (f '' (U ∩ sphere ζ ρ)) ∪ frontier Ω`,

the shape in which a curve joining the two ends of the image crosscut along `frontier Ω` arrives.
Its ingredients use only the assumptions they need: trapping a side uses the upper inclusion but
not boundedness, while existence of an enclosed side uses the lower inclusion but neither
boundedness nor the upper inclusion. The comparison with the frontier route uses instead the
filled hull of `f '' (U ∩ sphere ζ ρ) ∪ E`. The upper inclusion keeps `K` off the two sides by
`TauCeti.closure_image_inter_sphere_subset_union_frontier_image`: the image crosscut is relatively
closed in the image domain, so its closure adds only boundary points. Two facts locate the enclosed
side, and a diameter comparison selects the near one.

* **An enclosed side is trapped**: each side is preconnected and disjoint from `K`, so if it meets
  `filledHull K` it lies inside (`TauCeti.image_subset_filledHull_of_disjoint_inter_sphere`) and is
  therefore no wider than `K`.
* **At least one side**, as soon as some point of the image crosscut is a limit of points inside
  `K` (`TauCeti.nonempty_inter_filledHull_image_inter_ball_or_image_sdiff_closedBall`): a point of
  the inside close enough to it lies in the image domain and off `K`, hence on one of the two sides.

If `K` is narrower than the far side, at most the near side can be enclosed: trapping the far side
would give `diam B ≤ diam K`. Combining this exclusion with the two facts above,
`TauCeti.image_inter_ball_subset_filledHull_of_diam_lt` puts the near side inside `filledHull K`.

## What is assumed, and what remains

No theorem here assumes plane separation. The second fact above takes as a hypothesis that one
*given* point `p` of the image crosscut satisfies `p ∈ closure (filledHull K \ K)`, a property of
the set `K` at the point `p`; it is not an unproved theorem in disguise. This is the only place the
inside assumption is introduced; `TauCeti.image_inter_ball_subset_filledHull_of_diam_lt` passes it
on unchanged.

What that hypothesis costs, when `K` is a Jordan curve, is exactly the open frontier item recorded
in the roadmap section of `TauCeti/Topology/FilledHull.lean`: that every point of a Jordan curve is
a limit of points inside it, `J ⊆ closure (filledHull J \ J)`. To apply the reduction at every
small radius one must also produce a point of the image crosscut, prove the two circular-cut sides
preconnected, and show that the far-side image has diameter larger than the small curve. This file
isolates those inputs; it does not discharge them.

That the enclosure route asks for no more than the frontier route does is
`TauCeti.image_inter_ball_subset_filledHull_of_frontier_subset`: a boundary piece `E` enclosing
`frontier Ω ∩ frontier A` puts the near side inside `f '' (U ∩ sphere ζ ρ) ∪ E`, so the hypothesis
produced by the frontier route gives the same inclusion with the same `E`. Either route then uses
`TauCeti.diam_le_diam_of_subset_filledHull` to feed the common metric criterion
`TauCeti.exists_continuousOn_closure_eqOn_of_forall_exists_diam_le`.

## Main results

* `TauCeti.image_subset_filledHull_of_disjoint_inter_sphere` — an image side meeting the inside of
  such a curve lies inside it.
* `TauCeti.nonempty_inter_filledHull_image_inter_ball_or_image_sdiff_closedBall` — a curve with
  inside points next to the image crosscut encloses one of the two sides.
* `TauCeti.image_inter_ball_subset_filledHull_of_diam_lt` — such a curve, if narrower than the far
  side, encloses the *near* side.
* `TauCeti.image_inter_ball_subset_filledHull_of_frontier_subset` — the enclosure hypothesis is
  implied by the boundary-piece hypothesis of `Conformal/CutDiameter.lean`.

## Roadmap role

This advances layer **L5** of `TauCetiRoadmap/ConformalMapping/README.md`, the Jordan-domain case of
the Carathéodory boundary correspondence, by reducing enclosure of the near side to the explicit
inside, preconnectedness, nonemptiness and far-side diameter inputs above. It is the consumption of
the filled hull that
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

/-! ## An enclosed side is trapped, and narrow -/

/-- **An image side that meets the inside of such a curve lies inside it.** The side is
preconnected as a continuous image of a preconnected set and disjoint from `K` by
`TauCeti.disjoint_image_of_subset_closure_image_inter_sphere_union_frontier_image`,
so `TauCeti.IsPreconnected.subset_filledHull`
traps it in the bounded component of `Kᶜ` it meets. Instantiate `V` at `U ∩ ball ζ ρ` for the near
side and at `U \ closedBall ζ ρ` for the far side. -/
theorem image_subset_filledHull_of_disjoint_inter_sphere (hUo : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U) (hVU : V ⊆ U)
    (hV : Disjoint V (U ∩ sphere ζ ρ)) (hVc : IsPreconnected V)
    (hK : K ⊆ closure (f '' (U ∩ sphere ζ ρ)) ∪ frontier (f '' U))
    (hne : (f '' V ∩ filledHull K).Nonempty) : f '' V ⊆ filledHull K :=
  IsPreconnected.subset_filledHull (hVc.image f (hd.continuousOn.mono hVU))
    (disjoint_image_of_subset_closure_image_inter_sphere_union_frontier_image
      hUo hd hinj hVU hV hK) hne

/-! ## At least one side is enclosed -/

/-- **A curve with a point of its inside next to the image crosscut encloses one of the two sides.**
If a point `p` of the image crosscut is a limit of points of `filledHull K \ K`, then such a point
`q` close enough to `p` lies in the open image domain; being off `K` it is off the image crosscut,
so it lies on one of the two image sides, and it lies in `filledHull K`.

This is where the inside assumption is introduced, at one point as a hypothesis; the diameter
criterion below passes it on unchanged. For a Jordan curve `K` the hypothesis is the
plane-separation statement `J ⊆ closure (filledHull J \ J)` recorded in the roadmap section of
`TauCeti/Topology/FilledHull.lean`, read at `p`. -/
theorem nonempty_inter_filledHull_image_inter_ball_or_image_sdiff_closedBall (hUo : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U) (hγ : f '' (U ∩ sphere ζ ρ) ⊆ K)
    (hp : p ∈ f '' (U ∩ sphere ζ ρ)) (hin : p ∈ closure (filledHull K \ K)) :
    (f '' (U ∩ ball ζ ρ) ∩ filledHull K).Nonempty ∨
      (f '' (U \ closedBall ζ ρ) ∩ filledHull K).Nonempty := by
  have hΩo : IsOpen (f '' U) := isOpen_image_of_differentiableOn_of_injOn hUo hd hinj
  obtain ⟨q, hqΩ, hqH, hqK⟩ :=
    mem_closure_iff.mp hin _ hΩo (image_mono inter_subset_left hp)
  rw [image_eq_image_inter_ball_union_image_sdiff_closedBall_union_image_inter_sphere] at hqΩ
  exact (hqΩ.resolve_right fun h => hqK (hγ h)).imp (fun h => ⟨q, h, hqH⟩) fun h => ⟨q, h, hqH⟩

/-- **A narrow curve next to a crosscut encloses the near side.** Let `K` be bounded, run from the
image crosscut along the boundary of the image domain, and have a point of its inside next to the
image crosscut. If `K` is narrower than the *far* image side — the situation at a small crosscut
radius, where the far side is nearly the whole image domain — then it is the *near* side that `K`
encloses, and by `TauCeti.diam_le_diam_of_subset_filledHull` that side is no wider than `K`.

Of the two alternatives
`TauCeti.nonempty_inter_filledHull_image_inter_ball_or_image_sdiff_closedBall` offers, the far one
is excluded: it would trap the far side inside `K` and so make it no wider than `K`. The theorem
still requires both cut sides to be preconnected, a point on the image crosscut, and the strict
far-side diameter bound; those inputs are not produced here. -/
theorem image_inter_ball_subset_filledHull_of_diam_lt (hUo : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    (hAc : IsPreconnected (U ∩ ball ζ ρ)) (hBc : IsPreconnected (U \ closedBall ζ ρ))
    (hKb : IsBounded K) (hγ : f '' (U ∩ sphere ζ ρ) ⊆ K)
    (hK : K ⊆ closure (f '' (U ∩ sphere ζ ρ)) ∪ frontier (f '' U))
    (hlt : diam K < diam (f '' (U \ closedBall ζ ρ)))
    (hp : p ∈ f '' (U ∩ sphere ζ ρ)) (hin : p ∈ closure (filledHull K \ K)) :
    f '' (U ∩ ball ζ ρ) ⊆ filledHull K := by
  rcases nonempty_inter_filledHull_image_inter_ball_or_image_sdiff_closedBall
    hUo hd hinj hγ hp hin with h | h
  · exact image_subset_filledHull_of_disjoint_inter_sphere hUo hd hinj inter_subset_left
      disjoint_inter_ball_inter_sphere hAc hK h
  · exact absurd (diam_le_diam_of_subset_filledHull hKb
      (image_subset_filledHull_of_disjoint_inter_sphere hUo hd hinj sdiff_subset
        disjoint_sdiff_closedBall_inter_sphere hBc hK h)) (not_le.mpr hlt)

/-! ## Comparison with the frontier route -/

/-- **A boundary piece enclosing what the near side clings to encloses the near side.** If every
boundary point of the image domain on the frontier of the near image side lies in `E`, then the
frontier of that side lies in `f '' (U ∩ sphere ζ ρ) ∪ E` by
`TauCeti.frontier_image_inter_ball_subset`, so `TauCeti.subset_filledHull_of_frontier_subset`
encloses the side.

Thus the frontier route supplies the same filled-hull inclusion as the enclosure route, with the
same `E`; either inclusion gives a diameter bound for the generic criterion
`TauCeti.exists_continuousOn_closure_eqOn_of_forall_exists_diam_le`. -/
theorem image_inter_ball_subset_filledHull_of_frontier_subset (hUo : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    (hb : IsBounded (f '' (U ∩ ball ζ ρ))) {E : Set ℂ}
    (hE : frontier (f '' U) ∩ frontier (f '' (U ∩ ball ζ ρ)) ⊆ E) :
    f '' (U ∩ ball ζ ρ) ⊆ filledHull (f '' (U ∩ sphere ζ ρ) ∪ E) :=
  subset_filledHull_of_frontier_subset
    hb
    fun _ hw => (frontier_image_inter_ball_subset hUo hd hinj hw).imp id fun h => hE ⟨h, hw⟩

end TauCeti
