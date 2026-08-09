/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Basic

/-!
# Three frontier lemmas: straddling, splitting a domain in two, and clinging to it from inside

Three elementary facts about `frontier`, each the topological core of a step that a boundary
argument would otherwise carry out inside a concrete space.

## A connected set that straddles a set meets its frontier

A preconnected set that meets both a set `V` and its complement must meet `frontier V`: it cannot
cross from the inside of `V` to the outside without touching the boundary. This is the
intermediate-value principle in its purely topological form, and it is the mechanism by which a
*path* leaving a set produces a *boundary point* of that set.

Mathlib records the two extreme cases — `frontier_eq_empty_iff` and `nonempty_frontier_iff` say
that in a preconnected *space* the frontier of `V` is empty exactly when `V` is `∅` or `univ` — but
not this relative form, which is the one an argument along a segment or a path needs. No hypothesis
is placed on `V`; only preconnectedness of the straddling set is used.

The proof is the standard clopen argument: the complement of `frontier V` is the disjoint union of
the two open sets `interior V` and `interior Vᶜ` (`compl_frontier_eq_union_interior`), so a
preconnected set avoiding the frontier lies inside one of them, and then it misses `V` entirely or
is contained in `V` entirely.

## Where the boundary of the image of one side of a split domain can lie

Split a set `U` into two pieces `s` and `t` that a map `f` sends to *disjoint open* sets, plus a
remainder `u`. Then `frontier (f '' s) ⊆ f '' u ∪ frontier (f '' U)`
(`TauCeti.frontier_image_subset_image_union_frontier_image`): the boundary of the image of one side
consists of images of the remainder — the cut — and of boundary points of the whole image, and of
nothing else.

The proof is a three-way case split. A point `p` of `frontier (f '' s)` lies in `closure (f '' U)`,
so if it is not on `frontier (f '' U)` it is a value `f w` with `w` in one of the three covering
sets. It cannot come from `s`, since `f '' s` is open and therefore disjoint from its own frontier;
and it cannot come from `t`, since `f '' t` is then an open neighbourhood of `p`, which must meet
`f '' s`, contradicting disjointness of the two images. So `w ∈ u`.

The source carries no topology; the sides enter topologically only through their images, which are
asked to be open and disjoint, and that is all the argument uses of them. What is asked of the
sides themselves is purely set-theoretic: `s ⊆ U` and the covering `U ⊆ s ∪ t ∪ u`. In particular
`t` need not lie in `U`, and neither side need be open or disjoint from the other. A consumer whose
map is open and injective on two disjoint open sides supplies both image hypotheses, as the
conformal one below does through the open mapping theorem and `Disjoint.image`.

## What a set's frontier sees of a subset

A subset `A` of a set `V` cannot reach `frontier V` except through its own frontier:

> `frontier V ∩ closure A = frontier V ∩ frontier A`

(`TauCeti.frontier_inter_closure_eq_frontier_inter_frontier`). The reason is that `closure A` is
`A ∪ frontier A`, and a point of `A` on `frontier V` is already on `frontier A`: it is adherent to
`A` and, since `interior A ⊆ interior V`, it is not interior to `A`. So the part of `frontier V`
that `A` clings to has two interchangeable descriptions — as the reach of `closure A`, and as the
meeting of two frontiers. The first is the one an argument about limits of points of `A` produces;
the second is the one a diameter estimate consumes, `frontier` being where the estimates of a
domain-splitting argument live.

## Consumers

All three lemmas serve layer **L5** of `TauCetiRoadmap/ConformalMapping/README.md`, Carathéodory's
boundary correspondence. The first does so through
`TauCeti/Analysis/Normed/Module/DiamFrontier.lean`: a ray leaving a bounded set crosses its
frontier, which is what makes the frontier of such a set as wide as the set itself. The second is
the splitting step of `TauCeti/Analysis/Complex/Conformal/CutDiameter.lean`, where `s` and `t` are
the two sides of a circular crosscut of a domain and `u` is the crosscut arc. The third is what
lets `TauCeti/Analysis/Complex/Conformal/ClusterSet.lean` identify the boundary piece that one
side of such a crosscut cuts off, whose description as a union of cluster sets is naturally a
statement about a closure. Nothing here is specific to those uses; no lemma mentions a metric, let
alone a holomorphic map.

## Main results

* `TauCeti.IsPreconnected.inter_frontier_nonempty` — a preconnected set meeting both a set and its
  complement meets the frontier of that set.
* `TauCeti.frontier_image_subset_image_union_frontier_image` — for a set split into two sides with
  disjoint open images plus a remainder, the frontier of the image of the side lying in that set
  lies on the image of the remainder and on the frontier of the image of the whole.
* `TauCeti.frontier_inter_closure_eq_frontier_inter_frontier` — the frontier of a set meets the
  closure of a subset exactly where it meets that subset's frontier.
-/

public section

namespace TauCeti

open Set

section Straddle

variable {X : Type*} [TopologicalSpace X] {S V : Set X}

/-- **A preconnected set that meets both a set and its complement meets its frontier.** If `S` is
preconnected and contains a point of `V` and a point outside `V`, then `S` meets `frontier V`.

Nothing is assumed about `V`; the argument is that `(frontier V)ᶜ` is the union of the two disjoint
open sets `interior V` and `interior Vᶜ`, so a preconnected set missing the frontier is confined to
one of them and therefore cannot straddle `V`. -/
theorem IsPreconnected.inter_frontier_nonempty (hS : IsPreconnected S) (h₁ : (S ∩ V).Nonempty)
    (h₂ : (S \ V).Nonempty) : (S ∩ frontier V).Nonempty := by
  by_contra hcon
  have hsub : S ⊆ interior V ∪ interior Vᶜ := by
    rw [← compl_frontier_eq_union_interior]
    exact fun x hx hxf => hcon ⟨x, hx, hxf⟩
  have hdisj : Disjoint (interior V) (interior Vᶜ) :=
    disjoint_compl_right.mono interior_subset interior_subset
  rcases hS.subset_or_subset isOpen_interior isOpen_interior hdisj hsub with h | h
  · obtain ⟨x, hxS, hxV⟩ := h₂
    exact hxV (interior_subset (h hxS))
  · obtain ⟨x, hxS, hxV⟩ := h₁
    exact interior_subset (h hxS) hxV

end Straddle

section ImageSplit

variable {X Y : Type*} [TopologicalSpace Y] {f : X → Y} {U s t u : Set X}

/-- **The boundary of the image of one side of a split domain lies on the image of the remainder
and on the boundary of the image of the domain.** If `U` is covered by two sets `s`, `t` with
disjoint open images together with a third set `u`, and `s ⊆ U`, then
`frontier (f '' s) ⊆ f '' u ∪ frontier (f '' U)`.

The conclusion is about `s`, the side that is asked to lie in `U`. The argument treats the two
sides alike apart from that, so a consumer with `t ⊆ U` in hand bounds `t` as well by swapping
their roles.

A frontier point of `f '' s` lies in `closure (f '' U)`, so if it is not a frontier point of
`f '' U` it is a value `f w` with `w` in one of the three covering sets: `w ∈ s` would place it
inside the open set `f '' s`, which is disjoint from its own frontier, and `w ∈ t` inside the open
set `f '' t`, which meets `f '' s` because the point is in its closure, contradicting disjointness
of the two images. So `w ∈ u`.

The source carries no topology at all: `U` and the three sets covering it are constrained only by
the two set-theoretic hypotheses `hsU : s ⊆ U` and `hcov : U ⊆ s ∪ t ∪ u`, while every topological
hypothesis, and the conclusion, lives in the target. In particular `t` need not lie in `U`, and
the two sides need be neither open nor disjoint nor separated by injectivity — only their images
need be open and disjoint, which is what the argument uses and what an injective open map on two
disjoint open sides supplies. -/
theorem frontier_image_subset_image_union_frontier_image (hfs : IsOpen (f '' s))
    (hft : IsOpen (f '' t)) (hst : Disjoint (f '' s) (f '' t)) (hsU : s ⊆ U)
    (hcov : U ⊆ s ∪ t ∪ u) :
    frontier (f '' s) ⊆ f '' u ∪ frontier (f '' U) := by
  intro p hp
  have hpΩ : p ∈ closure (f '' U) := closure_mono (image_mono hsU) hp.1
  rw [closure_eq_self_union_frontier] at hpΩ
  rcases hpΩ with hpin | hpfr
  · obtain ⟨w, hw, rfl⟩ := hpin
    rcases hcov hw with (hws | hwt) | hwu
    · exact absurd ⟨mem_image_of_mem f hws, hp⟩
        (eq_empty_iff_forall_notMem.mp hfs.inter_frontier_eq (f w))
    · obtain ⟨q, hqt, hqs⟩ := mem_closure_iff.mp hp.1 _ hft (mem_image_of_mem f hwt)
      exact absurd hqs (disjoint_right.mp hst hqt)
    · exact Or.inl (mem_image_of_mem f hwu)
  · exact Or.inr hpfr

end ImageSplit

section Inside

variable {X : Type*} [TopologicalSpace X] {A V : Set X}

/-- **The frontier of a set meets the closure of a subset exactly where it meets that subset's
frontier.** For any `A ⊆ V`,

> `frontier V ∩ closure A = frontier V ∩ frontier A`.

Writing `closure A` as `A ∪ frontier A`, the first piece brings nothing new: a point of `A` on
`frontier V` is adherent to `A` and is kept out of `interior A` by `interior A ⊆ interior V`, so it
already lies on `frontier A`. Only the inclusion `A ⊆ V` is used — `V` need be neither open nor
closed, and `A` is arbitrary.

So the part of `frontier V` that `A` clings to may be described either as its meeting with
`closure A` or as its meeting with `frontier A`. An argument about limits of points of `A` produces
the first; a diameter estimate obtained by splitting `V` into pieces consumes the second. -/
theorem frontier_inter_closure_eq_frontier_inter_frontier (hAV : A ⊆ V) :
    frontier V ∩ closure A = frontier V ∩ frontier A := by
  rw [closure_eq_self_union_frontier, inter_union_distrib_left]
  refine union_eq_right.mpr fun x hx =>
    ⟨hx.1, (mem_frontier_iff_notMem_interior hx.2).mpr fun hint => ?_⟩
  exact (mem_frontier_iff_notMem_interior (hAV hx.2)).mp hx.1 (interior_mono hAV hint)

end Inside

end TauCeti
