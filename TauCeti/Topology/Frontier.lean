/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Basic

/-!
# A connected set that straddles a set meets its frontier

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

The intended consumer is layer **L5** of `TauCetiRoadmap/ConformalMapping/README.md`, Carathéodory's
boundary correspondence, through `TauCeti/Analysis/Normed/Module/DiamFrontier.lean`: a ray leaving a
bounded set crosses its frontier, which is what makes the frontier of such a set as wide as the set
itself. Nothing here is specific to that use.

## Main results

* `TauCeti.IsPreconnected.inter_frontier_nonempty` — a preconnected set meeting both a set and its
  complement meets the frontier of that set.
-/

public section

namespace TauCeti

open Set

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

end TauCeti
