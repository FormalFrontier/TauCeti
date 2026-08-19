/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.Connected.Basic
import TauCeti.Topology.Frontier
public import Mathlib.Topology.Connected.LocallyConnected

/-!
# Filling in the bounded complementary components of a set

The **filled hull** `TauCeti.filledHull K` of a subset `K` of a topological space with a bornology
is `K` together with the bounded connected components of its complement: the points whose component
in `Kᶜ` is bounded. Points of `K` qualify vacuously, their component in `Kᶜ` being empty. Filling a
circle gives the closed disc it bounds; filling a segment, or any set whose complement is connected
and unbounded, changes nothing.

This file is the topological layer: the definition and the structural facts, which ask only for a
topology and a bornology, being about components and boundedness and nothing else. That filling
does not make a set wider needs a real normed space and lives in
`TauCeti/Analysis/Normed/Module/FilledHull.lean`.

The shape in which the structural side is spent is `TauCeti.IsPreconnected.subset_filledHull`: a
preconnected set disjoint from `K` is trapped inside the filled hull as soon as it meets it, since
it then lies in a single bounded component. Together with the width bound of the normed file it
says that *a connected set that a small `K` cuts off from infinity is itself small*, with no
regularity asked of `K`; that composite is `TauCeti.IsPreconnected.diam_le_diam_of_disjoint` there.

The negation of membership — that the component of a point in the complement of `K` is *unbounded*
— already occurs, unfolded, in the winding-number layer: it is the hypothesis of
`TauCeti.Contour.windingNumber_eq_zero_of_unbounded_component` in
`TauCeti/Analysis/Contour/Winding/UnboundedComponent.lean` and of its cycle form
`TauCeti.Contour.Cycle.windingNumber_eq_zero_of_unbounded_component` in
`TauCeti/Analysis/Contour/Cycle/Winding.lean`, both of which say that the winding number vanishes
off the filled hull of the trace. Those statements are left as they stand: they are about the
unbounded side, which needs no name, whereas everything here is about the filled side.

The hull is *not* claimed to be connected or idempotent, neither of which holds without hypotheses
on `K`. Closedness does hold when `K` is closed and the space is locally connected
(`isClosed_filledHull`).

## Roadmap role

Plane separation for Jordan curves is the open frontier item of layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md`, the Carathéodory boundary correspondence:
`ConformalMapping/STATUS.md` records that nothing in the repository establishes that a Jordan curve
separates the plane, and asks that how much of it the boundary work needs be settled first. What
that work needs is the single statement that every point of a Jordan curve is a limit of points
inside it,

> `J ⊆ closure (filledHull J \ J)`,

which is written in the vocabulary defined here — the inside of `J` is `filledHull J \ J`. So this
file supplies what the missing stage is stated with rather than presuming it: nothing here assumes
separation, or any other regularity of `K`.

## Main results

* `TauCeti.filledHull` — the filled hull, and `TauCeti.subset_filledHull`,
  `TauCeti.filledHull_mono` its two structural properties.
* `TauCeti.filledHull_eq_self` — filling a set whose complement is preconnected and unbounded
  changes nothing.
* `TauCeti.IsPreconnected.subset_filledHull` — a preconnected set disjoint from `K` that meets the
  filled hull lies in it.
* `TauCeti.subset_filledHull_of_frontier_subset` — a bounded set whose frontier `K` swallows
  lies in the filled hull, with no connectivity asked of it.
* `TauCeti.isClosed_filledHull` — the filled hull of a closed set is closed.
-/

public section

namespace TauCeti

open Bornology Set

variable {E : Type*} [TopologicalSpace E] [Bornology E] {K L S : Set E} {x : E}

/-- The **filled hull** of a set `K`: the points whose connected component in the complement of `K`
is bounded. Equivalently, `K` together with the bounded connected components of `Kᶜ`; a point of
`K` belongs because its component in `Kᶜ` is empty. -/
def filledHull (K : Set E) : Set E := {x | IsBounded (connectedComponentIn Kᶜ x)}

@[simp]
theorem mem_filledHull_iff : x ∈ filledHull K ↔ IsBounded (connectedComponentIn Kᶜ x) := Iff.rfl

/-- **A set lies in its filled hull.** For `x ∈ K` the component of `x` in `Kᶜ` is empty, and the
empty set is bounded. -/
theorem subset_filledHull : K ⊆ filledHull K := by
  intro x hx
  have hxc : x ∉ Kᶜ := by simpa using hx
  simp [mem_filledHull_iff, connectedComponentIn_eq_empty hxc]

/-- **Filling is monotone.** Enlarging `K` shrinks the complement, hence shrinks each component of
it, hence can only turn unbounded components into bounded ones. -/
@[gcongr]
theorem filledHull_mono (h : K ⊆ L) : filledHull K ⊆ filledHull L := fun _ hx =>
  mem_filledHull_iff.mpr <|
    (mem_filledHull_iff.mp hx).subset (connectedComponentIn_mono _ (compl_subset_compl.mpr h))

/-- **Filling changes nothing when the complement is connected and unbounded.** The complement is
then a single component and that component is unbounded, so no point outside `K` is filled in. This
is the case of a segment in the plane, and of any set that does not separate the space. -/
theorem filledHull_eq_self (h : IsPreconnected Kᶜ) (hu : ¬ IsBounded Kᶜ) : filledHull K = K := by
  refine Subset.antisymm (fun x hx => ?_) subset_filledHull
  by_contra hxK
  exact hu ((mem_filledHull_iff.mp hx).subset
    (h.subset_connectedComponentIn (mem_compl hxK) subset_rfl))

/-- **A preconnected set that a set cuts off from infinity lies in its filled hull.** If `S` is
preconnected and disjoint from `K`, then `S` lies in a single connected component of `Kᶜ`; meeting
the filled hull says that component is bounded, so all of `S` is in the hull. -/
theorem IsPreconnected.subset_filledHull (hS : IsPreconnected S) (hSK : Disjoint S K)
    (hne : (S ∩ filledHull K).Nonempty) : S ⊆ filledHull K := by
  obtain ⟨x, hxS, hxH⟩ := hne
  have hScompl : S ⊆ Kᶜ := fun y hy => Set.disjoint_left.mp hSK hy
  have hScomp : S ⊆ connectedComponentIn Kᶜ x := hS.subset_connectedComponentIn hxS hScompl
  intro y hy
  rw [mem_filledHull_iff, ← connectedComponentIn_eq (hScomp hy)]
  exact mem_filledHull_iff.mp hxH

/-- **A bounded set whose frontier lies in `K` is cut off from infinity by `K`.** A point of
`S \ K` lies in `interior S`, since every non-interior point of `S` lies on `frontier S ⊆ K`. Its
connected component in `Kᶜ` cannot leave `interior S`: were it to, it would meet
`frontier (interior S) ⊆ frontier S ⊆ K` by `TauCeti.IsPreconnected.inter_frontier_nonempty`,
while lying in `Kᶜ`. So that component is bounded because `S` is. Points of `S ∩ K` lie in the
filled hull directly.

Unlike `TauCeti.IsPreconnected.subset_filledHull` this asks nothing of the connectivity of `S` and
nothing about the hull being met, at the price of asking `K` to swallow the whole frontier — the
same trade as between `TauCeti.diam_le_diam_of_frontier_subset` and
`TauCeti.IsPreconnected.diam_le_diam_of_disjoint`. -/
theorem subset_filledHull_of_frontier_subset (hSb : IsBounded S) (hfr : frontier S ⊆ K) :
    S ⊆ filledHull K := by
  intro x hx
  by_cases hxK : x ∈ K
  · exact subset_filledHull hxK
  have hxKc : x ∈ Kᶜ := hxK
  have hxi : x ∈ interior S := (mem_interior_iff_notMem_frontier hx).2 fun h => hxK (hfr h)
  have hcomp : connectedComponentIn Kᶜ x ⊆ interior S := by
    by_contra h
    obtain ⟨y, hy, hyi⟩ := not_subset.mp h
    obtain ⟨z, hz, hzf⟩ := IsPreconnected.inter_frontier_nonempty
      isPreconnected_connectedComponentIn ⟨x, mem_connectedComponentIn hxKc, hxi⟩ ⟨y, hy, hyi⟩
    exact connectedComponentIn_subset _ _ hz (hfr (frontier_interior_subset hzf))
  exact mem_filledHull_iff.mpr (hSb.subset (hcomp.trans interior_subset))

/-- **The filled hull of a closed set is closed.** Its complement is the union of the unbounded
connected components of `Kᶜ`, each of which is open. -/
theorem isClosed_filledHull [LocallyConnectedSpace E] (hK : IsClosed K) :
    IsClosed (filledHull K) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  rw [mem_compl_iff, mem_filledHull_iff] at hx
  refine ⟨connectedComponentIn Kᶜ x, fun y hy => ?_, hK.isOpen_compl.connectedComponentIn, ?_⟩
  · rw [mem_compl_iff, mem_filledHull_iff, ← connectedComponentIn_eq hy]
    exact hx
  · refine mem_connectedComponentIn fun hxK => hx ?_
    rw [connectedComponentIn_eq_empty (notMem_compl_iff.mpr hxK)]
    exact isBounded_empty

end TauCeti
