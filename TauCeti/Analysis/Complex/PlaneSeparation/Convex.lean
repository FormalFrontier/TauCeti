/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Topology
public import TauCeti.Analysis.Complex.PlaneSeparation.Basic
import TauCeti.Topology.FilledHull

/-!
# Plane separation for solid convex frontiers

The filled hull formulation of plane separation is immediate for the frontier of a bounded convex
set with nonempty interior. The general statement for Jordan curves is the open topological gate in
layer **L5** of `TauCetiRoadmap/ConformalMapping/README.md`; this is its solid-convex model case,
strictly generalising the circle case proved in `TauCeti/Topology/FilledHull.lean` and supplying a
concrete test of the `filledHull` interface that `Conformal/Caratheodory.lean` consumes.

The proof has two ingredients. `TauCeti.subset_filledHull_of_frontier_subset` puts every point of a
bounded set into the filled hull of its frontier. For a convex set with nonempty interior, the
interior is dense in the set (`Convex.closure_interior_eq_closure_of_nonempty_interior`), and the
interior is disjoint from the frontier. Thus every frontier point is approached by points in the
filled hull which are not on the frontier.

No Jordan separation theorem is used here. The arbitrary-Jordan case remains the next topological
step on the Carathéodory path.

## Main result

* `TauCeti.subset_closure_filledHull_sdiff_frontier_of_convex` — every point of the frontier of a
  bounded convex set with nonempty interior is approached by points in the bounded complementary
  components of that frontier.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*, Math.
  Ann. **73** (1913), 305–320.
* J. B. Conway, *Functions of One Complex Variable I*, Ch. IX.
-/

public section

namespace TauCeti

open Bornology Set Topology

/-- **The inside is dense at the frontier of a solid convex set.** If `s` is bounded and convex
with nonempty interior, every point of `frontier s` is a limit of points in
`filledHull (frontier s) \ frontier s`.

This is the solid-convex model case of the plane-separation statement needed by the
Carathéodory boundary correspondence. The bounded-set filled-hull lemma supplies the inside
points, while convexity makes the interior dense up to the frontier. -/
theorem subset_closure_filledHull_sdiff_frontier_of_convex {s : Set ℂ} (hs : Convex ℝ s)
    (hne : (interior s).Nonempty) (hb : IsBounded s) :
    frontier s ⊆ closure (filledHull (frontier s) \ frontier s) := by
  have hinterior : interior s ⊆ filledHull (frontier s) \ frontier s := by
    intro x hx
    refine ⟨subset_filledHull_of_frontier_subset hb subset_rfl (interior_subset hx), ?_⟩
    exact fun hxf => Set.disjoint_left.mp disjoint_interior_frontier hx hxf
  intro x hx
  apply closure_mono hinterior
  rw [hs.closure_interior_eq_closure_of_nonempty_interior hne]
  exact frontier_subset_closure hx

end TauCeti
