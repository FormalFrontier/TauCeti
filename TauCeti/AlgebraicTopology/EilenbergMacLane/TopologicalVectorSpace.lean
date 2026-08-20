/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Covering
public import TauCeti.Topology.Homotopy.HomotopyGroup.TopologicalVectorSpace

/-!
# Quotients of a real topological vector space are Eilenberg--Mac Lane spaces

A real topological vector space is contractible, hence simply connected, and all of its
homotopy groups vanish. Feeding this into
`IsQuotientCoveringMap.isEilenbergMacLaneSpaceOne` gives the classical source of
`K(G, 1)` spaces: whenever a group `G` acts on a real topological vector space so that the
orbit map is a quotient covering map — freely, with the orbits locally separated — the orbit
space is a `K(G, 1)`.

The two inputs are Mathlib's `RealTopologicalVectorSpace.contractibleSpace` and
`TauCeti.HomotopyGroup.subsingleton_of_topologicalVectorSpace`; both are instances, so the
statement carries no hypothesis beyond the quotient covering map itself.

This advances `TauCetiRoadmap/UniversalCovers/README.md`, Stage 4, item 13, "`K(G, 1)`
spaces". The circle and torus were already known to be `K(ℤ, 1)` and `K(ℤᵏ, 1)` by direct
computation of their homotopy groups; this states the underlying general principle.

## Main declarations

* `IsQuotientCoveringMap.isEilenbergMacLaneSpaceOne_realTopologicalVectorSpace`:
  **the orbit space of a free, properly discontinuous action of `G` on a real topological
  vector space is a `K(G, 1)`**.
-/

public section

open TauCeti
open scoped Topology Topology.Homotopy

namespace IsQuotientCoveringMap

variable {V X G : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [TopologicalSpace X] [Group G] [MulAction G V]
  {f : V → X} {v : V} {x : X}

/-- **The orbit space of a free, properly discontinuous action of `G` on a real topological
vector space is a `K(G, 1)`.**

The hypothesis is exactly that the orbit map `f` is a quotient covering map for `G`; the
asphericity and the identification of the fundamental group with `G` are then automatic. -/
theorem isEilenbergMacLaneSpaceOne_realTopologicalVectorSpace
    (hf : IsQuotientCoveringMap f G) (hv : f v = x) :
    IsEilenbergMacLaneSpaceOne G X x :=
  hf.isEilenbergMacLaneSpaceOne hv fun _ ↦ inferInstance

end IsQuotientCoveringMap

end
