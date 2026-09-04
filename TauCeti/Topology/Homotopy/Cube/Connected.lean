/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Cube.Basic

/-!
# Connectedness consequences for cubes

`TauCeti.Topology.Homotopy.Cube.Basic` constructs paths in a cube and in its boundary.  This
module records the `Fin`-indexed path-connectedness form and direct `JoinedIn` elimination lemmas.
Keeping these consequences named is useful when an argument needs a direct path witness (for
example, to apply a covering-space or homotopy extension lemma) without rebuilding it at each use
site.

The boundary statements require a nontrivial index type: the boundary of a one-dimensional cube
is disconnected, while the boundary of a cube with at least two coordinates is path connected.
These are the cube-connectivity prerequisites in Stage 3, item 9 of
`TauCetiRoadmap/UniversalCovers/README.md`.
-/

public section

namespace TauCeti

open scoped Topology
open unitInterval

variable {N : Type*}

/-- Any two points of a cube can be joined by a path lying in the cube. -/
theorem joinedIn_cube (x y : I^N) : JoinedIn (Set.univ : Set (I^N)) x y :=
  isPathConnected_cube.joinedIn x (Set.mem_univ x) y (Set.mem_univ y)

section Fin

variable (n : ℕ)

/-- The `n`-cube is path connected, in the finite-index form used by `π_ n`. -/
theorem isPathConnected_cube_fin : IsPathConnected (Set.univ : Set (I^(Fin n))) :=
  isPathConnected_cube

end Fin

section Boundary

variable [Nontrivial N]

/-- Any two points of a cube boundary can be joined by a path staying in that boundary. -/
theorem joinedIn_cubeBoundary {x y : I^N} (hx : x ∈ Cube.boundary N)
    (hy : y ∈ Cube.boundary N) : JoinedIn (Cube.boundary N) x y :=
  isPathConnected_cubeBoundary.joinedIn x hx y hy

section Fin

variable {n : ℕ} (hn : 2 ≤ n)

/-- The boundary of the `n`-cube is connected for `2 ≤ n`. -/
theorem isConnected_cubeBoundary_fin (hn : 2 ≤ n) : IsConnected (Cube.boundary (Fin n)) :=
  (isPathConnected_cubeBoundary_fin hn).isConnected

/-- The boundary of the `n`-cube is preconnected for `2 ≤ n`. -/
theorem isPreconnected_cubeBoundary_fin (hn : 2 ≤ n) : IsPreconnected (Cube.boundary (Fin n)) :=
  (isConnected_cubeBoundary_fin hn).isPreconnected

/-- Any two points of the boundary of the `n`-cube can be joined inside it. -/
theorem joinedIn_cubeBoundary_fin (hn : 2 ≤ n) {x y : I^(Fin n)}
    (hx : x ∈ Cube.boundary (Fin n)) (hy : y ∈ Cube.boundary (Fin n)) :
    JoinedIn (Cube.boundary (Fin n)) x y :=
  (isPathConnected_cubeBoundary_fin hn).joinedIn x hx y hy

end Fin

end Boundary

end TauCeti
