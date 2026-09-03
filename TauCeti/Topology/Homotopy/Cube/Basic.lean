/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Topology.Connected.PathConnected

/-!
# Path-connectedness of the cube and its boundary

Mathlib's higher homotopy groups `π_ n X x` are built from generalized loops `Ω^ N X x`,
continuous maps `I^N → X` sending the cube boundary `Cube.boundary N`
(`{y | ∃ i, y i = 0 ∨ y i = 1}`) to the base point. Reasoning about `π_ n` for `n ≥ 2`
needs to know how the cube and, crucially, its *boundary* are connected: the boundary of an
`n`-cube is the topological sphere `S^{n-1}`, which is connected precisely when `n ≥ 2`.
Mathlib records the cube boundary set but proves nothing about its connectivity.

This file supplies that missing input:

* the whole cube `I^N` is path connected (`TauCeti.isPathConnected_cube`);
* its boundary is path connected as soon as the index type has at least two elements
  (`TauCeti.isPathConnected_cubeBoundary`), with the `Fin` reformulation
  `TauCeti.isPathConnected_cubeBoundary_fin` for `2 ≤ n`, plus the `IsConnected` and
  `IsPreconnected` corollaries.

The paths are elementary: a coordinate is dragged to `0` along the straight line
`pathTowardZero`, and any boundary point is joined to the corner `0` in two phases that each
keep one coordinate pinned at an endpoint, so the whole journey stays inside the boundary.
The two-element hypothesis is exactly what lets the second phase pin a *different* coordinate
at `0` while releasing the first.

This realises the "(pre)connectedness of cubes and cube boundaries for `n ≥ 2`" part of the
higher-homotopy API requested in the universal-covers roadmap, Stage 3 item 9
(`TauCetiRoadmap/UniversalCovers/README.md`), a prerequisite for proving that a covering map
induces isomorphisms on `π_ n` for `n ≥ 2`.

## Main declarations

* `TauCeti.pathTowardZero`: the straight-line path in `I` from `a` to `0`.
* `TauCeti.isPathConnected_cube`: `I^N` is path connected.
* `TauCeti.zero_mem_cubeBoundary`: the corner `0` lies on the boundary.
* `TauCeti.isPathConnected_cubeBoundary`: for `[Nontrivial N]`, `Cube.boundary N` is path
  connected.
* `TauCeti.isPathConnected_cubeBoundary_fin`: the `Fin` version for `2 ≤ n`.
-/

public section

namespace TauCeti

open scoped Topology
open unitInterval

variable {N : Type*}

/-- The straight-line path in the unit interval `I` from `a` to `0`, given by `t ↦ a * σ t`
where `σ` is the interval symmetry `t ↦ 1 - t`. -/
@[expose] def pathTowardZero (a : I) : Path a 0 where
  toFun t := a * σ t
  continuous_toFun := by
    rw [continuous_induced_rng]
    simp only [Function.comp_def, Set.Icc.coe_mul, coe_symm_eq]
    fun_prop
  source' := by simp [symm_zero]
  target' := by simp [symm_one]

@[simp]
theorem pathTowardZero_apply (a t : I) : pathTowardZero a t = a * σ t := rfl

/-- The cube `I^N` is path connected: every point is joined to the corner `0` by the pointwise
product of the coordinate paths `pathTowardZero`. -/
theorem isPathConnected_cube : IsPathConnected (Set.univ : Set (I^N)) :=
  ⟨fun _ => 0, Set.mem_univ _, fun {y} _ =>
    ⟨(Path.pi fun j => pathTowardZero (y j)).symm, fun _ => Set.mem_univ _⟩⟩

/-- The corner `0` lies on the boundary of the cube (any coordinate is `0`). -/
theorem zero_mem_cubeBoundary [Nonempty N] : (0 : I^N) ∈ Cube.boundary N :=
  ⟨Classical.arbitrary N, Or.inl rfl⟩

section Paths

variable [DecidableEq N]

/-- The path in `I^N` dragging every coordinate other than `i₀` to `0`, while holding the
`i₀`-coordinate fixed at `y i₀`. Its endpoint is supported on `i₀`. -/
private def cubeCollapseComplement (i₀ : N) (y : I^N) :
    Path y (Function.update (0 : I^N) i₀ (y i₀)) where
  toFun t := Function.update (fun j => pathTowardZero (y j) t) i₀ (y i₀)
  continuous_toFun :=
    (continuous_pi fun j => (pathTowardZero (y j)).continuous).update i₀ continuous_const
  source' := by
    simp only [Path.source]
    exact Function.update_eq_self i₀ y
  target' := by
    simp only [Path.target]
    rfl

@[simp]
private theorem cubeCollapseComplement_apply (i₀ : N) (y : I^N) (t : I) :
    cubeCollapseComplement i₀ y t
      = Function.update (fun j => pathTowardZero (y j) t) i₀ (y i₀) := rfl

/-- The path in `I^N` dragging the `i₀`-coordinate from `a` to `0`, with every other
coordinate held at `0`. It runs from the point supported on `i₀` back to the corner `0`. -/
private def cubeCollapseCoord (i₀ : N) (a : I) : Path (Function.update (0 : I^N) i₀ a) 0 where
  toFun t := Function.update (0 : I^N) i₀ (pathTowardZero a t)
  continuous_toFun := continuous_const.update i₀ (pathTowardZero a).continuous
  source' := by simp only [Path.source]
  target' := by
    simp only [Path.target]
    exact Function.update_eq_self i₀ (0 : I^N)

@[simp]
private theorem cubeCollapseCoord_apply (i₀ : N) (a t : I) :
    cubeCollapseCoord i₀ a t = Function.update (0 : I^N) i₀ (pathTowardZero a t) := rfl

end Paths

/-- The boundary of the cube `I^N` is path connected once the index type has at least two
elements. Any boundary point `y`, extreme in some coordinate `i₀`, is joined to the corner `0`
in two phases: first collapse every other coordinate to `0` (keeping `i₀` extreme), then
collapse the `i₀`-coordinate (keeping a *different* coordinate `j₀` at `0`). The two-element
hypothesis provides the index `j₀ ≠ i₀`. -/
theorem isPathConnected_cubeBoundary [Nontrivial N] : IsPathConnected (Cube.boundary N) := by
  classical
  refine ⟨0, zero_mem_cubeBoundary, fun {y} hy => ?_⟩
  obtain ⟨i₀, hi₀⟩ := hy
  obtain ⟨j₀, hj₀⟩ := exists_ne i₀
  have h1 : JoinedIn (Cube.boundary N) y (Function.update (0 : I^N) i₀ (y i₀)) :=
    ⟨cubeCollapseComplement i₀ y, fun t =>
      ⟨i₀, by rw [cubeCollapseComplement_apply, Function.update_self]; exact hi₀⟩⟩
  have h2 : JoinedIn (Cube.boundary N) (Function.update (0 : I^N) i₀ (y i₀)) 0 :=
    ⟨cubeCollapseCoord i₀ (y i₀), fun t =>
      ⟨j₀, Or.inl <| by rw [cubeCollapseCoord_apply, Function.update_of_ne hj₀]; rfl⟩⟩
  exact (h1.trans h2).symm

/-- The boundary of the cube `I^N` is connected once the index type has at least two elements. -/
theorem isConnected_cubeBoundary [Nontrivial N] : IsConnected (Cube.boundary N) :=
  isPathConnected_cubeBoundary.isConnected

/-- The boundary of the cube `I^N` is preconnected once the index type has at least two
elements. -/
theorem isPreconnected_cubeBoundary [Nontrivial N] : IsPreconnected (Cube.boundary N) :=
  isConnected_cubeBoundary.isPreconnected

/-- The boundary of the `n`-cube `I^(Fin n)` is path connected for `2 ≤ n`. This is the shape
in which the connectivity feeds into `π_ n` for `n ≥ 2`. -/
theorem isPathConnected_cubeBoundary_fin {n : ℕ} (hn : 2 ≤ n) :
    IsPathConnected (Cube.boundary (Fin n)) :=
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  isPathConnected_cubeBoundary

end TauCeti
