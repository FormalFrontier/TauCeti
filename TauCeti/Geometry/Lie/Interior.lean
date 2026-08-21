/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Interior points of group manifolds

Every point of a group manifold whose multiplication is `C^n`, for `n ≠ 0`, is an interior point;
smooth inversion is not required. It suffices to find one interior point in a chart and transport
it to the desired point by `C^n` left multiplication.

This supplies a prerequisite for Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main results

* `ContMDiffMul.isInteriorPoint`: every point of a group manifold with `C^n` multiplication, for
  `n ≠ 0`, is an interior point.
* `ContMDiffMul.boundarylessManifold`: a group manifold with `C^1` multiplication is boundaryless
  (opt-in, not an instance).

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The group adjoint".
-/

public section

open ModelWithCorners

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- Every point of a group manifold with `C^n` multiplication, for `n ≠ 0`, is an interior point. -/
theorem ContMDiffMul.isInteriorPoint {n : WithTop ℕ∞} [ContMDiffMul I n G] (hn : n ≠ 0)
    (g : G) : I.IsInteriorPoint g := by
  obtain ⟨y, hy⟩ := interior_extChartAt_target_nonempty I (1 : G)
  let x := (extChartAt I (1 : G)).symm y
  have hy_target : y ∈ (extChartAt I (1 : G)).target := interior_subset hy
  have hx_source : x ∈ (chartAt H (1 : G)).source := by
    rw [← extChartAt_source I (1 : G)]
    exact (extChartAt I (1 : G)).map_target hy_target
  have hx : I.IsInteriorPoint x := by
    rw [I.isInteriorPoint_iff_of_mem_atlas hn (chart_mem_atlas H (1 : G)) hx_source]
    -- `extChartAt` is definitionally the extension of `chartAt` used by the preceding theorem.
    change extChartAt I (1 : G) x ∈ interior (extChartAt I (1 : G)).target
    rwa [(extChartAt I (1 : G)).right_inv hy_target]
  have htranslate :=
    ((Diffeomorph.smul I I n (g * x⁻¹)).isLocalDiffeomorph x).isInteriorPoint_iff hn |>.mp hx
  simpa [x] using htranslate

/-- A group manifold with `C^1` multiplication is boundaryless.

This theorem is deliberately not an instance: consumers can opt in with
`attribute [local instance] ContMDiffMul.boundarylessManifold`. -/
theorem ContMDiffMul.boundarylessManifold [ContMDiffMul I 1 G] : BoundarylessManifold I G :=
  ⟨ContMDiffMul.isInteriorPoint (n := 1) (by norm_num)⟩
