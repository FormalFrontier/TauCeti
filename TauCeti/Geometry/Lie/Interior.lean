/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Interior points of Lie groups

Every point of a positive-smoothness Lie group manifold is an interior point. It suffices to find
one interior point in a chart and transport it to the identity by smooth left multiplication.

This supplies a prerequisite for Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main results

* `LieGroup.isInteriorPoint_one`: the identity of a Lie group is an interior point.

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

/-- The identity of a positive-smoothness Lie group manifold is an interior point. -/
theorem LieGroup.isInteriorPoint_one {n : WithTop ℕ∞} [LieGroup I n G] (hn : n ≠ 0) :
    I.IsInteriorPoint (1 : G) := by
  obtain ⟨y, hy⟩ := interior_extChartAt_target_nonempty I (1 : G)
  let x := (extChartAt I (1 : G)).symm y
  have hy_target : y ∈ (extChartAt I (1 : G)).target := interior_subset hy
  have hx_source : x ∈ (chartAt H (1 : G)).source := by
    rw [← extChartAt_source I (1 : G)]
    exact (extChartAt I (1 : G)).map_target hy_target
  have hx : I.IsInteriorPoint x := by
    rw [I.isInteriorPoint_iff_of_mem_atlas hn (chart_mem_atlas H (1 : G)) hx_source]
    change extChartAt I (1 : G) x ∈ interior (extChartAt I (1 : G)).target
    rwa [(extChartAt I (1 : G)).right_inv hy_target]
  have htranslate :=
    ((Diffeomorph.smul I I n x⁻¹).isLocalDiffeomorph x).isInteriorPoint_iff hn |>.mp hx
  simpa [x] using htranslate
