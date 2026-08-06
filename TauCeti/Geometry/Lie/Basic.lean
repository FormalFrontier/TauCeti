/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Basic facts about Lie groups

This file records lightweight consequences of the Lie-group regularity hierarchy.

## Main results

* `LieGroup.minSmoothnessThree`: a `C³` Lie group over an RCL-like field has the regularity
  required by Mathlib's tangent Lie algebra.
-/

public section

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- A `C³` Lie group over an RCL-like field has the regularity required by Mathlib's tangent Lie
algebra. This theorem is deliberately not a global instance; consumers activate it with
`attribute [local instance] LieGroup.minSmoothnessThree` to avoid typeclass loops. -/
theorem LieGroup.minSmoothnessThree [LieGroup I 3 G] :
    LieGroup I (minSmoothness 𝕜 3) G := by
  simpa using (inferInstance : LieGroup I 3 G)
