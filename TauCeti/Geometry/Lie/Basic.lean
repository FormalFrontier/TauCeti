/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Basic facts about Lie groups

This file records lightweight consequences of the Lie-group regularity hierarchy.

## Main results

* `t2Space_of_lieGroup`: a Lie group modeled on a normed space is Hausdorff.
* `LieGroup.minSmoothnessThree`: a `C³` Lie group over an RCL-like field has the regularity
  required by Mathlib's tangent Lie algebra.
-/

public section

open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

omit [IsRCLikeNormedField 𝕜] in
/-- A Lie group modeled on a normed space is Hausdorff. -/
theorem t2Space_of_lieGroup {n : ℕ∞ω} [LieGroup I n G] : T2Space G := by
  let _ : T1Space G := I.t1Space G
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I n
  exact IsTopologicalGroup.t2Space_iff_one_closed.mpr isClosed_singleton

/-- A `C³` Lie group over an RCL-like field has the regularity required by Mathlib's tangent Lie
algebra. This theorem is deliberately not a global instance, so the downgrade applies only in files
that opt in with `attribute [local instance] LieGroup.minSmoothnessThree`. -/
theorem LieGroup.minSmoothnessThree [LieGroup I 3 G] :
    LieGroup I (minSmoothness 𝕜 3) G := by
  simpa using (inferInstance : LieGroup I 3 G)
