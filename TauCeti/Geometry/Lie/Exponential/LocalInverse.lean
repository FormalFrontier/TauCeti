/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import TauCeti.Geometry.Lie.Exponential.Derivative
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
/-!
# Local inverse of the Lie-group exponential

The smooth coordinate exponential has derivative the identity at zero, so the inverse function
theorem supplies a smooth local logarithm in model-space identity coordinates.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The exponential map".
-/
public section
open Function Manifold
open scoped ContDiff Manifold Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [IsManifold I 1 G]
local instance lieGroupMinSmoothnessLocalInverse [LieGroup I ∞ G] :
    LieGroup I (minSmoothness ℝ 3) G := by
  simpa using (inferInstance : LieGroup I (3 : ℕ∞ω) G)
/-- The tangent-space exponential expressed in model-space identity coordinates. -/
@[expose]
noncomputable def mulInvariantExpModelSpace [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] (v : E) : E := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact extChartAt I (1 : G)
    (mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G))
/-- The coordinate exponential sends zero to the identity coordinate. -/
@[simp]
theorem mulInvariantExpModelSpace_zero [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    mulInvariantExpModelSpace (I := I) (G := G) 0 =
      extChartAt I (1 : G) (1 : G) := by
  change extChartAt I (1 : G)
    (mulInvariantExp (I := I) (G := G) (0 : GroupLieAlgebra I G)) = _
  rw [mulInvariantExp_zero]
/-- The coordinate exponential is smooth at zero. -/
theorem contDiffAt_mulInvariantExpModelSpace_zero [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    ContDiffAt ℝ ∞ (mulInvariantExpModelSpace (I := I) (G := G)) 0 := by
  rw [show mulInvariantExpModelSpace (I := I) (G := G) =
      fun v : E => extChartAt I (1 : G)
        (mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G)) by
    funext v
    rw [mulInvariantExpModelSpace]]
  exact contDiffAt_mulInvariantExp_modelSpace_zero (I := I) (G := G)
/-- The coordinate exponential has derivative the identity at zero. -/
theorem hasFDerivAt_mulInvariantExpModelSpace_zero [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    HasFDerivAt (mulInvariantExpModelSpace (I := I) (G := G))
      (ContinuousLinearMap.id ℝ E) 0 := by
  rw [show mulInvariantExpModelSpace (I := I) (G := G) =
      fun v : E => extChartAt I (1 : G)
        (mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G)) by
    funext v
    rw [mulInvariantExpModelSpace]]
  exact hasFDerivAt_mulInvariantExp_modelSpace_zero (I := I) (G := G)
/-- The coordinate exponential on the canonical neighborhoods selected by the inverse function
theorem. -/
@[expose]
noncomputable def mulInvariantExpLocalHomeomorph [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] : OpenPartialHomeomorph E E := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let h' : HasFDerivAt (mulInvariantExpModelSpace (I := I) (G := G))
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) 0 := by
    simpa using hasFDerivAt_mulInvariantExpModelSpace_zero (I := I) (G := G)
  exact (contDiffAt_mulInvariantExpModelSpace_zero (I := I) (G := G))
    |>.toOpenPartialHomeomorph _ h' (by simp)
/-- The local homeomorphism agrees with the coordinate exponential. -/
@[simp]
theorem mulInvariantExpLocalHomeomorph_apply [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] (v : E) :
    mulInvariantExpLocalHomeomorph (I := I) (G := G) v =
      mulInvariantExpModelSpace (I := I) (G := G) v := by
  unfold mulInvariantExpLocalHomeomorph
  rfl

/-- Zero belongs to the source of the local coordinate exponential. -/
theorem zero_mem_mulInvariantExpLocalHomeomorph_source [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G] :
    0 ∈ (mulInvariantExpLocalHomeomorph (I := I) (G := G)).source := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let h' : HasFDerivAt (mulInvariantExpModelSpace (I := I) (G := G))
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) 0 := by
    simpa using hasFDerivAt_mulInvariantExpModelSpace_zero (I := I) (G := G)
  exact (contDiffAt_mulInvariantExpModelSpace_zero (I := I) (G := G))
    |>.mem_toOpenPartialHomeomorph_source h' (by simp)

/-- The identity coordinate belongs to the target of the local coordinate exponential. -/
theorem identity_mem_mulInvariantExpLocalHomeomorph_target [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G] :
    extChartAt I (1 : G) (1 : G) ∈
      (mulInvariantExpLocalHomeomorph (I := I) (G := G)).target := by
  rw [← mulInvariantExpModelSpace_zero (I := I) (G := G)]
  exact (mulInvariantExpLocalHomeomorph (I := I) (G := G)).map_source
    zero_mem_mulInvariantExpLocalHomeomorph_source

/-- The canonical local logarithm in model-space identity coordinates. -/
@[expose]
noncomputable def mulInvariantLogModelSpace [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] : E → E :=
  (mulInvariantExpLocalHomeomorph (I := I) (G := G)).symm

/-- The coordinate logarithm sends the identity coordinate to zero. -/
@[simp]
theorem mulInvariantLogModelSpace_identity [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    mulInvariantLogModelSpace (I := I) (G := G)
      (I (chartAt H (1 : G) (1 : G))) = 0 := by
  change mulInvariantLogModelSpace (I := I) (G := G)
    (extChartAt I (1 : G) (1 : G)) = 0
  rw [← mulInvariantExpModelSpace_zero (I := I) (G := G)]
  exact (mulInvariantExpLocalHomeomorph (I := I) (G := G)).left_inv
    zero_mem_mulInvariantExpLocalHomeomorph_source

/-- Locally around zero, logarithm is a left inverse to the coordinate exponential. -/
theorem eventually_mulInvariantLogModelSpace_exp [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    ∀ᶠ v in 𝓝 (0 : E),
      mulInvariantLogModelSpace (I := I) (G := G)
        (mulInvariantExpModelSpace (I := I) (G := G) v) = v :=
  (mulInvariantExpLocalHomeomorph (I := I) (G := G)).eventually_left_inverse
    zero_mem_mulInvariantExpLocalHomeomorph_source

/-- Locally around the identity coordinate, exponential is a left inverse to logarithm. -/
theorem eventually_mulInvariantExpModelSpace_log [FiniteDimensional ℝ E] [LieGroup I ∞ G]
    [T2Space G] [BoundarylessManifold I G] :
    ∀ᶠ y in 𝓝 (extChartAt I (1 : G) (1 : G)),
      mulInvariantExpModelSpace (I := I) (G := G)
        (mulInvariantLogModelSpace (I := I) (G := G) y) = y := by
  rw [← mulInvariantExpModelSpace_zero (I := I) (G := G)]
  exact (mulInvariantExpLocalHomeomorph (I := I) (G := G)).eventually_right_inverse'
    zero_mem_mulInvariantExpLocalHomeomorph_source

/-- The coordinate logarithm is smooth at the identity coordinate. -/
theorem contDiffAt_mulInvariantLogModelSpace_identity [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G] :
    ContDiffAt ℝ ∞ (mulInvariantLogModelSpace (I := I) (G := G))
      (extChartAt I (1 : G) (1 : G)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let φ := mulInvariantExpLocalHomeomorph (I := I) (G := G)
  change ContDiffAt ℝ ∞ φ.symm (extChartAt I (1 : G) (1 : G))
  have hpre : φ.symm (extChartAt I (1 : G) (1 : G)) = 0 := by
    exact mulInvariantLogModelSpace_identity (I := I) (G := G)
  have hφ : (φ : E → E) = mulInvariantExpModelSpace (I := I) (G := G) := by
    funext v
    exact mulInvariantExpLocalHomeomorph_apply (I := I) (G := G) v
  apply φ.contDiffAt_symm (f₀' := ContinuousLinearEquiv.refl ℝ E)
    identity_mem_mulInvariantExpLocalHomeomorph_target
  · rw [hpre, hφ]
    simpa using hasFDerivAt_mulInvariantExpModelSpace_zero (I := I) (G := G)
  · rw [hpre, hφ]
    exact contDiffAt_mulInvariantExpModelSpace_zero (I := I) (G := G)
