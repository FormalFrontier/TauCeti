/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Exponential.Basic

/-!
# Parameter dependence of invariant integral curves

This file begins the analytic parameter-dependence theory for the invariant integral curves that
define the Lie-group exponential. In the identity chart, the tangent vector and group coordinate
form an autonomous ODE on the product model space. Picard--Lindelöf then supplies a single local
flow, continuous jointly in its initial condition and time, for all sufficiently small tangent
vectors.

## Main results

* `mulInvariantCoordinateVectorField`: the invariant vector field in the identity chart, with its
  generating tangent vector included as a parameter.
* `contDiffAt_mulInvariantCoordinateVectorField`: this coordinate vector field is smooth near the
  zero vector and the identity.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The exponential map".
-/

public section

open Bundle Function Manifold VectorField
open scoped ContDiff Manifold Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [IsManifold I 1 G] [IsManifold I 2 G]

/-- The left-invariant vector field, expressed in the identity chart and parameterized by its
generating tangent vector in the model space. -/
noncomputable def mulInvariantCoordinateVectorField (p : E × E) : E :=
  let g := (extChartAt I (1 : G)).symm p.2
  tangentCoordChange I g (1 : G) g
    (mulInvariantVectorField
      ((groupLieAlgebraEquivModelSpace (I := I) (G := G)).symm p.1) g)

/-- The coordinate expression of the parameterized left-invariant vector field is smooth near the
zero tangent vector and the identity. -/
theorem contDiffAt_mulInvariantCoordinateVectorField
    [ContMDiffMul I ∞ G] [BoundarylessManifold I G] :
    ContDiffAt ℝ ∞ (mulInvariantCoordinateVectorField (I := I) (G := G))
      (0, extChartAt I (1 : G) (1 : G)) := by
  letI : ContMDiffMul I (∞ + 1) G := by
    simpa using (inferInstance : ContMDiffMul I ∞ G)
  let V : E × G → TangentBundle I G := fun p =>
    ⟨p.2, mulInvariantVectorField
      ((groupLieAlgebraEquivModelSpace (I := I) (G := G)).symm p.1) p.2⟩
  have hV : ContMDiff (𝓘(ℝ, E).prod I) I.tangent ∞ V :=
    contMDiff_mulInvariantVectorField_modelSpace (n := ∞)
  have hV₀ := hV.contMDiffAt (x := ((0 : E), (1 : G)))
  rw [contMDiffAt_iff] at hV₀
  have h := hV₀.2.contDiffAt
    (range_mem_nhds_isInteriorPoint BoundarylessManifold.isInteriorPoint)
  let w : E × E → E := fun x =>
    ((extChartAt I.tangent (V (0, 1)) ∘ V ∘
      (extChartAt (𝓘(ℝ, E).prod I) (0, 1)).symm) x).2
  have hw : w = mulInvariantCoordinateVectorField (I := I) (G := G) := by
    funext p
    change tangentCoordChange I ((extChartAt I (1 : G)).symm p.2) (1 : G)
      ((extChartAt I (1 : G)).symm p.2)
        (mulInvariantVectorField
          ((groupLieAlgebraEquivModelSpace (I := I) (G := G)).symm p.1)
          ((extChartAt I (1 : G)).symm p.2)) =
      mulInvariantCoordinateVectorField (I := I) (G := G) p
    rfl
  rw [← hw]
  simpa only [w, extChartAt_prod, extChartAt_self_apply, modelWithCornersSelf_coe,
    PartialEquiv.prod_coe, PartialEquiv.refl_coe, id_eq] using h.snd
