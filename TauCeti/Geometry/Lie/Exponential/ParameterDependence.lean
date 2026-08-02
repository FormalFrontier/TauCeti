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
* `exists_continuousOn_local_mulInvariantCoordinateFlow`: a continuous local flow on a uniform
  closed neighborhood of the zero vector and the identity coordinate.

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

/-- Near the zero tangent vector and the identity coordinate, the parameterized invariant ODE has
a single flow that is continuous jointly in its initial condition and time. The tangent-vector
coordinate is frozen by the ODE; the second coordinate follows the invariant vector field. -/
theorem exists_continuousOn_local_mulInvariantCoordinateFlow
    [FiniteDimensional ℝ E] [ContMDiffMul I ∞ G] [BoundarylessManifold I G] :
    ∃ (α : (E × E) × ℝ → E × E) (δ : ℝ) (r : NNReal), 0 < δ ∧ 0 < r ∧
      ContinuousOn α
        (Metric.closedBall ((0 : E), extChartAt I (1 : G) (1 : G)) r ×ˢ
          Set.Icc (-δ) δ) ∧
      ∀ x ∈ Metric.closedBall ((0 : E), extChartAt I (1 : G) (1 : G)) r,
        α (x, 0) = x ∧
          (∀ t ∈ Set.Icc (-δ) δ,
            HasDerivWithinAt (fun s => α (x, s))
              ((0 : E),
                mulInvariantCoordinateVectorField (I := I) (G := G) (α (x, t)))
              (Set.Icc (-δ) δ) t) ∧
          ∀ t ∈ Set.Icc (-δ) δ, (α (x, t)).1 = x.1 := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let center : E × E := (0, extChartAt I (1 : G) (1 : G))
  let F : E × E → E × E := fun p =>
    (0, mulInvariantCoordinateVectorField (I := I) (G := G) p)
  have hF : ContDiffAt ℝ 1 F center := by
    exact contDiffAt_const.prodMk
      (contDiffAt_mulInvariantCoordinateVectorField.of_le (by norm_num))
  obtain ⟨δ, hδ, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hF
  obtain ⟨α, hα, hαcont⟩ :=
    (hpl (0 : ℝ)).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have hα' : ∀ x ∈ Metric.closedBall center r,
      α (x, 0) = x ∧ ∀ t ∈ Set.Icc (-δ) δ,
        HasDerivWithinAt (fun s => α (x, s))
          ((0 : E), mulInvariantCoordinateVectorField (I := I) (G := G) (α (x, t)))
          (Set.Icc (-δ) δ) t := by
    intro x hx
    simpa only [F, zero_sub, zero_add] using hα x hx
  refine ⟨α, δ, r, hδ, hr, ?_, ?_⟩
  · simpa only [center, zero_sub, zero_add] using hαcont
  · intro x hx
    have hx' : x ∈ Metric.closedBall center r := by simpa only [center] using hx
    refine ⟨(hα' x hx').1, (hα' x hx').2, ?_⟩
    let β : ℝ → E := fun t => (α (x, t)).1
    have hβ : ∀ t ∈ Set.Icc (-δ) δ,
        HasDerivWithinAt β 0 (Set.Icc (-δ) δ) t := by
      intro t ht
      change HasDerivWithinAt
        ((ContinuousLinearMap.fst ℝ E E) ∘ fun s => α (x, s)) 0
          (Set.Icc (-δ) δ) t
      simpa using (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivWithinAt t
        ((hα' x hx').2 t ht)
    have hconst := constant_of_derivWithin_zero
      (fun t ht => (hβ t ht).differentiableWithinAt)
      (fun t ht => (hβ t (Set.Ico_subset_Icc_self ht)).derivWithin
        ((uniqueDiffOn_Icc (by linarith)).uniqueDiffWithinAt
          (Set.Ico_subset_Icc_self ht)))
    intro t ht
    have hzero : (0 : ℝ) ∈ Set.Icc (-δ) δ := by constructor <;> linarith
    change β t = x.1
    exact (hconst t ht).trans ((hconst 0 hzero).symm.trans
      (congrArg Prod.fst (hα' x hx').1))
