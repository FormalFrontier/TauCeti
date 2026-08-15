/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Exponential.LocalInverse

/-!
# Derivatives involving the local Lie logarithm

This file records first-order interactions between the local logarithm, the exponential, and
group multiplication.

## Main result

* `hasDerivAt_mulInvariantLog_mulInvariantExp_smul_mul_mulInvariantExp_smul`: the local logarithm
  of the product of two exponential lines has initial derivative `X + Y`.
-/

public section

open Function Manifold
open scoped ContDiff Manifold Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [IsManifold I 1 G]

attribute [local instance] LieGroup.minSmoothnessThree

-- Multiplication's tangent-map API and `extChartAt` use dependent tangent-space synonyms at
-- definitionally equal basepoints. The conversions below state each semantic boundary explicitly.
private theorem hasFDerivAt_extChartAt_mulInvariantExp_smul_mul_mulInvariantExp_smul
    [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
    (X Y : GroupLieAlgebra I G) :
    HasFDerivAt
      (fun t : ℝ => extChartAt I (1 : G)
        (mulInvariantExp (I := I) (G := G) (t • X) *
          mulInvariantExp (I := I) (G := G) (t • Y)))
      ((1 : ℝ →L[ℝ] ℝ).smulRight ((show E from X) + (show E from Y))) 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hX := hasMFDerivAt_mulInvariantExp_smul_zero (I := I) (G := G) X
  have hY := hasMFDerivAt_mulInvariantExp_smul_zero (I := I) (G := G) Y
  have hpair := hX.prodMk hY
  have hmul := (contMDiff_mul (G := G) I ∞).contMDiffAt
    (x := (mulInvariantExp (I := I) (G := G) ((0 : ℝ) • X),
      mulInvariantExp (I := I) (G := G) ((0 : ℝ) • Y)))
    |>.mdifferentiableAt (by simp)
  have hcurve := hmul.hasMFDerivAt.comp 0 hpair
  have hzero :
      mulInvariantExp (I := I) (G := G) ((0 : ℝ) • X) *
        mulInvariantExp (I := I) (G := G) ((0 : ℝ) • Y) = (1 : G) := by
    simp
  rw [hzero] at hcurve
  have hsource :
      mulInvariantExp (I := I) (G := G) ((0 : ℝ) • X) *
          mulInvariantExp (I := I) (G := G) ((0 : ℝ) • Y) ∈
        (chartAt H (1 : G)).source := by
    rw [hzero]
    exact mem_chart_source H (1 : G)
  have hext := (mdifferentiableAt_extChartAt (I := I)
    (x := (1 : G)) hsource).hasMFDerivAt
  have hchart := hext.comp 0 hcurve
  simp only [Function.comp_apply] at hchart
  rw [hzero] at hchart
  apply hchart.mdifferentiableAt.differentiableAt.hasFDerivAt.congr_fderiv
  rw [← mfderiv_eq_fderiv, hchart.mfderiv]
  apply DFunLike.coe_injective
  funext t
  rw [show (0 : ℝ) • X = 0 by exact zero_smul ℝ X,
    show (0 : ℝ) • Y = 0 by exact zero_smul ℝ Y,
    mulInvariantExp_zero]
  have hmul_apply := mfderiv_mul_apply_one (I := I) (G := G) (t • X) (t • Y)
  have hmul_model := congrArg (fun Z : GroupLieAlgebra I G => show E from Z)
    (hmul_apply.trans (smul_add t X Y).symm)
  rw [mfderiv_extChartAt_self]
  -- `extChartAt` lands in the self-model, whose tangent space is the model-space synonym `E`.
  -- Expose that final chart boundary before applying the model-space equality above.
  change
    (show E from
      (mfderiv (I.prod I) I (fun p : G × G => p.1 * p.2) ((1, 1) : G × G))
        (t • X, t • Y)) =
      (show E from t • (X + Y))
  exact hmul_model

/-- The local logarithm of the product of two exponential lines has initial derivative `X + Y`. -/
theorem hasDerivAt_mulInvariantLog_mulInvariantExp_smul_mul_mulInvariantExp_smul
    [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
    (X Y : GroupLieAlgebra I G) :
    HasDerivAt
      (fun t : ℝ => (show E from mulInvariantLog (I := I) (G := G)
        (mulInvariantExp (I := I) (G := G) (t • X) *
          mulInvariantExp (I := I) (G := G) (t • Y))))
      ((show E from X) + (show E from Y)) 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hlog := hasFDerivAt_mulInvariantLogChart_one (I := I) (G := G)
  have hcurve :=
    hasFDerivAt_extChartAt_mulInvariantExp_smul_mul_mulInvariantExp_smul
      (I := I) (G := G) X Y
  have hlog' : HasFDerivAt (mulInvariantLogChart (I := I) (G := G))
      (ContinuousLinearMap.id ℝ E)
      (extChartAt I (1 : G)
        (mulInvariantExp (I := I) (G := G) ((0 : ℝ) • X) *
          mulInvariantExp (I := I) (G := G) ((0 : ℝ) • Y))) := by
    simpa using hlog
  have hcomp' := (hlog'.comp 0 hcurve).hasDerivAt
  rw [show (mulInvariantLogChart (I := I) (G := G) ∘
      fun t : ℝ => extChartAt I (1 : G)
        (mulInvariantExp (I := I) (G := G) (t • X) *
          mulInvariantExp (I := I) (G := G) (t • Y))) =
      fun t : ℝ => (show E from mulInvariantLog (I := I) (G := G)
        (mulInvariantExp (I := I) (G := G) (t • X) *
          mulInvariantExp (I := I) (G := G) (t • Y))) by
    funext t
    exact (mulInvariantLog_eq_chart (I := I) (G := G) _).symm] at hcomp'
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] using hcomp'

end
