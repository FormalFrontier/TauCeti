/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra
public import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

/-!
# Integral curves of invariant vector fields

Left-invariant vector fields on real Lie groups modeled on complete spaces are complete. Local
integral curves around the identity can be translated to give a uniform existence interval around
every point, after which Mathlib's uniform-time theorem produces global integral curves.

## Main results

* `exists_isMIntegralCurve_mulInvariantVectorField`: every left-invariant vector field has a global
  integral curve through every point.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The exponential map".
-/

public section

open Function Manifold Set
open scoped Manifold

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

namespace IsMIntegralCurveOn

/-- Left translation preserves integral curves of a left-invariant vector field. -/
theorem const_mul_mulInvariantVectorField [LieGroup I (minSmoothness ℝ 3) G]
    {v : GroupLieAlgebra I G} {γ : ℝ → G} {s : Set ℝ}
    (hγ : IsMIntegralCurveOn γ (mulInvariantVectorField v) s) (g : G) :
    IsMIntegralCurveOn (fun t ↦ g * γ t) (mulInvariantVectorField v) s := by
  intro t ht
  have hg : MDiffAt (fun x : G ↦ g * x) (γ t) :=
    (contMDiffAt_mul_left (n := minSmoothness ℝ 3)).mdifferentiableAt (by simp)
  have hder :
      (mfderiv% (fun x : G ↦ g * x) (γ t)).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (γ t))) =
        (1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (g * γ t)) := by
    have hvec : mfderiv% (fun x : G ↦ g * x) (γ t)
        (mulInvariantVectorField v (γ t)) = mulInvariantVectorField v (g * γ t) := by
      have D : (fun x : G ↦ (g * γ t) * x) =
          (fun x : G ↦ g * x) ∘ (fun x : G ↦ γ t * x) := by
        funext z
        simp [mul_assoc]
      rw [mulInvariantVectorField, mulInvariantVectorField, D]
      exact (mfderiv_comp_apply_of_eq (I' := I) (f := fun x : G ↦ γ t * x)
        (g := fun x : G ↦ g * x) (y := γ t) (1 : G)
        ((contMDiffAt_mul_left (n := minSmoothness ℝ 3)).mdifferentiableAt (by simp))
        ((contMDiffAt_mul_left (n := minSmoothness ℝ 3)).mdifferentiableAt (by simp))
        (by simp) v).symm
    calc
      _ = (1 : ℝ →L[ℝ] ℝ).smulRight
          (mfderiv% (fun x : G ↦ g * x) (γ t) (mulInvariantVectorField v (γ t))) := by
        apply ContinuousLinearMap.ext
        intro c
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.smulRight_apply, map_smul]
      _ = _ := by rw [hvec]
  change HasMFDerivAt[s] ((fun x : G ↦ g * x) ∘ γ) t
    ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (g * γ t)))
  rw [← hder]
  exact hg.hasMFDerivAt.comp_hasMFDerivWithinAt t (hγ t ht)

end IsMIntegralCurveOn

/-- Every left-invariant vector field on a real Lie group modeled on a complete space has a global
integral curve through every point. -/
theorem exists_isMIntegralCurve_mulInvariantVectorField [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) (x : G) :
    ∃ γ : ℝ → G, γ 0 = x ∧ IsMIntegralCurve γ (mulInvariantVectorField v) := by
  let V := mulInvariantVectorField v
  have hV : CMDiff 1 (fun g ↦ (⟨g, V g⟩ : TangentBundle I G)) :=
    (contMDiff_mulInvariantVectorField v).of_le (by simp)
  obtain ⟨γ, hγ0, hγ⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless (x₀ := (1 : G)) 0 hV.contMDiffAt
  obtain ⟨ε, hε, hγ⟩ := isMIntegralCurveAt_iff'.mp hγ
  rw [Real.ball_eq_Ioo] at hγ
  have hγ : IsMIntegralCurveOn γ V (Ioo (-ε) ε) := by
    simpa only [zero_sub, zero_add] using hγ
  apply exists_isMIntegralCurve_of_isMIntegralCurveOn hV hε
  intro y
  refine ⟨fun t ↦ y * γ t, by simp [hγ0], ?_⟩
  exact hγ.const_mul_mulInvariantVectorField y
