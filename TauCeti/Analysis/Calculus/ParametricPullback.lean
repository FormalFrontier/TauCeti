/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.VectorField
public import TauCeti.Analysis.Calculus.ParametricFDeriv
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse

/-!
# Differentiating a parametric pullback

For a differentiable vector field and a sufficiently smooth parametric family whose inverse spatial
Jacobian is differentiable, the derivative at a base time of its pullback is the Lie bracket
`[V, W]` of the family's parameter velocity `V` with the pulled-back field `W`, when the family
agrees with the identity to first order at the point. This is the vector-space calculus statement
underlying the infinitesimal adjoint action of a Lie group.

This supplies a prerequisite for Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main result

* `VectorField.hasDerivAt_parametric_pullback`: differentiating the parametric pullback gives the
  Lie bracket.
* `VectorField.hasDerivAt_parametric_pullback_of_completeSpace`: the Banach-space specialization.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The infinitesimal adjoint".
* Sébastien Gouëzel, `Mathlib/Analysis/Calculus/VectorField.lean`, definitions
  `VectorField.pullback` and `VectorField.lieBracket`.
-/

public section

noncomputable section

open ContinuousLinearMap
open scoped Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace VectorField

private theorem isInvertible_spatialFDeriv_of_eq_id {F : 𝕜 × E → E} {t₀ : 𝕜} {x : E}
    (hA0 : spatialFDeriv F x t₀ = ContinuousLinearMap.id 𝕜 E) :
    (spatialFDeriv F x t₀).IsInvertible := by
  rw [hA0]
  exact ⟨ContinuousLinearEquiv.refl 𝕜 E, rfl⟩

/-- Let `F` have the minimum smoothness needed for symmetric second derivatives at `(t₀, x)` and
agree with the identity to first order at `x` when `t = t₀`. If the inverse spatial-Jacobian
family is differentiable at `t₀` and `W` is differentiable at `x`, then the derivative of the
pullback of `W` along `F` is the Lie bracket `[V, W]`, where `V` is the parameter velocity of `F`
at `t₀`. -/
theorem hasDerivAt_parametric_pullback {F : 𝕜 × E → E} {W : E → E} {t₀ : 𝕜} {x : E}
    (hF : ContDiffAt 𝕜 (minSmoothness 𝕜 2) F (t₀, x)) (hF0 : F (t₀, x) = x)
    (hA0 : spatialFDeriv F x t₀ = ContinuousLinearMap.id 𝕜 E)
    (hInvDiff : DifferentiableAt 𝕜 (fun t => (spatialFDeriv F x t).inverse) t₀)
    (hW : DifferentiableAt 𝕜 W x) :
    HasDerivAt
      (fun t => pullback 𝕜 (fun y => F (t, y)) W x)
      (lieBracket 𝕜 (timeFDeriv F t₀) W x) t₀ := by
  have hA := hasDerivAt_spatialFDeriv hF
  have hz : HasDerivAt (fun t => F (t, x)) (timeFDeriv F t₀ x) t₀ := by
    have hFdiff : DifferentiableAt 𝕜 F (t₀, x) :=
      (hF.of_le le_minSmoothness).differentiableAt two_ne_zero
    exact hasDerivAt_parameterCurve hFdiff
  have hW0 : HasFDerivAt W (fderiv 𝕜 W x) (F (t₀, x)) := by
    simpa only [hF0] using hW.hasFDerivAt
  have hpull := hA.clm_inverse_apply (isInvertible_spatialFDeriv_of_eq_id hA0) hInvDiff
    (hW0.comp_hasDerivAt t₀ hz)
  have hslice : (fun t => pullback 𝕜 (fun y => F (t, y)) W x) =ᶠ[𝓝 t₀]
      fun t => (spatialFDeriv F x t).inverse (W (F (t, x))) := by
    have hpath : ContinuousAt (fun t : 𝕜 => (t, x)) t₀ := by fun_prop
    filter_upwards [hpath.eventually (hF.eventually (by norm_num))] with t ht
    simp only [pullback,
      fderiv_timeSlice ((ht.of_le le_minSmoothness).differentiableAt two_ne_zero)]
  have hpull' : HasDerivAt
      (fun t => (spatialFDeriv F x t).inverse (W (F (t, x))))
      (lieBracket 𝕜 (timeFDeriv F t₀) W x) t₀ := by
    simpa only [Function.comp_apply, hF0, hA0, ContinuousLinearMap.inverse_id,
      ContinuousLinearMap.id_apply, lieBracket] using hpull
  exact hpull'.congr_of_eventuallyEq hslice

/-- The Banach-space specialization of `hasDerivAt_parametric_pullback`, where differentiability
of the inverse spatial-Jacobian family follows automatically from invertibility at the base
point. -/
theorem hasDerivAt_parametric_pullback_of_completeSpace [CompleteSpace E]
    {F : 𝕜 × E → E} {W : E → E} {t₀ : 𝕜} {x : E}
    (hF : ContDiffAt 𝕜 (minSmoothness 𝕜 2) F (t₀, x)) (hF0 : F (t₀, x) = x)
    (hA0 : spatialFDeriv F x t₀ = ContinuousLinearMap.id 𝕜 E)
    (hW : DifferentiableAt 𝕜 W x) :
    HasDerivAt (fun t => pullback 𝕜 (fun y => F (t, y)) W x)
      (lieBracket 𝕜 (timeFDeriv F t₀) W x) t₀ := by
  apply hasDerivAt_parametric_pullback hF hF0 hA0
  · exact DifferentiableAt.clm_inverse_of_completeSpace
      (hasDerivAt_spatialFDeriv hF).differentiableAt
      (isInvertible_spatialFDeriv_of_eq_id hA0)
  · exact hW

end VectorField
