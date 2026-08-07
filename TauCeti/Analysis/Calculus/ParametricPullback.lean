/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.VectorField
public import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
public import TauCeti.Analysis.Calculus.ParametricFDeriv

/-!
# Differentiating a parametric pullback

For a differentiable vector field and a sufficiently smooth parametric family whose inverse spatial
Jacobian is differentiable, the derivative at zero of its pullback is the Lie bracket with the
family's initial velocity when the family agrees with the identity to first order at the point.
This is the vector-space calculus statement underlying the infinitesimal adjoint action of a Lie
group.

This supplies a prerequisite for Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main result

* `hasDerivAt_parametric_pullback`: differentiating the parametric pullback gives the Lie bracket.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The infinitesimal adjoint".
-/

public section

noncomputable section

open ContinuousLinearMap
open scoped Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Let `F` have the minimum smoothness needed for symmetric second derivatives at `(0, x)` and
agree with the identity to first order at `x` when `t = 0`. If the inverse spatial-Jacobian family
is differentiable at zero and `W` is differentiable at `x`, then the derivative of the pullback of
`W` along `F` is the Lie bracket of the initial velocity of `F` with `W`. -/
theorem hasDerivAt_parametric_pullback {F : 𝕜 × E → E} {W : E → E} {x : E}
    (hF : ContDiffAt 𝕜 (minSmoothness 𝕜 2) F (0, x)) (hF0 : F (0, x) = x)
    (hA0 : spatialFDeriv F x 0 = ContinuousLinearMap.id 𝕜 E)
    (hInvDiff : DifferentiableAt 𝕜 (fun t => (spatialFDeriv F x t).inverse) 0)
    (hW : DifferentiableAt 𝕜 W x) :
    HasDerivAt
      (fun t => VectorField.pullback 𝕜 (fun y => F (t, y)) W x)
      (VectorField.lieBracket 𝕜 (timeFDeriv F) W x) 0 := by
  have hA := hasDerivAt_spatialFDeriv hF
  have hz : HasDerivAt (fun t => F (t, x)) (timeFDeriv F x) 0 := by
    have hFdiff : DifferentiableAt 𝕜 F (0, x) :=
      (hF.of_le le_minSmoothness).differentiableAt two_ne_zero
    exact hasDerivAt_timeFDeriv hFdiff
  have hW0 : HasFDerivAt W (fderiv 𝕜 W x) (F (0, x)) := by
    simpa only [hF0] using hW.hasFDerivAt
  have hpull := hA.clm_inverse_apply (by
    rw [hA0]
    exact ⟨ContinuousLinearEquiv.refl 𝕜 E, rfl⟩)
    hInvDiff (hW0.comp_hasDerivAt 0 hz)
  have hslice : (fun t => VectorField.pullback 𝕜 (fun y => F (t, y)) W x) =ᶠ[𝓝 0]
      fun t => (spatialFDeriv F x t).inverse (W (F (t, x))) := by
    have hpath : ContinuousAt (fun t : 𝕜 => (t, x)) 0 := by fun_prop
    filter_upwards [hpath.eventually (hF.eventually (by norm_num))] with t ht
    unfold VectorField.pullback
    congr 2
    have hs := ((ht.of_le le_minSmoothness).differentiableAt two_ne_zero).hasFDerivAt.comp x
      ((hasFDerivAt_const (x := x) (c := t)).prodMk (hasFDerivAt_id (x := x)))
    -- The slice is definitionally `F ∘ Prod.mk t`; keep that conversion local to this equality.
    have hs' : fderiv 𝕜 (fun y => F (t, y)) x =
        (fderiv 𝕜 F (t, x)).comp
          (ContinuousLinearMap.prod (0 : E →L[𝕜] 𝕜) (ContinuousLinearMap.id 𝕜 E)) := by
      change fderiv 𝕜 (F ∘ Prod.mk t) x = _
      exact hs.fderiv
    rw [hs']
    apply ContinuousLinearMap.ext
    intro w
    exact (spatialFDeriv_apply F x t w).symm
  have hpull' : HasDerivAt
      (fun t => (spatialFDeriv F x t).inverse (W (F (t, x))))
      (VectorField.lieBracket 𝕜 (timeFDeriv F) W x) 0 := by
    simpa only [Function.comp_apply, hF0, hA0, ContinuousLinearMap.inverse_id,
      ContinuousLinearMap.id_apply, VectorField.lieBracket] using hpull
  exact hpull'.congr_of_eventuallyEq hslice
