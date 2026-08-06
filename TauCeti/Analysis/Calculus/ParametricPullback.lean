/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.VectorField
public import TauCeti.Analysis.Calculus.ParametricFDeriv

/-!
# Differentiating a parametric pullback

The derivative at zero of the pullback of a vector field along a parametric family that starts at
the identity is the Lie bracket with the family's initial velocity. This is the vector-space
calculus statement underlying the infinitesimal adjoint action of a Lie group.

This supplies a prerequisite for Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main result

* `hasDerivAt_parametricPullback`: differentiating the parametric pullback gives the Lie bracket.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The infinitesimal adjoint".
-/

public section

noncomputable section

open ContinuousLinearMap
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Let `F t` be a twice continuously differentiable family of maps starting at the identity near
`x`. If its spatial derivative is locally invertible and its inverse varies differentiably, then
the derivative of the pullback of `W` along `F` is the Lie bracket of the initial velocity of `F`
with `W`.

The explicit hypotheses on the inverse family separate the mixed-derivative calculation from the
inverse-function argument used by individual applications. -/
theorem hasDerivAt_parametricPullback {F : ℝ × E → E} {W : E → E} {x : E}
    (hF : ContDiffAt ℝ 2 F (0, x)) (hF0 : F (0, x) = x)
    (hA0 : spatialFDeriv F x 0 = ContinuousLinearMap.id ℝ E)
    (hAdiff : DifferentiableAt ℝ (spatialFDeriv F x) 0)
    (hInvDiff : DifferentiableAt ℝ (fun t => (spatialFDeriv F x t).inverse) 0)
    (hAInv : ∀ᶠ t in 𝓝 0, (spatialFDeriv F x t).IsInvertible)
    (hW : DifferentiableAt ℝ W x) :
    HasDerivAt
      (fun t => (spatialFDeriv F x t).inverse (W (F (t, x))))
      (VectorField.lieBracket ℝ (timeFDeriv F) W x) 0 := by
  let A' : E →L[ℝ] E := _root_.deriv (spatialFDeriv F x) 0
  have hA : HasDerivAt (spatialFDeriv F x) A' 0 := hAdiff.hasDerivAt
  have hp : HasDerivAt (fun t : ℝ => (t, x)) (1, 0) 0 :=
    (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).prodMk (hasDerivAt_const (x := 0) x)
  have hz : HasDerivAt (fun t => F (t, x)) (timeFDeriv F x) 0 := by
    have hFdiff : DifferentiableAt ℝ F (0, x) := hF.differentiableAt (by norm_num)
    simpa only [timeFDeriv_apply, Function.comp_def] using
      hFdiff.hasFDerivAt.comp_hasDerivAt 0 hp
  have hW0 : HasFDerivAt W (fderiv ℝ W x) (F (0, x)) := by
    simpa only [hF0] using hW.hasFDerivAt
  have hpull := hA.clm_inverse_apply_comp hA0 hInvDiff hAInv hz hW0
  have hA_apply (w : E) : A' w = fderiv ℝ (timeFDeriv F) x w := by
    have hw : HasDerivAt (fun _ : ℝ => w) 0 0 := hasDerivAt_const 0 w
    have hAw : HasDerivAt (fun t => spatialFDeriv F x t w) (A' w) 0 := by
      simpa only [map_zero, add_zero] using hA.clm_apply hw
    rw [← deriv_spatialFDeriv_apply hF, hAw.deriv]
  rw [hF0] at hpull
  simpa only [VectorField.lieBracket, hA_apply] using hpull
