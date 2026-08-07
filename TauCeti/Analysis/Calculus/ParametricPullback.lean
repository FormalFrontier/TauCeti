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

The derivative at zero of the pullback of a vector field along a parametric family that agrees
with the identity to first order at a point is the Lie bracket with the family's initial velocity.
This is the vector-space calculus statement underlying the infinitesimal adjoint action of a Lie
group.

This supplies a prerequisite for Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main result

* `hasDerivAt_pullback_parametric`: differentiating the parametric pullback gives the Lie bracket.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The infinitesimal adjoint".
-/

public section

noncomputable section

open ContinuousLinearMap
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Let `F t` be a twice continuously differentiable family of maps that agrees with the identity
to first order at `x` when `t = 0`. Then the derivative of the pullback of `W` along `F` is the Lie
bracket of the initial velocity of `F` with `W`. -/
theorem hasDerivAt_pullback_parametric {F : ℝ × E → E} {W : E → E} {x : E}
    (hF : ContDiffAt ℝ 2 F (0, x)) (hF0 : F (0, x) = x)
    (hA0 : spatialFDeriv F x 0 = ContinuousLinearMap.id ℝ E)
    (hInvDiff : DifferentiableAt ℝ (fun t => (spatialFDeriv F x t).inverse) 0)
    (hAInv : ∀ᶠ t in 𝓝 0, (spatialFDeriv F x t).IsInvertible)
    (hW : DifferentiableAt ℝ W x) :
    HasDerivAt
      (fun t => VectorField.pullback ℝ (fun y => F (t, y)) W x)
      (VectorField.lieBracket ℝ (timeFDeriv F) W x) 0 := by
  let A' : E →L[ℝ] E := _root_.deriv (spatialFDeriv F x) 0
  have hp : HasDerivAt (fun t : ℝ => (t, x)) (1, 0) 0 :=
    (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).prodMk (hasDerivAt_const (x := 0) x)
  have hDFdiff : DifferentiableAt ℝ (fderiv ℝ F) (0, x) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hAdiff : DifferentiableAt ℝ (spatialFDeriv F x) 0 := by
    have hraw : DifferentiableAt ℝ
        (fun t => (fderiv ℝ F (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) 0 := by
      fun_prop
    convert hraw using 1
    funext t
    apply ContinuousLinearMap.ext
    intro w
    exact spatialFDeriv_apply F x t w
  have hA : HasDerivAt (spatialFDeriv F x) A' 0 := hAdiff.hasDerivAt
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
  have hslice : (fun t => VectorField.pullback ℝ (fun y => F (t, y)) W x) =ᶠ[𝓝 0]
      fun t => (spatialFDeriv F x t).inverse (W (F (t, x))) := by
    have hpath : ContinuousAt (fun t : ℝ => (t, x)) 0 := hp.continuousAt
    filter_upwards [hpath.eventually (hF.eventually (by norm_num))] with t ht
    unfold VectorField.pullback
    congr 2
    have hs := (ht.differentiableAt (by norm_num)).hasFDerivAt.comp x
      ((hasFDerivAt_const (x := x) (c := t)).prodMk (hasFDerivAt_id (x := x)))
    have hs' : fderiv ℝ (fun y => F (t, y)) x =
        (fderiv ℝ F (t, x)).comp
          (ContinuousLinearMap.prod (0 : E →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ E)) := by
      change fderiv ℝ (F ∘ Prod.mk t) x = _
      exact hs.fderiv
    rw [hs']
    apply ContinuousLinearMap.ext
    intro w
    exact (spatialFDeriv_apply F x t w).symm
  have hpull' : HasDerivAt
      (fun t => (spatialFDeriv F x t).inverse (W (F (t, x))))
      (VectorField.lieBracket ℝ (timeFDeriv F) W x) 0 := by
    simpa only [VectorField.lieBracket, hA_apply] using hpull
  exact hpull'.congr_of_eventuallyEq hslice
