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

* `hasDerivAt_parametric_pullback`: differentiating the parametric pullback gives the Lie bracket.

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
theorem hasDerivAt_parametric_pullback {F : ℝ × E → E} {W : E → E} {x : E}
    (hF : ContDiffAt ℝ 2 F (0, x)) (hF0 : F (0, x) = x)
    (hA0 : spatialFDeriv F x 0 = ContinuousLinearMap.id ℝ E)
    (hInvDiff : DifferentiableAt ℝ (fun t => (spatialFDeriv F x t).inverse) 0)
    (hAInv : ∀ᶠ t in 𝓝 0, (spatialFDeriv F x t).IsInvertible)
    (hW : DifferentiableAt ℝ W x) :
    HasDerivAt
      (fun t => VectorField.pullback ℝ (fun y => F (t, y)) W x)
      (VectorField.lieBracket ℝ (timeFDeriv F) W x) 0 := by
  have hp : HasDerivAt (fun t : ℝ => (t, x)) (1, 0) 0 :=
    (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).prodMk (hasDerivAt_const (x := 0) x)
  have hA := hasDerivAt_spatialFDeriv hF
  have hz : HasDerivAt (fun t => F (t, x)) (timeFDeriv F x) 0 := by
    have hFdiff : DifferentiableAt ℝ F (0, x) := hF.differentiableAt (by norm_num)
    simpa only [timeFDeriv_apply, Function.comp_def] using
      hFdiff.hasFDerivAt.comp_hasDerivAt 0 hp
  have hW0 : HasFDerivAt W (fderiv ℝ W x) (F (0, x)) := by
    simpa only [hF0] using hW.hasFDerivAt
  have hpull := hA.clm_inverse_apply (by
    rw [hA0]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩)
    hInvDiff hAInv (hW0.comp_hasDerivAt 0 hz)
  have hslice : (fun t => VectorField.pullback ℝ (fun y => F (t, y)) W x) =ᶠ[𝓝 0]
      fun t => (spatialFDeriv F x t).inverse (W (F (t, x))) := by
    have hpath : ContinuousAt (fun t : ℝ => (t, x)) 0 := hp.continuousAt
    filter_upwards [hpath.eventually (hF.eventually (by norm_num))] with t ht
    unfold VectorField.pullback
    congr 2
    have hs := (ht.differentiableAt (by norm_num)).hasFDerivAt.comp x
      ((hasFDerivAt_const (x := x) (c := t)).prodMk (hasFDerivAt_id (x := x)))
    -- The slice is definitionally `F ∘ Prod.mk t`; keep that conversion local to this equality.
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
    simpa only [Function.comp_apply, hF0, hA0, ContinuousLinearMap.inverse_id,
      ContinuousLinearMap.id_apply, VectorField.lieBracket] using hpull
  exact hpull'.congr_of_eventuallyEq hslice
