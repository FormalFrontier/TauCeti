/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Mixed derivatives of a parametric map

For a map `F : 𝕜 × E → F'` with the minimum smoothness needed for symmetric second derivatives,
differentiating its spatial Jacobian in the parameter direction is the spatial derivative of its
parameter velocity. This is the mixed-partial identity needed to identify the derivative of a flow
pullback with a Lie bracket. Over `ℝ` or `ℂ`, the required smoothness is `C²`; over a general
nontrivially normed field, it is analyticity.

This supplies a prerequisite for Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main result

* `hasDerivAt_timeFDeriv`: the parameter velocity differentiates the corresponding time slice.
* `deriv_spatialFDeriv_apply`: the parameter derivative of the spatial Jacobian equals the
  derivative of the parameter-velocity field.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The infinitesimal adjoint".
-/

public section

noncomputable section

open ContinuousLinearMap

variable {𝕜 E F' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- The spatial Jacobian of a parametric map at `x`, as a function of the parameter. -/
def spatialFDeriv (F : 𝕜 × E → F') (x : E) (t : 𝕜) : E →L[𝕜] F' :=
  (fderiv 𝕜 F (t, x)).comp (ContinuousLinearMap.inr 𝕜 𝕜 E)

@[simp]
theorem spatialFDeriv_apply (F : 𝕜 × E → F') (x : E) (t : 𝕜) (w : E) :
    spatialFDeriv F x t w = fderiv 𝕜 F (t, x) (0, w) :=
  (rfl)

/-- The parameter velocity at zero of a parametric map. -/
def timeFDeriv (F : 𝕜 × E → F') (x : E) : F' :=
  fderiv 𝕜 F (0, x) (1, 0)

@[simp]
theorem timeFDeriv_apply (F : 𝕜 × E → F') (x : E) :
    timeFDeriv F x = fderiv 𝕜 F (0, x) (1, 0) :=
  (rfl)

/-- The parameter velocity is the derivative at zero of the corresponding time slice. -/
theorem hasDerivAt_timeFDeriv {F : 𝕜 × E → F'} {x : E}
    (hF : DifferentiableAt 𝕜 F (0, x)) :
    HasDerivAt (fun t => F (t, x)) (timeFDeriv F x) 0 := by
  have hp : HasDerivAt (fun t : 𝕜 => (t, x)) (1, 0) 0 :=
    (hasDerivAt_id (𝕜 := 𝕜) (0 : 𝕜)).prodMk (hasDerivAt_const (x := 0) x)
  simpa only [timeFDeriv_apply, Function.comp_def] using
    hF.hasFDerivAt.comp_hasDerivAt 0 hp

/-- For a sufficiently smooth parametric map, the parameter derivative of its spatial Jacobian,
applied to `w`, is the spatial derivative of its parameter-velocity field applied to `w`. -/
private theorem deriv_spatialFDeriv_apply_aux {F : 𝕜 × E → F'} {x w : E}
    (hF : ContDiffAt 𝕜 (minSmoothness 𝕜 2) F (0, x)) :
    _root_.deriv (fun t => spatialFDeriv F x t w) 0 =
      fderiv 𝕜 (timeFDeriv F) x w := by
  let DF : 𝕜 × E → (𝕜 × E →L[𝕜] F') := fderiv 𝕜 F
  have hDFdiff : DifferentiableAt 𝕜 DF (0, x) :=
    (hF.fderiv_right (m := 1) le_minSmoothness).differentiableAt one_ne_zero
  have hDF := hDFdiff.hasFDerivAt
  have hp : HasDerivAt (fun t : 𝕜 => (t, x)) (1, 0) 0 :=
    (hasDerivAt_id (𝕜 := 𝕜) (0 : 𝕜)).prodMk (hasDerivAt_const (x := 0) x)
  have hspace : HasDerivAt (fun _ : 𝕜 => ((0 : 𝕜), w)) 0 0 :=
    hasDerivAt_const (x := 0) _
  have hDFp := hDF.comp_hasDerivAt 0 hp
  have hAraw := hDFp.clm_apply hspace
  have hA : HasDerivAt (fun t => DF (t, x) (0, w))
      (fderiv 𝕜 DF (0, x) (1, 0) (0, w)) 0 := by
    simpa only [Function.comp_apply, map_zero, add_zero] using hAraw
  have hq : HasFDerivAt (fun z : E => ((0 : 𝕜), z))
      (ContinuousLinearMap.inr 𝕜 𝕜 E) x :=
    (hasFDerivAt_const (x := x) (c := (0 : 𝕜))).prodMk (hasFDerivAt_id (x := x))
  have hone : HasFDerivAt (fun _ : E => ((1 : 𝕜), (0 : E)))
      (0 : E →L[𝕜] 𝕜 × E) x :=
    hasFDerivAt_const (x := x) ((1 : 𝕜), (0 : E))
  have hVraw := (hDF.comp x hq).clm_apply hone
  have hV : HasFDerivAt (timeFDeriv F) (fderiv 𝕜 DF (0, x) ∘L
      ContinuousLinearMap.inr 𝕜 𝕜 E |>.flip (1, 0)) x := by
    -- Expose the named wrapper as the slice used by `hVraw`.
    rw [show timeFDeriv F = fun z => fderiv 𝕜 F (0, z) (1, 0) from
      funext (timeFDeriv_apply F)]
    simpa only [DF, Function.comp_apply, map_zero, add_zero,
      ContinuousLinearMap.comp_zero, zero_add] using hVraw
  have hsymm := hF.isSymmSndFDerivAt le_rfl
  -- Identify the named spatial Jacobian with the applied full derivative.
  rw [show _root_.deriv (fun t => spatialFDeriv F x t w) 0 = _ from
    by simpa only [DF, spatialFDeriv_apply] using hA.deriv, hV.fderiv]
  simpa [DF, Function.comp_def] using hsymm (1, 0) (0, w)

/-- The derivative of the spatial Jacobian is the derivative of the parameter-velocity field. -/
theorem hasDerivAt_spatialFDeriv {F : 𝕜 × E → F'} {x : E}
    (hF : ContDiffAt 𝕜 (minSmoothness 𝕜 2) F (0, x)) :
    HasDerivAt (spatialFDeriv F x) (fderiv 𝕜 (timeFDeriv F) x) 0 := by
  have hdiff : DifferentiableAt 𝕜 (spatialFDeriv F x) 0 := by
    have hDFdiff : DifferentiableAt 𝕜 (fderiv 𝕜 F) (0, x) :=
      (hF.fderiv_right (m := 1) le_minSmoothness).differentiableAt one_ne_zero
    have hraw : DifferentiableAt 𝕜
        (fun t => (fderiv 𝕜 F (t, x)).comp (ContinuousLinearMap.inr 𝕜 𝕜 E)) 0 := by
      fun_prop
    convert hraw using 1
    funext t
    ext w
    exact spatialFDeriv_apply F x t w
  have heq : _root_.deriv (spatialFDeriv F x) 0 = fderiv 𝕜 (timeFDeriv F) x := by
    apply ContinuousLinearMap.ext
    intro w
    have hw : HasDerivAt (fun _ : 𝕜 => w) 0 0 := hasDerivAt_const 0 w
    calc
      _ = _root_.deriv (fun t => spatialFDeriv F x t w) 0 := by
        simpa only [map_zero, add_zero] using (hdiff.hasDerivAt.clm_apply hw).deriv.symm
      _ = _ := deriv_spatialFDeriv_apply_aux hF
  rw [← heq]
  exact hdiff.hasDerivAt

/-- Applied form of `hasDerivAt_spatialFDeriv`. -/
theorem deriv_spatialFDeriv_apply {F : 𝕜 × E → F'} {x w : E}
    (hF : ContDiffAt 𝕜 (minSmoothness 𝕜 2) F (0, x)) :
    _root_.deriv (fun t => spatialFDeriv F x t w) 0 =
      fderiv 𝕜 (timeFDeriv F) x w := by
  have hw : HasDerivAt (fun _ : 𝕜 => w) 0 0 := hasDerivAt_const 0 w
  simpa only [map_zero, add_zero] using (hasDerivAt_spatialFDeriv hF).clm_apply hw |>.deriv
