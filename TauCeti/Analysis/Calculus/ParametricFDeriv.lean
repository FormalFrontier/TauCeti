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
differentiating its spatial Jacobian in the parameter direction at `t₀` is the spatial derivative
of its parameter velocity at `t₀`. This is the mixed-partial identity needed to identify the
derivative of a flow pullback with a Lie bracket. Over `ℝ` or `ℂ`, the required smoothness is `C²`;
over a general nontrivially normed field, it is analyticity.

This supplies a prerequisite for Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main definitions

* `spatialFDeriv`: the spatial Jacobian of a parametric map.
* `timeFDeriv`: the parameter velocity at a specified parameter value.

## Main results

* `hasDerivAt_timeSlice`: the parameter velocity differentiates the corresponding time slice.
* `hasDerivAt_spatialFDeriv`: the spatial Jacobian differentiates to the spatial derivative of the
  parameter velocity.
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

/-- The parameter velocity of a parametric map at `(t, x)`. -/
def timeFDeriv (F : 𝕜 × E → F') (t : 𝕜) (x : E) : F' :=
  fderiv 𝕜 F (t, x) (1, 0)

@[simp]
theorem timeFDeriv_apply (F : 𝕜 × E → F') (t : 𝕜) (x : E) :
    timeFDeriv F t x = fderiv 𝕜 F (t, x) (1, 0) :=
  (rfl)

/-- The parameter velocity is the derivative of the corresponding time slice. -/
theorem hasDerivAt_timeSlice {F : 𝕜 × E → F'} {t : 𝕜} {x : E}
    (hF : DifferentiableAt 𝕜 F (t, x)) :
    HasDerivAt (fun s => F (s, x)) (timeFDeriv F t x) t := by
  have hp : HasDerivAt (fun s : 𝕜 => (s, x)) (1, 0) t := by
    simpa using (hasFDerivAt_prodMk_left t x).hasDerivAt
  simpa only [timeFDeriv_apply, Function.comp_def] using
    hF.hasFDerivAt.comp_hasDerivAt t hp

/-- The derivative of a spatial slice is its spatial Jacobian. -/
@[simp]
theorem fderiv_timeSlice {F : 𝕜 × E → F'} {t : 𝕜} {x : E}
    (hF : DifferentiableAt 𝕜 F (t, x)) :
    fderiv 𝕜 (fun y => F (t, y)) x = spatialFDeriv F x t := by
  change fderiv 𝕜 (F ∘ fun y => (t, y)) x = _
  exact (hF.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv

/-- For a sufficiently smooth parametric map, the parameter derivative of its spatial Jacobian,
applied to `w`, is the spatial derivative of its parameter-velocity field applied to `w`. -/
theorem deriv_spatialFDeriv_apply {F : 𝕜 × E → F'} {t : 𝕜} {x w : E}
    (hF : ContDiffAt 𝕜 (minSmoothness 𝕜 2) F (t, x)) :
    _root_.deriv (fun s => spatialFDeriv F x s w) t =
      fderiv 𝕜 (timeFDeriv F t) x w := by
  let DF : 𝕜 × E → (𝕜 × E →L[𝕜] F') := fderiv 𝕜 F
  have hDFdiff : DifferentiableAt 𝕜 DF (t, x) :=
    (hF.fderiv_right (m := 1) le_minSmoothness).differentiableAt one_ne_zero
  have hDF := hDFdiff.hasFDerivAt
  have hp : HasDerivAt (fun s : 𝕜 => (s, x)) (1, 0) t := by
    simpa using (hasFDerivAt_prodMk_left t x).hasDerivAt
  have hspace : HasDerivAt (fun _ : 𝕜 => ((0 : 𝕜), w)) 0 t :=
    hasDerivAt_const (x := t) _
  have hDFp := hDF.comp_hasDerivAt t hp
  have hAraw := hDFp.clm_apply hspace
  have hA : HasDerivAt (fun s => DF (s, x) (0, w))
      (fderiv 𝕜 DF (t, x) (1, 0) (0, w)) t := by
    simpa only [Function.comp_apply, map_zero, add_zero] using hAraw
  have hq : HasFDerivAt (fun z : E => (t, z))
      (ContinuousLinearMap.inr 𝕜 𝕜 E) x :=
    hasFDerivAt_prodMk_right t x
  have hone : HasFDerivAt (fun _ : E => ((1 : 𝕜), (0 : E)))
      (0 : E →L[𝕜] 𝕜 × E) x :=
    hasFDerivAt_const (x := x) ((1 : 𝕜), (0 : E))
  have hVraw := (hDF.comp x hq).clm_apply hone
  have hV : HasFDerivAt (timeFDeriv F t) (fderiv 𝕜 DF (t, x) ∘L
      ContinuousLinearMap.inr 𝕜 𝕜 E |>.flip (1, 0)) x := by
    -- Expose the named wrapper as the slice used by `hVraw`.
    rw [show timeFDeriv F t = fun z => fderiv 𝕜 F (t, z) (1, 0) from
      funext (timeFDeriv_apply F t)]
    simpa only [DF, Function.comp_apply, map_zero, add_zero,
      ContinuousLinearMap.comp_zero, zero_add] using hVraw
  have hsymm := hF.isSymmSndFDerivAt le_rfl
  -- Identify the named spatial Jacobian with the applied full derivative.
  rw [show _root_.deriv (fun s => spatialFDeriv F x s w) t = _ from
    by simpa only [DF, spatialFDeriv_apply] using hA.deriv, hV.fderiv]
  simpa [DF, Function.comp_def] using hsymm (1, 0) (0, w)

/-- At `t`, the spatial Jacobian has derivative the spatial derivative of the parameter velocity. -/
theorem hasDerivAt_spatialFDeriv {F : 𝕜 × E → F'} {t : 𝕜} {x : E}
    (hF : ContDiffAt 𝕜 (minSmoothness 𝕜 2) F (t, x)) :
    HasDerivAt (spatialFDeriv F x) (fderiv 𝕜 (timeFDeriv F t) x) t := by
  have hdiff : DifferentiableAt 𝕜 (spatialFDeriv F x) t := by
    have hDFdiff : DifferentiableAt 𝕜 (fderiv 𝕜 F) (t, x) :=
      (hF.fderiv_right (m := 1) le_minSmoothness).differentiableAt one_ne_zero
    have hraw : DifferentiableAt 𝕜
        (fun s => (fderiv 𝕜 F (s, x)).comp (ContinuousLinearMap.inr 𝕜 𝕜 E)) t := by
      fun_prop
    convert hraw using 1
    funext t
    ext w
    exact spatialFDeriv_apply F x t w
  have heq : _root_.deriv (spatialFDeriv F x) t = fderiv 𝕜 (timeFDeriv F t) x := by
    apply ContinuousLinearMap.ext
    intro w
    have hw : HasDerivAt (fun _ : 𝕜 => w) 0 t := hasDerivAt_const t w
    calc
      _ = _root_.deriv (fun s => spatialFDeriv F x s w) t := by
        simpa only [map_zero, add_zero] using (hdiff.hasDerivAt.clm_apply hw).deriv.symm
      _ = _ := deriv_spatialFDeriv_apply hF
  rw [← heq]
  exact hdiff.hasDerivAt
