/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Mixed derivatives of a parametric map

For a map `F : 𝕜 × E → F'` with the minimum smoothness needed for symmetric second derivatives,
differentiating its spatial Jacobian in the parameter direction at `t₀` is the spatial derivative
of its parameter velocity at `t₀`. This is the mixed-partial identity needed to identify the
derivative of a parametric-family pullback with a Lie bracket. Over `ℝ` or `ℂ`, the required
smoothness is `C²`;
over a general nontrivially normed field, it is analyticity.

This supplies a prerequisite for Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main definitions

* `spatialFDeriv`: the spatial Jacobian of a parametric map.
* `timeFDeriv`: the parameter velocity at a specified parameter value.

## Main results

* `hasDerivAt_parameterCurve`: the parameter velocity differentiates the corresponding parameter
  curve.
* `fderiv_timeSlice`: the derivative of a fixed-parameter slice is its spatial Jacobian.
* `hasDerivAt_spatialFDeriv`: the spatial Jacobian differentiates to the spatial derivative of the
  parameter velocity.
* `deriv_spatialFDeriv_apply`: the parameter derivative of the spatial Jacobian equals the
  derivative of the parameter-velocity field.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The infinitesimal adjoint".
* Sébastien Gouëzel, `Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`, theorem
  `ContDiffAt.isSymmSndFDerivAt`.
-/

public section

noncomputable section

open ContinuousLinearMap

variable {𝕜 E F' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- The spatial Jacobian of a parametric map at `x`, as a function of the parameter. If `F` is not
differentiable at `(t, x)`, its value at `t` is the junk value `0`. -/
def spatialFDeriv (F : 𝕜 × E → F') (x : E) (t : 𝕜) : E →L[𝕜] F' :=
  (fderiv 𝕜 F (t, x)).comp (ContinuousLinearMap.inr 𝕜 𝕜 E)

/-- The spatial derivative as the restriction of the full derivative to the spatial factor. -/
theorem spatialFDeriv_def (F : 𝕜 × E → F') (x : E) (t : 𝕜) :
    spatialFDeriv F x t =
      (fderiv 𝕜 F (t, x)).comp (ContinuousLinearMap.inr 𝕜 𝕜 E) :=
  (rfl)

@[simp]
theorem spatialFDeriv_apply (F : 𝕜 × E → F') (x : E) (t : 𝕜) (w : E) :
    spatialFDeriv F x t w = fderiv 𝕜 F (t, x) (0, w) :=
  (rfl)

/-- The parameter velocity of a parametric map at `(t, x)`. If `F` is not differentiable there,
this is the junk value `0`. -/
def timeFDeriv (F : 𝕜 × E → F') (t : 𝕜) (x : E) : F' :=
  fderiv 𝕜 F (t, x) (1, 0)

@[simp]
theorem timeFDeriv_apply (F : 𝕜 × E → F') (t : 𝕜) (x : E) :
    timeFDeriv F t x = fderiv 𝕜 F (t, x) (1, 0) :=
  (rfl)

/-- The parameter velocity is the derivative of the parameter curve `fun s ↦ F (s, x)`. -/
theorem hasDerivAt_parameterCurve {F : 𝕜 × E → F'} {t : 𝕜} {x : E}
    (hF : DifferentiableAt 𝕜 F (t, x)) :
    HasDerivAt (fun s => F (s, x)) (timeFDeriv F t x) t := by
  simpa only [timeFDeriv_apply, Function.comp_def, ContinuousLinearMap.inl_apply] using
    hF.hasFDerivAt.comp_hasDerivAt t (hasFDerivAt_prodMk_left t x).hasDerivAt

/-- The derivative of the fixed-parameter slice `fun y ↦ F (t, y)` is its spatial Jacobian. -/
theorem fderiv_timeSlice {F : 𝕜 × E → F'} {t : 𝕜} {x : E}
    (hF : DifferentiableAt 𝕜 F (t, x)) :
    fderiv 𝕜 (fun y => F (t, y)) x = spatialFDeriv F x t := by
  rw [spatialFDeriv_def]
  exact (hF.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv

/-- At `t`, the spatial Jacobian has derivative the spatial derivative of the parameter velocity. -/
theorem hasDerivAt_spatialFDeriv {F : 𝕜 × E → F'} {t : 𝕜} {x : E}
    (hF : ContDiffAt 𝕜 (minSmoothness 𝕜 2) F (t, x)) :
    HasDerivAt (spatialFDeriv F x) (fderiv 𝕜 (timeFDeriv F t) x) t := by
  -- Compute the parameter derivative of `s ↦ DF (s, x) (0, w)` and the spatial
  -- derivative of `timeFDeriv F t = fun z ↦ DF (t, z) (1, 0)`. Symmetry of the
  -- second derivative identifies these two mixed partials, pointwise in `w`.
  let DF : 𝕜 × E → (𝕜 × E →L[𝕜] F') := fderiv 𝕜 F
  have hDFdiff : DifferentiableAt 𝕜 DF (t, x) :=
    (hF.fderiv_right (m := 1) le_minSmoothness).differentiableAt one_ne_zero
  have hdiff : DifferentiableAt 𝕜 (spatialFDeriv F x) t := by
    rw [show spatialFDeriv F x = fun s =>
      (DF (s, x)).comp (ContinuousLinearMap.inr 𝕜 𝕜 E) from
        funext (spatialFDeriv_def F x)]
    fun_prop
  have heq : _root_.deriv (spatialFDeriv F x) t = fderiv 𝕜 (timeFDeriv F t) x := by
    apply ContinuousLinearMap.ext
    intro w
    have hDF := hDFdiff.hasFDerivAt
    have hspace : HasDerivAt (fun _ : 𝕜 => ((0 : 𝕜), w)) 0 t :=
      hasDerivAt_const (x := t) _
    have hParamRaw :=
      (hDF.comp_hasDerivAt t (hasFDerivAt_prodMk_left t x).hasDerivAt).clm_apply hspace
    have hParam : HasDerivAt (fun s => DF (s, x) (0, w))
        (fderiv 𝕜 DF (t, x) (1, 0) (0, w)) t := by
      simpa only [Function.comp_apply, ContinuousLinearMap.inl_apply, map_zero, add_zero] using
        hParamRaw
    have hone : HasFDerivAt (fun _ : E => ((1 : 𝕜), (0 : E)))
        (0 : E →L[𝕜] 𝕜 × E) x :=
      hasFDerivAt_const (x := x) ((1 : 𝕜), (0 : E))
    have hSpatialRaw :=
      (hDF.comp x (hasFDerivAt_prodMk_right t x)).clm_apply hone
    have hSpatial : HasFDerivAt (timeFDeriv F t) (fderiv 𝕜 DF (t, x) ∘L
        ContinuousLinearMap.inr 𝕜 𝕜 E |>.flip (1, 0)) x := by
      rw [show timeFDeriv F t = fun z => fderiv 𝕜 F (t, z) (1, 0) from
        funext (timeFDeriv_apply F t)]
      simpa only [DF, Function.comp_apply, map_zero, add_zero,
        ContinuousLinearMap.comp_zero, zero_add] using hSpatialRaw
    have hParamDeriv : _root_.deriv (fun s => spatialFDeriv F x s w) t =
        fderiv 𝕜 DF (t, x) (1, 0) (0, w) := by
      simpa only [DF, spatialFDeriv_apply] using hParam.deriv
    have hsymm := hF.isSymmSndFDerivAt le_rfl
    have hw : HasDerivAt (fun _ : 𝕜 => w) 0 t := hasDerivAt_const t w
    calc
      _ = _root_.deriv (fun s => spatialFDeriv F x s w) t := by
        simpa only [map_zero, add_zero] using (hdiff.hasDerivAt.clm_apply hw).deriv.symm
      _ = fderiv 𝕜 DF (t, x) (1, 0) (0, w) := hParamDeriv
      _ = _ := by
        rw [hSpatial.fderiv]
        simpa only [DF, ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.inr_apply] using hsymm (1, 0) (0, w)
  rw [← heq]
  exact hdiff.hasDerivAt

/-- For a sufficiently smooth parametric map, the parameter derivative of its spatial Jacobian,
applied to `w`, is the spatial derivative of its parameter-velocity field applied to `w`. -/
theorem deriv_spatialFDeriv_apply {F : 𝕜 × E → F'} {t : 𝕜} {x w : E}
    (hF : ContDiffAt 𝕜 (minSmoothness 𝕜 2) F (t, x)) :
    _root_.deriv (fun s => spatialFDeriv F x s w) t =
      fderiv 𝕜 (timeFDeriv F t) x w := by
  simpa only [map_zero, add_zero] using
    ((hasDerivAt_spatialFDeriv hF).clm_apply (hasDerivAt_const t w)).deriv
