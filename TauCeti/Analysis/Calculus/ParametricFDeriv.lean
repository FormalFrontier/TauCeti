/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import TauCeti.Analysis.Calculus.SecondDerivative

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
* `hasFDerivAt_timeSlice`: the spatial Jacobian differentiates the corresponding fixed-parameter
  slice.
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

/-- Applying a differentiable family of continuous linear maps to a constant vector. -/
private theorem HasDerivAt.clm_apply_const {t : 𝕜} {c : 𝕜 → E →L[𝕜] F'}
    {c' : E →L[𝕜] F'} (hc : HasDerivAt c c' t) (u : E) :
    HasDerivAt (fun s => c s u) (c' u) t := by
  simpa only [map_zero, add_zero] using hc.clm_apply (hasDerivAt_const t u)

section

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Applying a differentiable family of continuous linear maps to a constant vector. -/
private theorem HasFDerivAt.clm_apply_const {c : E → F' →L[𝕜] G}
    {c' : E →L[𝕜] F' →L[𝕜] G} {x : E} (hc : HasFDerivAt c c' x) (u : F') :
    HasFDerivAt (fun y => c y u) (c'.flip u) x := by
  simpa only [ContinuousLinearMap.comp_zero, zero_add] using
    hc.clm_apply (hasFDerivAt_const (x := x) u)

end

/-- The spatial Jacobian of a parametric map at `x`, as a function of the parameter. If `F` is not
differentiable at `(t, x)`, its value at `t` is the junk value `0`. -/
def spatialFDeriv (F : 𝕜 × E → F') (x : E) (t : 𝕜) : E →L[𝕜] F' :=
  (fderiv 𝕜 F (t, x)).comp (ContinuousLinearMap.inr 𝕜 𝕜 E)

/-- The spatial derivative as the restriction of the full derivative to the spatial factor. -/
theorem spatialFDeriv_def (F : 𝕜 × E → F') (x : E) (t : 𝕜) :
    spatialFDeriv F x t =
      (fderiv 𝕜 F (t, x)).comp (ContinuousLinearMap.inr 𝕜 𝕜 E) :=
  (rfl)

/-- The spatial derivative, as a function of the parameter. -/
theorem spatialFDeriv_eq (F : 𝕜 × E → F') (x : E) :
    spatialFDeriv F x = fun t =>
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

/-- The parameter velocity, as a function of the spatial variable. -/
theorem timeFDeriv_eq (F : 𝕜 × E → F') (t : 𝕜) :
    timeFDeriv F t = fun x => fderiv 𝕜 F (t, x) (1, 0) :=
  (rfl)

/-- The parameter velocity is the derivative of the parameter curve `fun s ↦ F (s, x)`. -/
theorem hasDerivAt_parameterCurve {F : 𝕜 × E → F'} {t : 𝕜} {x : E}
    (hF : DifferentiableAt 𝕜 F (t, x)) :
    HasDerivAt (fun s => F (s, x)) (timeFDeriv F t x) t := by
  simpa only [timeFDeriv_apply, Function.comp_def, ContinuousLinearMap.inl_apply] using
    hF.hasFDerivAt.comp_hasDerivAt t (hasFDerivAt_prodMk_left t x).hasDerivAt

/-- The spatial Jacobian is the derivative of the fixed-parameter slice `fun y ↦ F (t, y)`. -/
theorem hasFDerivAt_timeSlice {F : 𝕜 × E → F'} {t : 𝕜} {x : E}
    (hF : DifferentiableAt 𝕜 F (t, x)) :
    HasFDerivAt (fun y => F (t, y)) (spatialFDeriv F x t) x := by
  rw [spatialFDeriv_def]
  exact hF.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)

/-- The derivative of the fixed-parameter slice `fun y ↦ F (t, y)` is its spatial Jacobian. -/
theorem fderiv_timeSlice {F : 𝕜 × E → F'} {t : 𝕜} {x : E}
    (hF : DifferentiableAt 𝕜 F (t, x)) :
    fderiv 𝕜 (fun y => F (t, y)) x = spatialFDeriv F x t :=
  (hasFDerivAt_timeSlice hF).fderiv

private theorem hasDerivAt_spatialFDeriv_apply_mixed {F : 𝕜 × E → F'}
    {t : 𝕜} {x w : E} (hF : ContDiffAt 𝕜 (minSmoothness 𝕜 2) F (t, x)) :
    HasDerivAt (fun s => spatialFDeriv F x s w)
      (fderiv 𝕜 (fderiv 𝕜 F) (t, x) (1, 0) (0, w)) t := by
  have hDF : HasFDerivAt (fderiv 𝕜 F) (fderiv 𝕜 (fderiv 𝕜 F) (t, x)) (t, x) :=
    TauCeti.ContDiffAt.hasFDerivAt_fderiv hF le_minSmoothness
  have hParam :=
    (hDF.comp_hasDerivAt t (hasFDerivAt_prodMk_left t x).hasDerivAt).clm_apply_const (0, w)
  simpa only [spatialFDeriv_apply, Function.comp_apply, ContinuousLinearMap.inl_apply] using hParam

private theorem hasFDerivAt_timeFDeriv_mixed {F : 𝕜 × E → F'} {t : 𝕜} {x : E}
    (hF : ContDiffAt 𝕜 (minSmoothness 𝕜 2) F (t, x)) :
    HasFDerivAt (timeFDeriv F t)
      ((fderiv 𝕜 (fderiv 𝕜 F) (t, x) ∘L ContinuousLinearMap.inr 𝕜 𝕜 E).flip (1, 0)) x := by
  have hDF : HasFDerivAt (fderiv 𝕜 F) (fderiv 𝕜 (fderiv 𝕜 F) (t, x)) (t, x) :=
    TauCeti.ContDiffAt.hasFDerivAt_fderiv hF le_minSmoothness
  have hSpatial := (hDF.comp x (hasFDerivAt_prodMk_right t x)).clm_apply_const (1, 0)
  rw [timeFDeriv_eq]
  exact hSpatial

/-- At `t`, the spatial Jacobian has derivative the spatial derivative of the parameter velocity. -/
theorem hasDerivAt_spatialFDeriv {F : 𝕜 × E → F'} {t : 𝕜} {x : E}
    (hF : ContDiffAt 𝕜 (minSmoothness 𝕜 2) F (t, x)) :
    HasDerivAt (spatialFDeriv F x) (fderiv 𝕜 (timeFDeriv F t) x) t := by
  -- Compute the parameter derivative of `s ↦ DF (s, x) (0, w)` and the spatial
  -- derivative of `timeFDeriv F t = fun z ↦ DF (t, z) (1, 0)`. Symmetry of the
  -- second derivative identifies these two mixed partials, pointwise in `w`.
  have hDFdiff : DifferentiableAt 𝕜 (fderiv 𝕜 F) (t, x) :=
    (TauCeti.ContDiffAt.hasFDerivAt_fderiv hF le_minSmoothness).differentiableAt
  have hdiff : DifferentiableAt 𝕜 (spatialFDeriv F x) t := by
    rw [spatialFDeriv_eq]
    fun_prop
  have heq : _root_.deriv (spatialFDeriv F x) t = fderiv 𝕜 (timeFDeriv F t) x := by
    apply ContinuousLinearMap.ext
    intro w
    have hParam := hasDerivAt_spatialFDeriv_apply_mixed hF (w := w)
    have hSpatial := hasFDerivAt_timeFDeriv_mixed hF
    have hsymm := hF.isSymmSndFDerivAt le_rfl
    calc
      _ = _root_.deriv (fun s => spatialFDeriv F x s w) t := by
        exact (hdiff.hasDerivAt.clm_apply_const w).deriv.symm
      _ = fderiv 𝕜 (fderiv 𝕜 F) (t, x) (1, 0) (0, w) := hParam.deriv
      _ = _ := by
        rw [hSpatial.fderiv]
        simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.inr_apply] using hsymm (1, 0) (0, w)
  rw [← heq]
  exact hdiff.hasDerivAt

/-- For a sufficiently smooth parametric map, the parameter derivative of its spatial Jacobian,
applied to `w`, is the spatial derivative of its parameter-velocity field applied to `w`. -/
theorem deriv_spatialFDeriv_apply {F : 𝕜 × E → F'} {t : 𝕜} {x w : E}
    (hF : ContDiffAt 𝕜 (minSmoothness 𝕜 2) F (t, x)) :
    _root_.deriv (fun s => spatialFDeriv F x s w) t =
      fderiv 𝕜 (timeFDeriv F t) x w := by
  exact ((hasDerivAt_spatialFDeriv hF).clm_apply_const w).deriv
