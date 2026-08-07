/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Mixed derivatives of a parametric map

For a map `F : ℝ × E → F'` that is twice continuously differentiable at the relevant point,
differentiating its spatial Jacobian in the parameter direction is the spatial derivative of its
parameter velocity. This is the mixed-partial identity needed to identify the derivative of a flow
pullback with a Lie bracket.

This supplies a prerequisite for Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main result

* `deriv_spatialFDeriv_apply`: the parameter derivative of the spatial Jacobian equals the
  derivative of the parameter-velocity field.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The infinitesimal adjoint".
-/

public section

noncomputable section

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-- The spatial Jacobian of a parametric map at `x`, as a function of the parameter. -/
def spatialFDeriv (F : ℝ × E → F') (x : E) (t : ℝ) : E →L[ℝ] F' :=
  (fderiv ℝ F (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)

@[simp]
theorem spatialFDeriv_apply (F : ℝ × E → F') (x : E) (t : ℝ) (w : E) :
    spatialFDeriv F x t w = fderiv ℝ F (t, x) (0, w) :=
  (rfl)

/-- The parameter velocity at zero of a parametric map. -/
def timeFDeriv (F : ℝ × E → F') (x : E) : F' :=
  fderiv ℝ F (0, x) (1, 0)

@[simp]
theorem timeFDeriv_apply (F : ℝ × E → F') (x : E) :
    timeFDeriv F x = fderiv ℝ F (0, x) (1, 0) :=
  (rfl)

/-- For a `C²` parametric map, the parameter derivative of its spatial Jacobian, applied to `w`,
is the spatial derivative of its parameter-velocity field applied to `w`. -/
private theorem deriv_spatialFDeriv_apply_aux {F : ℝ × E → F'} {x w : E}
    (hF : ContDiffAt ℝ 2 F (0, x)) :
    _root_.deriv (fun t => spatialFDeriv F x t w) 0 =
      fderiv ℝ (timeFDeriv F) x w := by
  let DF : ℝ × E → (ℝ × E →L[ℝ] F') := fderiv ℝ F
  have hDFdiff : DifferentiableAt ℝ DF (0, x) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDF := hDFdiff.hasFDerivAt
  have hp : HasDerivAt (fun t : ℝ => (t, x)) (1, 0) 0 :=
    (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).prodMk (hasDerivAt_const (x := 0) x)
  have hspace : HasDerivAt (fun _ : ℝ => ((0 : ℝ), w)) 0 0 :=
    hasDerivAt_const (x := 0) _
  have hDFp := hDF.comp_hasDerivAt 0 hp
  have hAraw := hDFp.clm_apply hspace
  have hA : HasDerivAt (fun t => DF (t, x) (0, w))
      (fderiv ℝ DF (0, x) (1, 0) (0, w)) 0 := by
    simpa only [Function.comp_apply, map_zero, add_zero] using hAraw
  have hq : HasFDerivAt (fun z : E => ((0 : ℝ), z))
      (ContinuousLinearMap.inr ℝ ℝ E) x :=
    (hasFDerivAt_const (x := x) (c := (0 : ℝ))).prodMk (hasFDerivAt_id (x := x))
  have hone : HasFDerivAt (fun _ : E => ((1 : ℝ), (0 : E)))
      (0 : E →L[ℝ] ℝ × E) x :=
    hasFDerivAt_const (x := x) ((1 : ℝ), (0 : E))
  have hVraw := (hDF.comp x hq).clm_apply hone
  have hV : HasFDerivAt (timeFDeriv F) (fderiv ℝ DF (0, x) ∘L
      ContinuousLinearMap.inr ℝ ℝ E |>.flip (1, 0)) x := by
    -- Expose the named wrapper as the slice used by `hVraw`.
    rw [show timeFDeriv F = fun z => fderiv ℝ F (0, z) (1, 0) from
      funext (timeFDeriv_apply F)]
    simpa only [DF, Function.comp_apply, map_zero, add_zero,
      ContinuousLinearMap.comp_zero, zero_add] using hVraw
  have hsymm := hF.isSymmSndFDerivAt (by norm_num)
  -- Identify the named spatial Jacobian with the applied full derivative.
  rw [show _root_.deriv (fun t => spatialFDeriv F x t w) 0 = _ from
    by simpa only [DF, spatialFDeriv_apply] using hA.deriv, hV.fderiv]
  simpa [DF, Function.comp_def] using hsymm (1, 0) (0, w)

/-- The derivative of the spatial Jacobian is the derivative of the parameter-velocity field. -/
theorem hasDerivAt_spatialFDeriv {F : ℝ × E → F'} {x : E}
    (hF : ContDiffAt ℝ 2 F (0, x)) :
    HasDerivAt (spatialFDeriv F x) (fderiv ℝ (timeFDeriv F) x) 0 := by
  have hdiff : DifferentiableAt ℝ (spatialFDeriv F x) 0 := by
    have hDFdiff : DifferentiableAt ℝ (fderiv ℝ F) (0, x) :=
      (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hraw : DifferentiableAt ℝ
        (fun t => (fderiv ℝ F (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) 0 := by
      fun_prop
    convert hraw using 1
    funext t
    ext w
    exact spatialFDeriv_apply F x t w
  have heq : _root_.deriv (spatialFDeriv F x) 0 = fderiv ℝ (timeFDeriv F) x := by
    apply ContinuousLinearMap.ext
    intro w
    have hw : HasDerivAt (fun _ : ℝ => w) 0 0 := hasDerivAt_const 0 w
    calc
      _ = _root_.deriv (fun t => spatialFDeriv F x t w) 0 := by
        simpa only [map_zero, add_zero] using (hdiff.hasDerivAt.clm_apply hw).deriv.symm
      _ = _ := deriv_spatialFDeriv_apply_aux hF
  rw [← heq]
  exact hdiff.hasDerivAt

/-- Applied form of `hasDerivAt_spatialFDeriv`. -/
theorem deriv_spatialFDeriv_apply {F : ℝ × E → F'} {x w : E}
    (hF : ContDiffAt ℝ 2 F (0, x)) :
    _root_.deriv (fun t => spatialFDeriv F x t w) 0 =
      fderiv ℝ (timeFDeriv F) x w := by
  have hw : HasDerivAt (fun _ : ℝ => w) 0 0 := hasDerivAt_const 0 w
  simpa only [map_zero, add_zero] using (hasDerivAt_spatialFDeriv hF).clm_apply hw |>.deriv
