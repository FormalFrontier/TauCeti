/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse

/-!
# Mixed derivatives of a parametric map

For a twice continuously differentiable map `F : ℝ × E → E`, differentiating its spatial
Jacobian in the parameter direction is the spatial derivative of its parameter velocity. This is
the mixed-partial identity needed to identify the derivative of a flow pullback with a Lie bracket.

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

/-- The spatial Jacobian of a parametric map at `x`, as a function of the parameter. -/
def spatialFDeriv (F : ℝ × E → E) (x : E) (t : ℝ) : E →L[ℝ] E :=
  (fderiv ℝ F (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)

@[simp]
theorem spatialFDeriv_apply (F : ℝ × E → E) (x : E) (t : ℝ) (w : E) :
    spatialFDeriv F x t w = fderiv ℝ F (t, x) (0, w) :=
  (rfl)

/-- The parameter velocity at zero of a parametric map. -/
def timeFDeriv (F : ℝ × E → E) (x : E) : E :=
  fderiv ℝ F (0, x) (1, 0)

@[simp]
theorem timeFDeriv_apply (F : ℝ × E → E) (x : E) :
    timeFDeriv F x = fderiv ℝ F (0, x) (1, 0) :=
  (rfl)

/-- For a `C²` parametric map, the parameter derivative of its spatial Jacobian, applied to `w`,
is the spatial derivative of its parameter-velocity field applied to `w`. -/
theorem deriv_spatialFDeriv_apply {F : ℝ × E → E} {x w : E}
    (hF : ContDiffAt ℝ 2 F (0, x)) :
    _root_.deriv (fun t => spatialFDeriv F x t w) 0 =
      fderiv ℝ (timeFDeriv F) x w := by
  let DF : ℝ × E → (ℝ × E →L[ℝ] E) := fderiv ℝ F
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
  change HasFDerivAt (fun z => DF (0, z) (1, 0)) _ x at hVraw
  have hsymm := hF.isSymmSndFDerivAt (by norm_num)
  change _root_.deriv (fun t => DF (t, x) (0, w)) 0 =
    fderiv ℝ (fun z => DF (0, z) (1, 0)) x w
  rw [hA.deriv, hVraw.fderiv]
  simpa [DF, Function.comp_def] using hsymm (1, 0) (0, w)
