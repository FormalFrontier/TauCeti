/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Planar
public import Mathlib.Analysis.Calculus.FDeriv.Norm
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Flux of the planar Newtonian kernel

This file computes the outward normal derivative of the planar Newtonian kernel on a circle.
The resulting flux is `-1`, as required for the fundamental solution of the negative Laplacian.
This calculation fixes the normalization of `planarNewtonianKernel` and is the boundary
calculation needed for its later distributional identity `-Δ G = δ₀`.

## Main declarations

* `TauCeti.fderiv_planarNewtonianKernel_self`: the radial derivative of the kernel.
* `TauCeti.fderiv_planarNewtonianKernel_sub_circle_normal`: its outward normal derivative on a
  circle centered at the pole.
* `TauCeti.integral_fderiv_planarNewtonianKernel_sub_circle_normal`: the total circle flux is `-1`.
-/

public section

noncomputable section

namespace TauCeti

open scoped Interval

/-- The derivative of the planar Newtonian kernel in the radial direction is `-(2π)⁻¹`. -/
@[simp]
theorem fderiv_planarNewtonianKernel_self {z : ℂ} (hz : z ≠ 0) :
    fderiv ℝ planarNewtonianKernel z z = -(2 * Real.pi)⁻¹ := by
  have hnorm : DifferentiableAt ℝ (fun w : ℂ ↦ ‖w‖) z :=
    (differentiableAt_fun_id : DifferentiableAt ℝ (fun w : ℂ ↦ w) z).norm ℂ hz
  have hlog :
      HasFDerivAt (fun w : ℂ ↦ Real.log ‖w‖)
        ((‖z‖ : ℝ)⁻¹ • fderiv ℝ (fun w : ℂ ↦ ‖w‖) z) z :=
    hnorm.hasFDerivAt.log (norm_ne_zero_iff.mpr hz)
  rw [show planarNewtonianKernel =
    fun w : ℂ ↦ -(2 * Real.pi)⁻¹ * Real.log ‖w‖ by
      ext w
      exact planarNewtonianKernel_def w]
  rw [(hlog.const_mul (-(2 * Real.pi)⁻¹)).fderiv]
  simp only [smul_apply, smul_eq_mul]
  rw [DifferentiableAt.fderiv_norm_self hnorm]
  rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz), mul_one]

/-- The derivative of a translated planar Newtonian kernel in the radial direction from its pole
is `-(2π)⁻¹`. -/
@[simp]
theorem fderiv_planarNewtonianKernel_sub_self {z a : ℂ} (hza : z ≠ a) :
    fderiv ℝ (fun w ↦ planarNewtonianKernel (w - a)) z (z - a) =
      -(2 * Real.pi)⁻¹ := by
  rw [fderiv_comp_sub]
  exact fderiv_planarNewtonianKernel_self (sub_ne_zero.mpr hza)

/-- On the circle of radius `r`, the outward normal derivative of the planar Newtonian kernel is
`-(2πr)⁻¹`. -/
@[simp]
theorem fderiv_planarNewtonianKernel_sub_circle_normal {a : ℂ} {r θ : ℝ} (hr : 0 < r) :
    fderiv ℝ (fun w ↦ planarNewtonianKernel (w - a)) (circleMap a r θ)
        ((r : ℂ)⁻¹ * circleMap 0 r θ) = -(2 * Real.pi * r)⁻¹ := by
  rw [fderiv_comp_sub, circleMap_sub_center]
  have hz : circleMap 0 r θ ≠ 0 := by
    rw [ne_eq, ← norm_eq_zero, norm_circleMap_zero, abs_of_pos hr]
    exact hr.ne'
  rw [← Complex.ofReal_inv, ← Complex.real_smul]
  rw [map_smul, fderiv_planarNewtonianKernel_self hz]
  simp only [smul_eq_mul]
  field_simp

/-- The arclength-weighted normal derivative of the planar Newtonian kernel is constant on every
positively oriented circle around its pole. -/
@[simp]
theorem radius_mul_fderiv_planarNewtonianKernel_sub_circle_normal
    {a : ℂ} {r θ : ℝ} (hr : 0 < r) :
    r * fderiv ℝ (fun w ↦ planarNewtonianKernel (w - a)) (circleMap a r θ)
        ((r : ℂ)⁻¹ * circleMap 0 r θ) = -(2 * Real.pi)⁻¹ := by
  rw [fderiv_planarNewtonianKernel_sub_circle_normal hr]
  field_simp

/-- The outward flux of the planar Newtonian kernel through any circle centered at its pole is
`-1`. The factor `r` is the arclength Jacobian in the angular parametrization. -/
@[simp]
theorem integral_fderiv_planarNewtonianKernel_sub_circle_normal {a : ℂ} {r : ℝ} (hr : 0 < r) :
    r * ∫ θ : ℝ in 0..2 * Real.pi,
        fderiv ℝ (fun w ↦ planarNewtonianKernel (w - a)) (circleMap a r θ)
          ((r : ℂ)⁻¹ * circleMap 0 r θ) = -1 := by
  simp_rw [fderiv_planarNewtonianKernel_sub_circle_normal hr]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  field_simp

end TauCeti

end
