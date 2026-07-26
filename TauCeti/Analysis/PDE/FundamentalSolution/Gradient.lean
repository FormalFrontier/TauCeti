/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Planar
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Gradient of the planar Newtonian kernel

This file computes the full Fréchet derivative of the planar Newtonian kernel away from its
pole.  The result is the covector

`-(2π ‖z‖²)⁻¹ ⟪z, ·⟫`,

whose operator norm is `(2π ‖z‖)⁻¹`.  Translated versions give the corresponding formulas for a
pole at an arbitrary point.  These inverse-distance estimates are the pointwise kernel input for
forming and differentiating planar Newtonian potentials.

The calculation uses Mathlib's derivative of the squared norm and the Fréchet chain rule for the
real logarithm.  It complements `FundamentalSolution.Flux`, which computes only the derivative in
the radial direction needed for the circle flux.

The normalization and inverse-distance gradient formula follow Evans, *Partial Differential
Equations*, Section 2.2.

## Main declarations

* `TauCeti.hasFDerivAt_planarNewtonianKernel`: the full derivative at a nonzero point.
* `TauCeti.fderiv_planarNewtonianKernel_apply`: its value in an arbitrary direction.
* `TauCeti.norm_fderiv_planarNewtonianKernel`: its inverse-distance operator norm.
* `TauCeti.hasFDerivAt_planarNewtonianKernel_sub`: the translated full derivative.
* `TauCeti.fderiv_planarNewtonianKernel_sub_apply`: the corresponding translated formula.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace

/-- Away from the origin, the planar Newtonian kernel has derivative
`-(2π)⁻¹ ‖z‖⁻² ⟪z, ·⟫`. -/
theorem hasFDerivAt_planarNewtonianKernel {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt planarNewtonianKernel
      ((-(2 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹) • innerSL ℝ z) z := by
  have hsq :
      HasFDerivAt (fun w : ℂ ↦ ‖w‖ ^ 2) (2 • innerSL ℝ z) z := by
    simpa only [id_eq, one_apply_eq_self, one_smul, ContinuousLinearMap.comp_id] using
      (hasFDerivAt_id z).norm_sq
  have hlog :
      HasFDerivAt (fun w : ℂ ↦ Real.log (‖w‖ ^ 2))
        ((‖z‖ ^ 2)⁻¹ • (2 • innerSL ℝ z)) z :=
    hsq.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz))
  have heq :
      planarNewtonianKernel =
        fun w : ℂ ↦ (-(2 * Real.pi)⁻¹ / 2) * Real.log (‖w‖ ^ 2) := by
    funext w
    rw [planarNewtonianKernel_def, Real.log_pow]
    ring
  have hmap :
      ((-(2 * Real.pi)⁻¹ / 2) • ((‖z‖ ^ 2)⁻¹ • (2 • innerSL ℝ z))) =
        ((-(2 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹) • innerSL ℝ z) := by
    ext v
    simp only [smul_apply, innerSL_apply_apply]
    ring
  rw [heq, ← hmap]
  exact hlog.const_mul (-(2 * Real.pi)⁻¹ / 2)

/-- The Fréchet derivative of the planar Newtonian kernel as a continuous linear functional. -/
theorem fderiv_planarNewtonianKernel {z : ℂ} (hz : z ≠ 0) :
    fderiv ℝ planarNewtonianKernel z =
      (-(2 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹) • innerSL ℝ z :=
  (hasFDerivAt_planarNewtonianKernel hz).fderiv

/-- The directional derivative of the planar Newtonian kernel is the radial inner-product
covector scaled by `-(2π ‖z‖²)⁻¹`. -/
theorem fderiv_planarNewtonianKernel_apply {z : ℂ} (hz : z ≠ 0) (v : ℂ) :
    fderiv ℝ planarNewtonianKernel z v =
      (-(2 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹) * ⟪z, v⟫_ℝ := by
  rw [fderiv_planarNewtonianKernel hz]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]

/-- The derivative of the planar Newtonian kernel has inverse-distance operator norm. -/
@[simp]
theorem norm_fderiv_planarNewtonianKernel {z : ℂ} (hz : z ≠ 0) :
    ‖fderiv ℝ planarNewtonianKernel z‖ = (2 * Real.pi * ‖z‖)⁻¹ := by
  rw [fderiv_planarNewtonianKernel hz, norm_smul, innerSL_apply_norm]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_inv, abs_mul, abs_of_pos (by positivity),
    abs_of_pos hpi, abs_inv, abs_pow, abs_of_pos hn]
  field_simp

/-- A planar Newtonian kernel with pole at `a` has the translated Fréchet derivative. -/
theorem hasFDerivAt_planarNewtonianKernel_sub {z a : ℂ} (hza : z ≠ a) :
    HasFDerivAt (fun w : ℂ ↦ planarNewtonianKernel (w - a))
      ((-(2 * Real.pi)⁻¹ * (‖z - a‖ ^ 2)⁻¹) • innerSL ℝ (z - a)) z := by
  rw [hasFDerivAt_comp_sub]
  exact hasFDerivAt_planarNewtonianKernel (sub_ne_zero.mpr hza)

/-- The Fréchet derivative of a planar Newtonian kernel with pole at `a`. -/
theorem fderiv_planarNewtonianKernel_sub {z a : ℂ} (hza : z ≠ a) :
    fderiv ℝ (fun w : ℂ ↦ planarNewtonianKernel (w - a)) z =
      (-(2 * Real.pi)⁻¹ * (‖z - a‖ ^ 2)⁻¹) • innerSL ℝ (z - a) :=
  (hasFDerivAt_planarNewtonianKernel_sub hza).fderiv

/-- The directional derivative of a planar Newtonian kernel with pole at `a`. -/
theorem fderiv_planarNewtonianKernel_sub_apply {z a : ℂ} (hza : z ≠ a) (v : ℂ) :
    fderiv ℝ (fun w : ℂ ↦ planarNewtonianKernel (w - a)) z v =
      (-(2 * Real.pi)⁻¹ * (‖z - a‖ ^ 2)⁻¹) * ⟪z - a, v⟫_ℝ := by
  rw [fderiv_planarNewtonianKernel_sub hza]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]

/-- The derivative of a planar Newtonian kernel with pole at `a` has inverse-distance norm. -/
@[simp]
theorem norm_fderiv_planarNewtonianKernel_sub {z a : ℂ} (hza : z ≠ a) :
    ‖fderiv ℝ (fun w : ℂ ↦ planarNewtonianKernel (w - a)) z‖ =
      (2 * Real.pi * ‖z - a‖)⁻¹ := by
  rw [fderiv_comp_sub]
  exact norm_fderiv_planarNewtonianKernel (sub_ne_zero.mpr hza)

end TauCeti

end
