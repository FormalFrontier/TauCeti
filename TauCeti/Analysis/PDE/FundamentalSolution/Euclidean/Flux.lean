/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Flux of the Newtonian kernel in Euclidean space

For every dimension `n ≠ 0` and `n ≠ 2`, this file computes the outward normal derivative of
the normalized Newtonian kernel on a sphere. Integrating against the canonical measure on the
unit sphere, with the radial surface Jacobian, gives total flux `-1` through every sphere
centered at the pole. This is the boundary normalization needed for the distributional identity
`-Δ Gₙ = δ₀`. The planar case `n = 2` is treated in
`TauCeti.Analysis.PDE.FundamentalSolution.Flux`.

The measure `volume.toSphere` is Mathlib's polar-coordinate surface measure. Its total mass is
`n` times the volume of the Euclidean unit ball.

## Main declarations

* `TauCeti.fderiv_newtonianKernel_sub_apply_sphere_normal`: the outward normal derivative on a
  sphere.
* `TauCeti.rpow_mul_integral_fderiv_newtonianKernel_sub_sphere_normal`: the total sphere flux is
  `-1`.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric

open scoped RealInnerProductSpace

/-- On the sphere of radius `r` centered at its pole, the outward normal derivative of the
Newtonian kernel is constant and equals `-(n ωₙ)⁻¹ r^(1-n)`. -/
@[simp]
theorem fderiv_newtonianKernel_sub_apply_sphere_normal (n : ℕ) (hn2 : n ≠ 2)
    {a : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    fderiv ℝ (fun y ↦ newtonianKernel n (y - a)) (a + r • (u : EuclideanSpace ℝ (Fin n))) u =
      -(((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        r ^ (1 - (n : ℝ))) := by
  have hu_norm : ‖(u : EuclideanSpace ℝ (Fin n))‖ = 1 := norm_eq_of_mem_sphere u
  have hru : r • (u : EuclideanSpace ℝ (Fin n)) ≠ 0 :=
    smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere u)
  have hnorm_ru : ‖r • (u : EuclideanSpace ℝ (Fin n))‖ = r := by
    rw [norm_smul_of_nonneg hr.le, hu_norm, mul_one]
  rw [fderiv_newtonianKernel_sub_apply n hn2 (by simpa using hru)]
  simp only [add_sub_cancel_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hu_norm,
    one_pow, mul_one]
  rw [hnorm_ru]
  have hpow : r ^ (-(n : ℝ)) * r = r ^ (1 - (n : ℝ)) := by
    rw [← Real.rpow_add_one hr.ne', neg_add_eq_sub]
  rw [mul_assoc, hpow]

/-- The outward flux of the Newtonian kernel through any sphere centered at its pole is `-1`.
The factor `r ^ (n - 1)` is the surface Jacobian for radial scaling from the unit sphere. -/
theorem rpow_mul_integral_fderiv_newtonianKernel_sub_sphere_normal
    (n : ℕ) (hn0 : n ≠ 0) (hn2 : n ≠ 2)
    {a : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) :
    r ^ (n - 1) * ∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        fderiv ℝ (fun y ↦ newtonianKernel n (y - a))
          (a + r • (u : EuclideanSpace ℝ (Fin n))) u ∂volume.toSphere = -1 := by
  simp_rw [fderiv_newtonianKernel_sub_apply_sphere_normal n hn2 hr]
  rw [integral_const]
  simp only [Measure.toSphere_real_apply_univ, finrank_euclideanSpace, Fintype.card_fin,
    smul_eq_mul]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hvol := volume_real_unitBall_pos n
  -- Express the natural-power surface Jacobian as a real power before cancelling exponents.
  have h_surface_rpow : r ^ (n - 1) = r ^ ((n : ℝ) - 1) := by
    rw [← Real.rpow_natCast, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn0), Nat.cast_one]
  rw [h_surface_rpow]
  calc
    r ^ ((n : ℝ) - 1) *
          ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
            -(((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
              r ^ (1 - (n : ℝ)))) =
        -(r ^ ((n : ℝ) - 1) * r ^ (1 - (n : ℝ))) := by
      field_simp
    _ = -1 := by
      rw [← Real.rpow_add hr]
      norm_num

end TauCeti

end
