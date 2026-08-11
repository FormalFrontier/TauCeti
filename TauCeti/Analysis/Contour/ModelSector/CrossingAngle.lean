/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.ModelSector.Closed
public import TauCeti.Analysis.Contour.RegularityConditions
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Angle

/-!
# The model sector's crossing angle is its opening angle

`TauCeti.Contour.crossingAngle` reads the opening angle at a crossing off the two one-sided
tangent limits, and `TauCeti.Contour.windingNumber_closedModelSector` gives the model sector of
opening `α` winding number `α / 2π` about its corner. Nothing connected the two: the winding
value was stated in terms of the *parameter* `α`, and the crossing angle in terms of *tangents*,
with no theorem saying they agree.

This file supplies that bridge. `crossingAngle_modelSector` holds for every real `α`: the
crossing angle at the corner is the `[0, 2π)` normalisation of `α`, which is `α` itself exactly
when `0 ≤ α < 2π`. Under those bounds,
`windingNumber_closedModelSector_eq_crossingAngle_div_two_pi` then restates the winding number
about the corner as the crossing angle over `2π`, with no reference to the parametrisation.

That is the shape a general curve can be compared against, since a curve is tangent to a model
sector without being equal to one.

## Main declarations

* `TauCeti.Contour.crossingAngle_modelSector`: the model sector of opening `α` has crossing
  angle `α` at its corner — stated for every real `α` as the `[0, 2π)` normalisation of `α`,
  which is `α` itself exactly when `0 ≤ α < 2π`.
* `TauCeti.Contour.windingNumber_closedModelSector_eq_crossingAngle_div_two_pi`: hence its
  winding number about the corner is `crossingAngle / (2π)`.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 — the model sector is their equation (2.4), and the crossing-angle
  reading of its index is what this file supplies.
-/

public section

open Complex Filter Set

open scoped Real Topology

namespace TauCeti

namespace Contour

variable {z₀ : ℂ} {r φ α : ℝ}

/-- Near its corner the model sector is its two-ray corner, so the two curves have the same
derivative there. -/
private theorem modelSector_deriv_eventuallyEq (hr : 0 < r) (φ α : ℝ) {t : ℝ} (ht : |t| < r) :
    deriv (modelSector z₀ r φ α) t =
      deriv (twoRayCorner z₀ (Complex.exp ((φ + α : ℝ) * Complex.I))
        (Complex.exp ((φ : ℝ) * Complex.I))) t := by
  refine Filter.EventuallyEq.deriv_eq ?_
  have hmem : Set.Ioo (-r) r ∈ 𝓝 t :=
    Ioo_mem_nhds (by cases abs_lt.mp ht; linarith) (abs_lt.mp ht).2
  filter_upwards [hmem] with s hs
  exact (modelSector_eqOn_corner z₀ hr.le φ α (by rwa [Set.uIoo_of_le (by linarith)])).symm

/-- **The model sector's crossing angle is its opening angle.** At the corner the incoming
tangent is `-exp((φ + α)i)` and the outgoing one is `exp(φ i)`, so the normalised angle from the
exit ray to the reversed entry ray is `α` itself — for `0 ≤ α < 2π`, the range on which the
opening angle determines the sector. -/
@[simp]
theorem crossingAngle_modelSector (hr : 0 < r) (φ : ℝ) (α : ℝ) :
    crossingAngle (modelSector z₀ r φ α) 0 = toIcoMod Real.two_pi_pos 0 α := by
  set u : ℂ := Complex.exp ((φ + α : ℝ) * Complex.I) with hu
  set v : ℂ := Complex.exp ((φ : ℝ) * Complex.I) with hv
  -- The one-sided tangent limits are the two ray directions: the derivative is locally constant
  -- on each side of the corner.
  have hderiv : ∀ {t : ℝ}, t ≠ 0 → |t| < r →
      deriv (modelSector z₀ r φ α) t = if t < 0 then -u else v := fun ht htr => by
    rw [modelSector_deriv_eventuallyEq hr φ α htr, deriv_twoRayCorner_of_ne ht]
  have h_R : Tendsto (deriv (modelSector z₀ r φ α)) (𝓝[>] 0) (𝓝 v) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT hr] with s hs
    rw [hderiv (ne_of_gt hs.1) (by rw [abs_of_pos hs.1]; exact hs.2),
      ite_eq_right (not_lt.mpr hs.1.le)]
  have h_L : Tendsto (deriv (modelSector z₀ r φ α)) (𝓝[<] 0) (𝓝 (-u)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsLT (neg_lt_zero.mpr hr)] with s hs
    rw [hderiv (ne_of_lt hs.2) (by rw [abs_of_neg hs.2]; linarith [hs.1]), ite_eq_left hs.2]
  rw [crossingAngle_eq_of_tendsto h_R h_L, neg_neg]
  -- `arg u - arg v` is `α` in `Real.Angle`; the shared transport reads that back.
  refine Real.Angle.toIcoMod_eq_toIcoMod_iff_coe_eq.mpr ?_
  rw [Real.Angle.coe_sub, hu, hv, Complex.arg_exp_mul_I, Complex.arg_exp_mul_I,
    Real.Angle.coe_toIocMod, Real.Angle.coe_toIocMod, ← Real.Angle.coe_sub]
  norm_num

/-- **The model sector's winding number, read off its crossing angle.** Combining
`windingNumber_closedModelSector` with `crossingAngle_modelSector`: the winding number about the
corner is the crossing angle over `2π`, with no reference to the parametrisation. -/
theorem windingNumber_closedModelSector_eq_crossingAngle_div_two_pi (hr : 0 < r) (φ : ℝ)
    (hα : 0 ≤ α) (hα2 : α < 2 * Real.pi) :
    windingNumber (modelSector z₀ r φ α) (-r) (r + α) z₀ =
      (crossingAngle (modelSector z₀ r φ α) 0 : ℂ) / (2 * (Real.pi : ℂ)) := by
  rw [crossingAngle_modelSector hr φ α, windingNumber_closedModelSector hr φ hα,
    (toIcoMod_eq_self Real.two_pi_pos).mpr (Set.mem_Ico.mpr ⟨hα, by rw [zero_add]; exact hα2⟩)]

end Contour

end TauCeti
