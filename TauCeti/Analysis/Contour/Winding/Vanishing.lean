/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Basic
import TauCeti.Analysis.Contour.Winding.Integer
import TauCeti.Analysis.Contour.Curve.IntegralBound

/-!
# The winding number vanishes far from a bounded closed curve

For a closed curve `γ` continuous on the compact interval `Set.uIcc a b` (so its image is bounded),
differentiable off a countable set, with interval-integrable derivative, the generalized winding
number `fun w ↦ windingNumber γ a b w` vanishes for every `w` sufficiently far from the origin:
`windingNumber_eventually_zero_cocompact` states this as an eventual property along the cocompact
filter, together with the fact that such `w` lie off the curve. This is the input to the Liouville
step of Dixon's proof of the homology form of Cauchy's theorem (roadmap `homologyCauchyTheorem`):
the Dixon function agrees with `dixonH2` wherever the winding number is zero.

## Main results

* `TauCeti.Contour.windingNumber_eventually_zero_cocompact` — off the curve, the winding number is
  eventually `0` along `cocompact ℂ`.

## Provenance

Adapted from `winding_eventually_zero_cocompact_of_lipschitz` in `NullHomologous.lean` of the
AINTLIB `LeanModularForms` development. The raw-function port replaces the Lipschitz derivative
bound with the `L¹` norm `∫ ‖deriv γ‖`, so continuity on the compact interval (which bounds the
image) and interval-integrability of the derivative suffice — no Lipschitz hypothesis.
-/

public section

open Complex MeasureTheory Set

open scoped Real Topology Interval

namespace TauCeti.Contour

/-- The value `‖(2πi)⁻¹‖ = (2π)⁻¹` normalizing the index integral to the winding number. -/
private theorem norm_inv_two_pi_I : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
  rw [norm_inv, show (2 : ℂ) * (Real.pi : ℂ) * Complex.I = ((2 * Real.pi : ℝ) : ℂ) * Complex.I from
      by push_cast; ring, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]

/-- **The winding number vanishes for a point far from a bounded closed curve.** If the closed curve
`γ` lies in the closed ball of radius `R` and `‖w‖` exceeds `R + (∫ ‖deriv γ‖) / (2π)`, then the
integer-valued winding number about `w` has absolute value below `1`, hence is `0`. -/
private theorem windingNumber_eq_zero_of_far {γ : ℝ → ℂ} {a b R : ℝ} {P : Set ℝ} {w : ℂ}
    (hclosed : γ a = γ b) (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b)
    (hR : ∀ t ∈ uIcc a b, ‖γ t‖ ≤ R) (hw : R + (∫ t in Ι a b, ‖deriv γ t‖) / (2 * Real.pi) < ‖w‖) :
    windingNumber γ a b w = 0 := by
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hD_nonneg : 0 ≤ ∫ t in Ι a b, ‖deriv γ t‖ := integral_nonneg fun _ => norm_nonneg _
  have hwR : R < ‖w‖ :=
    lt_of_le_of_lt (le_add_of_nonneg_right (div_nonneg hD_nonneg h2pi_pos.le)) hw
  have hpos : 0 < ‖w‖ - R := by linarith
  have h_off : ∀ t ∈ uIcc a b, γ t ≠ w := fun t ht heq => by
    have h := hR t ht; rw [heq] at h; linarith
  obtain ⟨n, hn⟩ := exists_int_windingNumber_of_closed hclosed hP hγ_cont hγ_diff h_off
    (intervalIntegrable_inv_sub_mul_deriv hγ_cont h_off hderiv_int)
  have h_norm_wind : ‖windingNumber γ a b w‖
      ≤ (2 * Real.pi)⁻¹ * ((∫ t in Ι a b, ‖deriv γ t‖) / (‖w‖ - R)) := by
    rw [windingNumber_eq_integral_of_avoidance hγ_cont h_off
        (intervalIntegrable_inv_sub_mul_deriv hγ_cont h_off hderiv_int),
      norm_mul, norm_inv_two_pi_I]
    exact mul_le_mul_of_nonneg_left
      (norm_integral_inv_sub_mul_le hderiv_int (fun t ht ↦ hR t (uIoc_subset_uIcc ht)) hwR)
      (by positivity)
  have h_lt_one : (2 * Real.pi)⁻¹ * ((∫ t in Ι a b, ‖deriv γ t‖) / (‖w‖ - R)) < 1 := by
    have key : (∫ t in Ι a b, ‖deriv γ t‖) / (2 * Real.pi) < ‖w‖ - R := by
      rw [lt_sub_iff_add_lt]; linarith
    rw [inv_mul_eq_div, div_div, div_lt_one (mul_pos hpos h2pi_pos)]
    exact (div_lt_iff₀ h2pi_pos).mp key
  have h_abs : |(n : ℝ)| < 1 := by
    have h := lt_of_le_of_lt h_norm_wind h_lt_one
    rwa [hn, Complex.norm_intCast] at h
  rw [hn, show n = 0 from Int.abs_lt_one_iff.mp (by exact_mod_cast h_abs), Int.cast_zero]

/-- **The winding number is eventually zero far from a bounded closed curve.** For a closed curve
`γ` (`γ a = γ b`) continuous on `Set.uIcc a b`, differentiable off a countable set `P`, with
interval-integrable derivative, every point `w` far enough from the origin lies off the curve and
has winding number `0`; equivalently, `fun w ↦ (γ avoids w) ∧ windingNumber γ a b w = 0` holds
eventually along `cocompact ℂ`. The bounded image (continuity on the compact interval) and the
integer-valuedness of the winding number for a closed curve force the small far-field value to be
exactly `0`. -/
theorem windingNumber_eventually_zero_cocompact {γ : ℝ → ℂ} {a b : ℝ} {P : Set ℝ}
    (hclosed : γ a = γ b) (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) :
    ∀ᶠ w in Filter.cocompact ℂ,
      (∀ t ∈ uIcc a b, γ t ≠ w) ∧ windingNumber γ a b w = 0 := by
  obtain ⟨R, hR⟩ := isCompact_uIcc.exists_bound_of_continuousOn hγ_cont
  have hD_nonneg : 0 ≤ ∫ t in Ι a b, ‖deriv γ t‖ := integral_nonneg fun _ => norm_nonneg _
  set RR : ℝ := R + (∫ t in Ι a b, ‖deriv γ t‖) / (2 * Real.pi) with hRR_def
  have hR_le_RR : R ≤ RR := le_add_of_nonneg_right (div_nonneg hD_nonneg (by positivity))
  have h_mem : {w : ℂ | RR < ‖w‖} ∈ Filter.cocompact ℂ := by
    rw [Filter.mem_cocompact]
    exact ⟨Metric.closedBall 0 RR, isCompact_closedBall 0 RR, fun w hw => by
      simpa [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using hw⟩
  filter_upwards [h_mem] with w (hw : RR < ‖w‖)
  refine ⟨fun t ht heq => ?_, windingNumber_eq_zero_of_far hclosed hP hγ_cont hγ_diff hderiv_int hR
    (hRR_def ▸ hw)⟩
  have h := hR t ht; rw [heq] at h
  linarith [lt_of_le_of_lt hR_le_RR hw]

end TauCeti.Contour
