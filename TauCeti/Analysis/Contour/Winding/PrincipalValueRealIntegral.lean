/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Winding.RealIntegral
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The real part of a principal-value winding number

Hungerbühler--Wasem Proposition 2.3 replaces the singular complex index integrand along a curve
through `w` by the real integrand

`((γ - w)⁻¹ * γ').im = (x y' - y x') / (x² + y²)`.

The complex integral generally exists only as a Cauchy principal value.  By contrast, once the
real integrand is interval-integrable, deleting the part of the curve inside an `ε`-ball about
`w` does not change its limiting integral.  This file identifies the imaginary part of the
complex principal value with that ordinary real integral.  After the normalization by
`(2πi)⁻¹`, this is exactly the real part of the generalized winding number.

The result is the analytic bridge needed by the on-curve form of HW Proposition 2.3: the geometric
part of that proposition supplies integrability (from boundedness at the finitely many crossings),
while the remaining assertion that the principal value is purely imaginary upgrades the real-part
identity here to the full real winding formula.

## Main results

* `HasCauchyPVAt.im_eq_integral_realWindingIntegrand` identifies the imaginary part of the
  Cauchy-kernel principal value with the ordinary integral of `realWindingIntegrand`.
* `windingNumber_re_eq_real_integral` gives the corresponding formula for the real part of the
  generalized winding number.
* `windingNumber_eq_real_integral_of_im_eq_zero` gives the full real formula when the winding
  number is known to be real.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), Proposition 2.3.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set Topology intervalIntegral

namespace TauCeti.Contour

variable {γ : ℝ → ℂ} {a b : ℝ} {w L : ℂ}

private theorem tendsto_integral_truncated_realWindingIntegrand
    (h_int : IntervalIntegrable
      (fun t => realWindingIntegrand (γ t - w) (deriv γ t)) volume a b)
    (h_meas : ∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun t => if ‖γ t - w‖ > ε then realWindingIntegrand (γ t - w) (deriv γ t) else 0)
        (volume.restrict (uIoc a b))) :
    Tendsto (fun ε => ∫ t in a..b,
        if ‖γ t - w‖ > ε then realWindingIntegrand (γ t - w) (deriv γ t) else 0)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t in a..b, realWindingIntegrand (γ t - w) (deriv γ t))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (E := ℝ)
    (bound := fun t => ‖realWindingIntegrand (γ t - w) (deriv γ t)‖)
  · exact h_meas
  · exact Filter.Eventually.of_forall fun ε => MeasureTheory.ae_of_all _ fun t _ => by
      by_cases hfar : ‖γ t - w‖ > ε
      · rw [if_pos hfar]
      · rw [if_neg hfar, norm_zero]
        exact norm_nonneg _
  · exact h_int.norm
  · exact MeasureTheory.ae_of_all _ fun t _ => by
      by_cases ht : γ t = w
      · simp [ht]
      · have hpos : 0 < ‖γ t - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr ht)
        refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
        simp [hε.2]

/-- The imaginary part of a Cauchy principal value of the index integral is the ordinary integral
of the real winding integrand, provided that real integrand is interval-integrable.  This remains
valid when the curve passes through `w`: both truncations delete the same `ε`-ball, and dominated
convergence restores the point values at crossings, where `realWindingIntegrand 0 v = 0`. -/
theorem HasCauchyPVAt.im_eq_integral_realWindingIntegrand
    (h : HasCauchyPVAt γ a b (fun z => (z - w)⁻¹) w L)
    (h_int : IntervalIntegrable
      (fun t => realWindingIntegrand (γ t - w) (deriv γ t)) volume a b) :
    L.im = ∫ t in a..b, realWindingIntegrand (γ t - w) (deriv γ t) := by
  have h_meas : ∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun t => if ‖γ t - w‖ > ε then realWindingIntegrand (γ t - w) (deriv γ t) else 0)
        (volume.restrict (uIoc a b)) := by
    filter_upwards [h.eventually_intervalIntegrable] with ε hε
    have him := MeasureTheory.AEStronglyMeasurable.im
      hε.aestronglyMeasurable_restrict_uIoc
    refine him.congr (MeasureTheory.ae_of_all _ fun t => ?_)
    by_cases hfar : ‖γ t - w‖ > ε
    · rw [RCLike.im_eq_complex_im]
      simpa only [if_pos hfar] using
        (realWindingIntegrand_def (γ t - w) (deriv γ t)).symm
    · simp [hfar]
  have h_real := tendsto_integral_truncated_realWindingIntegrand h_int h_meas
  have h_im : Tendsto (fun ε => (∫ t in a..b,
      if ‖γ t - w‖ > ε then (γ t - w)⁻¹ * deriv γ t else 0).im)
      (𝓝[>] (0 : ℝ)) (𝓝 L.im) := (continuous_im.tendsto L).comp h.tendsto
  have h_im' : Tendsto (fun ε => ∫ t in a..b,
      if ‖γ t - w‖ > ε then realWindingIntegrand (γ t - w) (deriv γ t) else 0)
      (𝓝[>] (0 : ℝ)) (𝓝 L.im) := by
    refine h_im.congr' ?_
    filter_upwards [h.eventually_intervalIntegrable] with ε hε
    symm
    calc
      (∫ t in a..b,
          if ‖γ t - w‖ > ε then realWindingIntegrand (γ t - w) (deriv γ t) else 0) =
          ∫ t in a..b, ((if ‖γ t - w‖ > ε then
            (γ t - w)⁻¹ * deriv γ t else 0 : ℂ).im) := by
        exact intervalIntegral.integral_congr fun t _ => by
          by_cases hfar : ‖γ t - w‖ > ε
          · simpa only [if_pos hfar] using
              realWindingIntegrand_def (γ t - w) (deriv γ t)
          · simp [hfar]
      _ = (∫ t in a..b,
          if ‖γ t - w‖ > ε then (γ t - w)⁻¹ * deriv γ t else 0).im :=
        intervalIntegral_im hε
  exact tendsto_nhds_unique h_im' h_real

/-- **The on-curve real-integral identity for the real part of the winding number.**  If the
Cauchy principal value defining `windingNumber γ a b w` exists and its real winding integrand is
interval-integrable, then

`(windingNumber γ a b w).re = (1 / 2π) ∫ realWindingIntegrand (γ - w) γ'`.

No avoidance hypothesis is imposed, so the curve may pass through `w`. -/
theorem windingNumber_re_eq_real_integral
    (h : HasCauchyPVAt γ a b (fun z => (z - w)⁻¹) w L)
    (h_int : IntervalIntegrable
      (fun t => realWindingIntegrand (γ t - w) (deriv γ t)) volume a b) :
    (windingNumber γ a b w).re =
      1 / (2 * Real.pi) *
        ∫ t in a..b, realWindingIntegrand (γ t - w) (deriv γ t) := by
  rw [windingNumber_eq_of_hasCauchyPVAt h, mul_re,
    h.im_eq_integral_realWindingIntegrand h_int]
  simp [Complex.inv_re, Complex.inv_im, Complex.normSq]

/-- The full on-curve real-integral formula when the generalized winding number is real.  This
separates the measure-theoretic content proved here from the geometric fact that the relevant
closed immersed-curve principal value is purely imaginary before normalization. -/
theorem windingNumber_eq_real_integral_of_im_eq_zero
    (h : HasCauchyPVAt γ a b (fun z => (z - w)⁻¹) w L)
    (h_int : IntervalIntegrable
      (fun t => realWindingIntegrand (γ t - w) (deriv γ t)) volume a b)
    (h_im : (windingNumber γ a b w).im = 0) :
    windingNumber γ a b w =
      ((1 / (2 * Real.pi) *
        ∫ t in a..b, realWindingIntegrand (γ t - w) (deriv γ t) : ℝ) : ℂ) := by
  apply Complex.ext
  · simpa using windingNumber_re_eq_real_integral h h_int
  · simpa using h_im

end TauCeti.Contour

end

end
