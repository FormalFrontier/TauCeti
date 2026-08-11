/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.Dixon.Def
import TauCeti.Analysis.Contour.Curve.Distance
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Holomorphy of Dixon's `h₂` off the curve

Dixon's `h₂` integral `dixonH2 f γ a b w = ∫ t in a..b, f (γ t) / (γ t - w) * deriv γ t` is
holomorphic in the point `w`, at every `w` off the curve. This is the Cauchy-type half of the
analyticity of Dixon's glued function.

## Main results

* `TauCeti.Contour.differentiableAt_dixonH2` — `fun w ↦ dixonH2 f γ a b w` is complex-differentiable
  at every point off the curve, given continuity of `γ` and interval-integrability of the Cauchy
  integrand `f (γ ·) / (γ · - w) · deriv γ`.

This feeds the `homologyCauchyTheorem` roadmap target
(`TauCetiRoadmap/ContourIntegration/Suggested.lean`, Layer 3, Dixon's argument).

## Provenance

Adapted from `dixonH2_differentiableAt` / `dixonH2_differentiableAt_of_regular` in `DixonDiff.lean`
of the AINTLIB `LeanModularForms` development, restated for a raw `γ : ℝ → ℂ` on an oriented
interval and phrased with the integrable Cauchy integrand (weaker than a continuous `f` and a
separately integrable derivative). See J. D. Dixon, *A brief proof of Cauchy's integral theorem*
(1971).
-/

public section

open Complex MeasureTheory Set

open scoped Real Interval

namespace TauCeti.Contour

section

variable {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {w : ℂ}

/-- The `w`-derivative of a single pole factor: `w' ↦ (z - w')⁻¹ · c` has derivative
`(z - w)⁻¹² · c` at `w` whenever `z ≠ w`. -/
private theorem h2_pole_hasDerivAt (c z w : ℂ) (hne : z - w ≠ 0) :
    HasDerivAt (fun w' ↦ (z - w')⁻¹ * c) ((z - w)⁻¹ ^ 2 * c) w := by
  have h_sub : HasDerivAt (fun w' ↦ z - w') (-1) w := HasDerivAt.const_sub z (hasDerivAt_id w)
  have h_inv : HasDerivAt (fun w' ↦ (z - w')⁻¹) ((z - w)⁻¹ ^ 2) w :=
    (h_sub.inv hne).congr_deriv (by rw [inv_pow]; ring)
  exact h_inv.mul_const c

/-- The pole factor `(γ · - w')⁻¹` is continuous on `uIcc a b` when `w'` is off the curve. -/
private theorem h2_kernel_continuousOn (hγ_cont : ContinuousOn γ (uIcc a b)) {w' : ℂ}
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ w') : ContinuousOn (fun t ↦ (γ t - w')⁻¹) (uIcc a b) :=
  (hγ_cont.sub continuousOn_const).inv₀ fun t ht ↦ sub_ne_zero.mpr (hoff t ht)

/-- A continuous factor times the a.e. strongly measurable numerator is a.e. strongly measurable. -/
private theorem h2_factor_mul_num_aestronglyMeasurable {g : ℝ → ℂ} (hg : ContinuousOn g (uIcc a b))
    (hnum : AEStronglyMeasurable (fun t ↦ f (γ t) * deriv γ t) (volume.restrict (Ι a b))) :
    AEStronglyMeasurable (fun t ↦ g t * (f (γ t) * deriv γ t)) (volume.restrict (Ι a b)) :=
  ((hg.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc).mul hnum

/-- On a ball of radius `ε` about the off-curve point, the squared-pole derivative integrand is
bounded by `ε⁻² · ‖numerator‖`. -/
private theorem h2_deriv_bound {ε : ℝ} (hε_pos : 0 < ε) {w' : ℂ}
    (h_dist : ∀ t ∈ uIcc a b, ε ≤ ‖γ t - w'‖) {t : ℝ} (ht : t ∈ uIcc a b) :
    ‖(γ t - w')⁻¹ ^ 2 * (f (γ t) * deriv γ t)‖ ≤ ε⁻¹ ^ 2 * ‖f (γ t) * deriv γ t‖ := by
  rw [norm_mul, norm_pow, norm_inv]
  gcongr
  exact h_dist t ht

/-- **`dixonH2` is holomorphic in the point, off the curve.** If `γ` is continuous on `uIcc a b`
and avoids `w` there, and the Cauchy integrand `f (γ ·) / (γ · - w) · deriv γ` is
interval-integrable, then `fun w ↦ dixonH2 f γ a b w` is complex-differentiable at `w`. -/
theorem differentiableAt_dixonH2 (hγ_cont : ContinuousOn γ (uIcc a b))
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ w)
    (h_cauchy_int : IntervalIntegrable (fun t ↦ f (γ t) / (γ t - w) * deriv γ t) volume a b) :
    DifferentiableAt ℂ (dixonH2 f γ a b) w := by
  obtain ⟨ε, hε_pos, h_dist_lb⟩ := exists_ball_dist_curve_lower_bound hγ_cont hoff
  have avoid : ∀ w' ∈ Metric.ball w ε, ∀ t ∈ uIcc a b, γ t ≠ w' := fun w' hw' t ht ↦
    sub_ne_zero.mp (norm_pos_iff.mp (lt_of_lt_of_le hε_pos (h_dist_lb w' hw' t ht)))
  -- Multiplying the Cauchy integrand by the continuous factor `γ · - w` recovers the numerator.
  have h_factor_cont : ContinuousOn (fun t ↦ γ t - w) (uIcc a b) := hγ_cont.sub continuousOn_const
  have h_num_int : IntervalIntegrable (fun t ↦ f (γ t) * deriv γ t) volume a b := by
    rw [intervalIntegrable_iff]
    refine (intervalIntegrable_iff.mp
      (h_cauchy_int.continuousOn_mul h_factor_cont)).congr_fun (fun t ht ↦ ?_) measurableSet_uIoc
    have hne : γ t - w ≠ 0 := sub_ne_zero.mpr (hoff t (Set.uIoc_subset_uIcc ht))
    field_simp
  have hnum := (intervalIntegrable_iff.mp h_num_int).aestronglyMeasurable
  have h_eq : dixonH2 f γ a b = fun w' ↦ ∫ t in a..b, (γ t - w')⁻¹ * (f (γ t) * deriv γ t) := by
    funext w'
    rw [dixonH2_def]
    exact intervalIntegral.integral_congr fun t _ ↦ by ring
  rw [h_eq]
  refine ((intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (F := fun w' t ↦ (γ t - w')⁻¹ * (f (γ t) * deriv γ t))
    (F' := fun w' t ↦ (γ t - w')⁻¹ ^ 2 * (f (γ t) * deriv γ t))
    (bound := fun t ↦ ε⁻¹ ^ 2 * ‖f (γ t) * deriv γ t‖)
    (Metric.ball_mem_nhds w hε_pos) ?_
    (h_num_int.continuousOn_mul (h2_kernel_continuousOn hγ_cont hoff))
    (h2_factor_mul_num_aestronglyMeasurable ((h2_kernel_continuousOn hγ_cont hoff).pow 2) hnum)
    (Filter.Eventually.of_forall fun t ht w' hw' ↦ h2_deriv_bound hε_pos
      (h_dist_lb w' hw') (Set.uIoc_subset_uIcc ht))
    (h_num_int.norm.const_mul (ε⁻¹ ^ 2))
    (Filter.Eventually.of_forall fun t ht w' hw' ↦ h2_pole_hasDerivAt (f (γ t) * deriv γ t) (γ t)
      w' (sub_ne_zero.mpr (avoid w' hw' t (Set.uIoc_subset_uIcc ht))))).2
    ).differentiableAt
  · filter_upwards [Metric.ball_mem_nhds w hε_pos] with w' hw'
    exact h2_factor_mul_num_aestronglyMeasurable
      (h2_kernel_continuousOn hγ_cont (avoid w' hw')) hnum

end

end TauCeti.Contour
