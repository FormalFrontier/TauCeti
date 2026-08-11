/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.Dixon.Def
import TauCeti.Analysis.Calculus.DSlope.Integral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Holomorphy of Dixon's `h₁` on the region

Dixon's `h₁` integral `dixonH1 f γ a b w = ∫ t in a..b, dslope f w (γ t) * deriv γ t` is
holomorphic in the point `w`, throughout the open region `U` where `f` is holomorphic and the
curve `γ` lives. This is the removable-singularity half of the analyticity of Dixon's glued
function: because `dslope f · (γ t)` extends `f`'s divided difference across the diagonal, the
integrand stays holomorphic even for `w` on the curve.

## Main results

* `TauCeti.Contour.differentiableOn_dixonH1` — `fun w ↦ dixonH1 f γ a b w` is complex-differentiable
  on `U`, for `f` differentiable on the open set `U` and `γ` continuous on `uIcc a b` with
  interval-integrable derivative and image in `U`.

This feeds the `homologyCauchyTheorem` roadmap target
(`TauCetiRoadmap/ContourIntegration/Suggested.lean`, Layer 3, Dixon's argument).

## Provenance

Adapted from `dixonH1_differentiableOn` / `dixonH1_differentiableOn_of_regular_open_full` in
`DixonDiff.lean` of the AINTLIB `LeanModularForms` development, restated for a raw `γ : ℝ → ℂ` on an
oriented interval with the curve's derivative required only to be interval-integrable. See
J. D. Dixon, *A brief proof of Cauchy's integral theorem* (1971).
-/

public section

open Complex MeasureTheory Set

open scoped Real Interval Topology

namespace TauCeti.Contour

section

variable {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ} {w₀ : ℂ}

/-- `dslope` is symmetric in its two point arguments. -/
private theorem dslope_comm (g : ℂ → ℂ) (x y : ℂ) : dslope g x y = dslope g y x := by
  by_cases h : y = x
  · rw [h]
  · rw [dslope_of_ne g h, dslope_of_ne g (Ne.symm h), slope_comm]

/-- The `w`-derivative of `w' ↦ dslope f w' c` at an interior point `w` is `deriv (dslope f c) w`,
using symmetry of `dslope` to move the varying argument into first position. -/
private theorem dslope_first_arg_hasDerivAt (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {c w : ℂ}
    (hc : c ∈ U) (hw : w ∈ U) :
    HasDerivAt (fun w' ↦ dslope f w' c) (deriv (dslope f c) w) w :=
  (((Complex.differentiableOn_dslope (hU.mem_nhds hc)).mpr hf w hw).differentiableAt
    (hU.mem_nhds hw)).hasDerivAt.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ ↦ dslope_comm f _ _)

/-- For `w ∈ U`, the fixed-point section `t ↦ dslope f w (γ t)` is continuous on `uIcc a b`. -/
private theorem dslope_comp_curve_continuousOn (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) {w : ℂ} (hw : w ∈ U) :
    ContinuousOn (fun t ↦ dslope f w (γ t)) (uIcc a b) := by
  simp_rw [dslope_comm f w]
  exact (continuousOn_dslope_first_arg hU hf hw).comp hγ_cont hγU

/-- A factor continuous on `uIcc a b` times `deriv γ` is a.e. strongly measurable on `Ι a b`. -/
private theorem factor_mul_deriv_aestronglyMeasurable {g : ℝ → ℂ} (hg : ContinuousOn g (uIcc a b)) :
    AEStronglyMeasurable (fun t ↦ g t * deriv γ t) (volume.restrict (Ι a b)) :=
  ((hg.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc).mul
    (stronglyMeasurable_deriv γ).aestronglyMeasurable

/-- A sequence of nonzero complex shifts of `w₀`, staying in `U` and tending to `0`; used to
realise `deriv (dslope f c) w₀` as an a.e.-limit of difference quotients. -/
private theorem exists_seq_ne_add_mem_tendsto (hU : IsOpen U) (hw₀ : w₀ ∈ U) :
    ∃ s : ℕ → ℂ, (∀ n, s n ≠ 0) ∧ (∀ n, w₀ + s n ∈ U) ∧
      Filter.Tendsto s Filter.atTop (𝓝 0) := by
  obtain ⟨ρ, hρ_pos, hρ_sub⟩ := Metric.isOpen_iff.mp hU w₀ hw₀
  refine ⟨fun n ↦ ((ρ / 2 / ((n : ℝ) + 1) : ℝ) : ℂ), fun n ↦ ?_, fun n ↦ ?_, ?_⟩
  · simp only [ne_eq, Complex.ofReal_eq_zero]; positivity
  · refine hρ_sub ?_
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    linarith [div_le_self (a := ρ / 2) (by linarith)
      (by linarith [Nat.cast_nonneg (α := ℝ) n] : (1 : ℝ) ≤ (n : ℝ) + 1)]
  · have h_real : Filter.Tendsto (fun n : ℕ ↦ ρ / 2 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).inv_tendsto_atTop).const_mul
          (ρ / 2)
    have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h_real
    rwa [Complex.ofReal_zero] at h

/-- Each difference quotient `t ↦ (dslope f (γ t) (w₀ + s) − dslope f (γ t) w₀) / s · deriv γ t`
is a.e. strongly measurable, being a continuous factor times `deriv γ`. -/
private theorem dslope_diffquot_aestronglyMeasurable (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hw₀ : w₀ ∈ U) {s : ℂ}
    (hs : w₀ + s ∈ U) :
    AEStronglyMeasurable
      (fun t ↦ (dslope f (γ t) (w₀ + s) - dslope f (γ t) w₀) / s * deriv γ t)
      (volume.restrict (Ι a b)) := by
  refine factor_mul_deriv_aestronglyMeasurable (ContinuousOn.div_const (ContinuousOn.sub ?_ ?_) _)
  · exact (continuousOn_dslope_first_arg hU hf hs).comp hγ_cont hγU
  · exact (continuousOn_dslope_first_arg hU hf hw₀).comp hγ_cont hγU

/-- The `F'`-integrand `t ↦ deriv (dslope f (γ t)) w₀ · deriv γ t` is a.e. strongly measurable:
`deriv (dslope f (γ t)) w₀` is the a.e.-limit of the measurable difference quotients above, since
`dslope f (γ t)` is differentiable at `w₀ ∈ U`. -/
private theorem dslope_deriv_mul_deriv_aestronglyMeasurable (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hw₀ : w₀ ∈ U) :
    AEStronglyMeasurable (fun t ↦ deriv (dslope f (γ t)) w₀ * deriv γ t)
      (volume.restrict (Ι a b)) := by
  obtain ⟨s, hs_ne, hs_mem, hs_tendsto⟩ := exists_seq_ne_add_mem_tendsto hU hw₀
  refine aestronglyMeasurable_of_tendsto_ae Filter.atTop
    (fun n ↦ dslope_diffquot_aestronglyMeasurable hU hf hγ_cont hγU hw₀ (hs_mem n)) ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  have ht_uIcc : t ∈ uIcc a b := Set.uIoc_subset_uIcc ht
  have h_diff : DifferentiableAt ℂ (dslope f (γ t)) w₀ :=
    ((Complex.differentiableOn_dslope (hU.mem_nhds (hγU t ht_uIcc))).mpr hf w₀ hw₀).differentiableAt
      (hU.mem_nhds hw₀)
  have hy : Filter.Tendsto (fun n ↦ w₀ + s n) Filter.atTop (𝓝[≠] w₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using hs_tendsto.const_add w₀,
      Filter.Eventually.of_forall fun n h ↦ hs_ne n (add_left_cancel (h.trans (add_zero w₀).symm))⟩
  have h_q_eq : ∀ n, (dslope f (γ t) (w₀ + s n) - dslope f (γ t) w₀) / s n * deriv γ t =
      slope (dslope f (γ t)) w₀ (w₀ + s n) * deriv γ t := fun n ↦ by
    have hsub : w₀ + s n - w₀ = s n := by ring
    rw [slope_def_field, hsub]
  simp_rw [h_q_eq]
  exact (h_diff.hasDerivAt.tendsto_slope.comp hy).mul_const _

/-- Near `w₀`, the derivative integrand is dominated by `C · ‖deriv γ t‖`, where `C` bounds
`deriv (dslope f c)` (Cauchy's estimate) uniformly for `c` on the curve. -/
private theorem dslope_deriv_product_norm_bound {C δ : ℝ}
    (h_dslope_bd : ∀ c ∈ γ '' uIcc a b, ∀ w ∈ Metric.ball w₀ δ, ‖deriv (dslope f c) w‖ ≤ C)
    {ε : ℝ} (hball : Metric.ball w₀ ε ⊆ Metric.ball w₀ δ) :
    ∀ᵐ t, t ∈ Ι a b → ∀ w ∈ Metric.ball w₀ ε,
      ‖deriv (dslope f (γ t)) w * deriv γ t‖ ≤ C * ‖deriv γ t‖ := by
  refine Filter.Eventually.of_forall fun t ht w hw ↦ ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (h_dslope_bd (γ t) ⟨t, Set.uIoc_subset_uIcc ht, rfl⟩ w (hball hw)) (norm_nonneg _)

/-- Pointwise differentiability of `dixonH1`'s integral form at `w₀ ∈ U`, via the parametric
Leibniz rule with `F' w t = deriv (dslope f (γ t)) w · deriv γ t`, dominated near `w₀` by Cauchy's
estimate on a ball avoiding the boundary of `U`. -/
private theorem differentiableAt_dixonH1_integral (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) (hw₀ : w₀ ∈ U) :
    DifferentiableAt ℂ (fun w ↦ ∫ t in a..b, dslope f w (γ t) * deriv γ t) w₀ := by
  have hK_compact : IsCompact (γ '' uIcc a b) := isCompact_uIcc.image_of_continuousOn hγ_cont
  have hK_sub : γ '' uIcc a b ⊆ U := fun _ ⟨t, ht, hz⟩ ↦ hz ▸ hγU t ht
  obtain ⟨C, hC_pos, δ, hδ_pos, h_dslope_bd⟩ :=
    deriv_dslope_bounded_on_compact hU hf hK_compact hK_sub hw₀
  obtain ⟨εU, hεU_pos, hεU_sub⟩ := Metric.isOpen_iff.mp hU w₀ hw₀
  have hε_pos : 0 < min δ εU := lt_min hδ_pos hεU_pos
  have hball_U : Metric.ball w₀ (min δ εU) ⊆ U :=
    (Metric.ball_subset_ball (min_le_right δ εU)).trans hεU_sub
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (F := fun w t ↦ dslope f w (γ t) * deriv γ t)
    (F' := fun w t ↦ deriv (dslope f (γ t)) w * deriv γ t)
    (bound := fun t ↦ C * ‖deriv γ t‖) (Metric.ball_mem_nhds w₀ hε_pos) ?_
    (hderiv_int.continuousOn_mul (dslope_comp_curve_continuousOn hU hf hγ_cont hγU hw₀))
    (dslope_deriv_mul_deriv_aestronglyMeasurable hU hf hγ_cont hγU hw₀)
    (dslope_deriv_product_norm_bound h_dslope_bd (Metric.ball_subset_ball (min_le_left δ εU)))
    (hderiv_int.norm.const_mul C) ?_).2.differentiableAt
  · filter_upwards [Metric.ball_mem_nhds w₀ hε_pos] with w hw
    exact factor_mul_deriv_aestronglyMeasurable
      (dslope_comp_curve_continuousOn hU hf hγ_cont hγU (hball_U hw))
  · refine Filter.Eventually.of_forall fun t ht w hw ↦ ?_
    exact (dslope_first_arg_hasDerivAt hU hf (hγU t (Set.uIoc_subset_uIcc ht))
      (hball_U hw)).mul_const (deriv γ t)

/-- **`dixonH1` is holomorphic on the region.** For `f` differentiable on the open set `U`, and `γ`
continuous on `uIcc a b` with `deriv γ` interval-integrable and image in `U`, the map
`fun w ↦ dixonH1 f γ a b w` is complex-differentiable on `U`. -/
theorem differentiableOn_dixonH1 (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) :
    DifferentiableOn ℂ (dixonH1 f γ a b) U := by
  have h_eq : dixonH1 f γ a b = fun w ↦ ∫ t in a..b, dslope f w (γ t) * deriv γ t :=
    funext fun w ↦ dixonH1_def f γ a b w
  rw [h_eq]
  exact fun w₀ hw₀ ↦ (differentiableAt_dixonH1_integral hU hf hγ_cont hγU hderiv_int
    hw₀).differentiableWithinAt

end

end TauCeti.Contour
