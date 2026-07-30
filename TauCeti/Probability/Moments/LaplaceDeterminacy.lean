/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Moments.Determinacy
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# A finite measure on `ℝ≥0` is determined by its Laplace transform

## Main results

* `TauCeti.Measure.ext_of_forall_integral_exp_neg_mul_eq`

## Implementation

The substitution `y = e^{-x}` converts the Laplace transform into a moment sequence: at a natural
argument `n`, `∫ e^{-n x} dμ = ∫ yⁿ d(μ.map (x ↦ e^{-x}))`. So matching Laplace transforms give
pushforwards with matching moments, and the pushforwards are moment-determinate because they are
carried by `(0, 1]` — bounded support makes the exponential-moment hypothesis of
`Measure.ext_of_forall_integral_pow_eq_of_exists_integrable_exp` automatic. Finally `x ↦ e^{-x}` is
injective and measurable between standard Borel spaces, hence a measurable embedding by
Lusin–Souslin, and `MeasurableEmbedding.map_injective` recovers `μ = ν` from the equal pushforwards.

Only the transform's values at *natural* arguments are used, so the theorem holds a fortiori under
the stated hypothesis at all nonnegative reals.

This is the uniqueness half of the Bernstein milestone in
`TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B; the existence half is
`TauCeti.exists_isFiniteMeasure_integral_exp_neg_mul_eq_of_isCompletelyMonotone`. The statement
mentions no complete monotonicity and is about two arbitrary finite measures, which is why it lives
beside the other determinacy results rather than under `Analysis/CompletelyMonotone/`.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal

namespace TauCeti

/-- The substitution `x ↦ e^{-x}`, which turns Laplace transforms into moments. -/
private def expNeg (x : ℝ≥0) : ℝ := Real.exp (-(x : ℝ))

@[simp]
private theorem expNeg_apply (x : ℝ≥0) : expNeg x = Real.exp (-(x : ℝ)) := rfl

private theorem measurable_expNeg : Measurable expNeg :=
  Real.continuous_exp.comp (continuous_subtype_val.neg) |>.measurable

private theorem injective_expNeg : Function.Injective expNeg := by
  intro x y hxy
  exact NNReal.coe_injective (neg_injective (Real.exp_injective hxy))

private theorem measurableEmbedding_expNeg : MeasurableEmbedding expNeg :=
  measurable_expNeg.measurableEmbedding injective_expNeg

private theorem abs_expNeg_le_one (x : ℝ≥0) : |expNeg x| ≤ 1 := by
  rw [expNeg_apply, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  simp

/-- The pushforward under `x ↦ e^{-x}` has every exponential moment, because it is carried by the
bounded set `(0, 1]`. -/
private theorem exists_integrable_exp_map_expNeg (μ : Measure ℝ≥0) [IsFiniteMeasure μ] :
    ∃ a : ℝ, 0 < a ∧ Integrable (fun y => Real.exp (a * |y|)) (μ.map expNeg) := by
  refine ⟨1, one_pos, ?_⟩
  have hmeas : AEStronglyMeasurable (fun y : ℝ => Real.exp (1 * |y|)) (μ.map expNeg) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).aestronglyMeasurable
  rw [integrable_map_measure hmeas measurable_expNeg.aemeasurable]
  refine Integrable.mono' (integrable_const (Real.exp 1))
    ((Real.continuous_exp.comp
      (continuous_const.mul (continuous_abs.comp
        (Real.continuous_exp.comp continuous_subtype_val.neg)))).aestronglyMeasurable) ?_
  filter_upwards with x
  rw [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
  exact Real.exp_le_exp.mpr (abs_expNeg_le_one x)

/-- **A finite measure on `ℝ≥0` is determined by its Laplace transform.**

Substituting `y = e^{-x}` turns the Laplace transform at natural arguments into the moment sequence
of the pushforward, which is carried by `(0, 1]` and so is moment-determinate. -/
theorem Measure.ext_of_forall_integral_exp_neg_mul_eq {μ ν : Measure ℝ≥0}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t : ℝ, 0 ≤ t →
      ∫ x, Real.exp (-t * (x : ℝ)) ∂μ = ∫ x, Real.exp (-t * (x : ℝ)) ∂ν) :
    μ = ν := by
  refine measurableEmbedding_expNeg.map_injective ?_
  refine Measure.ext_of_forall_integral_pow_eq_of_exists_integrable_exp
    (exists_integrable_exp_map_expNeg μ) (exists_integrable_exp_map_expNeg ν) fun n => ?_
  have hpow : ∀ (ρ : Measure ℝ≥0), ∫ y, y ^ n ∂(ρ.map expNeg)
      = ∫ x, Real.exp (-(n : ℝ) * (x : ℝ)) ∂ρ := by
    intro ρ
    have hpowmeas : AEStronglyMeasurable (fun y : ℝ => y ^ n) (ρ.map expNeg) :=
      (continuous_pow n).aestronglyMeasurable
    rw [integral_map measurable_expNeg.aemeasurable hpowmeas]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change expNeg x ^ n = Real.exp (-(n : ℝ) * (x : ℝ))
    rw [expNeg_apply, ← Real.exp_nat_mul]
    ring_nf
  rw [hpow, hpow]
  exact h (n : ℝ) (Nat.cast_nonneg n)

end TauCeti
