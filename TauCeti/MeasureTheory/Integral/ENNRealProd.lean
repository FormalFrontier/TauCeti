/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integrating finite products of `ℝ≥0∞`-valued functions

Two facts about a finite product `∏ i, f i ω` of `ℝ≥0∞`-valued functions, relating its real form
to its `ℝ≥0∞` form.

## Main results

* `integrable_prod_toReal` — a finite product of measurable `[0,1]`-valued functions is integrable
  against a finite measure, since the product is itself `[0,1]`-valued.
* `ofReal_integral_prod_toReal_eq_lintegral_prod` — the real integral of the product of the real
  forms is the lower integral of the product, provided no factor is infinite.

Both are stated for an arbitrary family `f : Fin r → Ω → ℝ≥0∞`. The motivating instance is a
product of measure evaluations `f i ω = κ ω (B i)` for a measurable family of probability
measures `κ`, where the `[0,1]` bound is `prob_le_one` and finiteness is `measure_ne_top`; nothing
in the proofs uses that the factors come from measures, so neither statement mentions one.
-/

public section

noncomputable section

open MeasureTheory Finset

open scoped ENNReal

namespace TauCeti

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **A finite product of `[0,1]`-valued measurable functions is integrable** against a finite
measure: the product is measurable, nonnegative, and bounded by `1`, so it is dominated by a
constant. -/
theorem integrable_prod_toReal {ν : Measure Ω} [IsFiniteMeasure ν] {r : ℕ} {f : Fin r → Ω → ℝ≥0∞}
    (hf_meas : ∀ i, Measurable (f i)) (hf_le : ∀ i ω, f i ω ≤ 1) :
    Integrable (fun ω => ∏ i, (f i ω).toReal) ν := by
  have hg_meas : Measurable fun ω => ∏ i, (f i ω).toReal :=
    Finset.measurable_prod _ fun i _ => (hf_meas i).ennreal_toReal
  refine (integrable_const (1 : ℝ)).mono' hg_meas.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_of_nonneg (Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg)]
  exact Finset.prod_le_one (fun i _ => ENNReal.toReal_nonneg) fun i _ =>
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact hf_le i ω)

/-- **The real integral of a finite product is its `ℝ≥0∞` integral**, factor by factor: each factor
is finite, so `ENNReal.ofReal_toReal` recovers it from its real form. -/
theorem ofReal_integral_prod_toReal_eq_lintegral_prod {ν : Measure Ω} {r : ℕ}
    {f : Fin r → Ω → ℝ≥0∞} (hf_ne_top : ∀ i ω, f i ω ≠ ∞)
    (h_int : Integrable (fun ω => ∏ i, (f i ω).toReal) ν) :
    ENNReal.ofReal (∫ ω, ∏ i, (f i ω).toReal ∂ν) = ∫⁻ ω, ∏ i, f i ω ∂ν := by
  rw [ofReal_integral_eq_lintegral_ofReal h_int
    (ae_of_all _ fun ω => Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg)]
  refine lintegral_congr fun ω => ?_
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ => ENNReal.toReal_nonneg]
  exact Finset.prod_congr rfl fun i _ => ENNReal.ofReal_toReal (hf_ne_top i ω)

end MeasureTheory

end TauCeti

end

end
