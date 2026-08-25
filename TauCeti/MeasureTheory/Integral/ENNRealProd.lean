/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrating finite products of `ℝ≥0∞`-valued functions

Two facts about a finite product `∏ i, f i ω` of `ℝ≥0∞`-valued functions, relating its real form
to its `ℝ≥0∞` form.

## Main results

* `integrable_prod_toReal` — a finite product of measurable `[0,1]`-valued functions is integrable
  against a finite measure, since the product is itself `[0,1]`-valued.
* `ofReal_integral_prod_toReal_eq_lintegral_prod` — the real integral of the product of the real
  forms is the lower integral of the product, provided the product is a.e. finite.

Both are stated for an arbitrary family `f : ι → Ω → ℝ≥0∞` indexed over a `Finset`, with
almost-everywhere hypotheses, since that is all integration sees. The motivating instance is a
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

/-- **A finite product of `[0,1]`-valued functions is integrable** against a finite measure: the
product is a.e. nonnegative and a.e. bounded by `1`, so it is dominated by a constant. -/
theorem integrable_prod_toReal {ι : Type*} {ν : Measure Ω} [IsFiniteMeasure ν] {s : Finset ι}
    {f : ι → Ω → ℝ≥0∞} (hf_meas : ∀ i ∈ s, AEMeasurable (f i) ν)
    (hf_le : ∀ i ∈ s, ∀ᵐ ω ∂ν, f i ω ≤ 1) :
    Integrable (fun ω => ∏ i ∈ s, (f i ω).toReal) ν := by
  have hg_meas : AEMeasurable (fun ω => ∏ i ∈ s, (f i ω).toReal) ν :=
    (Finset.aemeasurable_prod s fun i hi => (hf_meas i hi).ennreal_toReal).congr
      (ae_of_all _ fun ω => Finset.prod_apply ω s _)
  refine (integrable_const (1 : ℝ)).mono' hg_meas.aestronglyMeasurable ?_
  filter_upwards [(Filter.eventually_all_finset s).2 hf_le] with ω hω
  rw [Real.norm_of_nonneg (Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg)]
  exact Finset.prod_le_one (fun i _ => ENNReal.toReal_nonneg) fun i hi =>
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact hω i hi)

/-- **The real integral of a finite product is its `ℝ≥0∞` integral.** Only the *product* need be
a.e. finite — an infinite factor annihilated by a zero one is fine — since `ENNReal.toReal` is
multiplicative and `ENNReal.ofReal_toReal` is then applied to the product as a whole. -/
theorem ofReal_integral_prod_toReal_eq_lintegral_prod {ι : Type*} {ν : Measure Ω} {s : Finset ι}
    {f : ι → Ω → ℝ≥0∞} (hf_ne_top : ∀ᵐ ω ∂ν, (∏ i ∈ s, f i ω) ≠ ∞)
    (h_int : Integrable (fun ω => ∏ i ∈ s, (f i ω).toReal) ν) :
    ENNReal.ofReal (∫ ω, ∏ i ∈ s, (f i ω).toReal ∂ν) = ∫⁻ ω, ∏ i ∈ s, f i ω ∂ν := by
  rw [ofReal_integral_eq_lintegral_ofReal h_int
    (ae_of_all _ fun ω => Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg)]
  refine lintegral_congr_ae ?_
  filter_upwards [hf_ne_top] with ω hω
  rw [← ENNReal.toReal_prod, ENNReal.ofReal_toReal hω]

end MeasureTheory

end TauCeti

end

end
