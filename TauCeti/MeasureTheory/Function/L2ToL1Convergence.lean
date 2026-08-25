/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# `L²` convergence gives `L¹` convergence on a finite measure space

Mathlib supplies the exponent comparison `eLpNorm_le_eLpNorm_mul_rpow_measure_univ`, which costs a
fixed finite factor `μ univ ^ (1/p - 1/q)`. Packaging it as a statement about *convergence* — and
in the `∫ ‖·‖` form rather than the `eLpNorm` form — is what consumers usually want, and is not in
Mathlib.

Both de Finetti proof routes need it: the mean-ergodic theorem and the `L²` block estimates each
produce `L²` convergence, while the block factorizations consume `L¹` convergence written as an
integral of an absolute difference.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace TauCeti

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`L²` convergence implies `L¹` convergence on a finite measure space.** If a family `f` tends
to `0` in `L²` along a filter `l`, then `∫ ‖f i‖` tends to `0` along `l`.

The exponent comparison costs the fixed finite factor `μ univ ^ (1/1 - 1/2)`, which the limit
absorbs. Nothing in the argument constrains the index, the filter, or the codomain beyond having a
norm, so all three are arbitrary; the usual difference form is the instance `f i = W i - a`. -/
theorem tendsto_integral_norm_of_tendsto_eLpNorm_two {ι E : Type*} [NormedAddCommGroup E]
    {l : Filter ι} {μ : Measure Ω} [IsFiniteMeasure μ] {f : ι → Ω → E}
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ)
    (h : Tendsto (fun i => eLpNorm (f i) 2 μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ ω, ‖f i ω‖ ∂μ) l (𝓝 0) := by
  have hf_L1 : Tendsto (fun i => eLpNorm (f i) 1 μ) l (𝓝 0) := by
    have hbound := fun i => eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
      one_le_two (hf_meas i)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
      (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall hbound)
    simpa using ENNReal.Tendsto.mul_const h
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ Set.univ)))
  have hreal : Tendsto (fun i => (eLpNorm (f i) 1 μ).toReal) l (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hf_L1
  convert hreal using 1
  ext i
  simpa only [eLpNorm_one_eq_lintegral_enorm] using (integral_norm_eq_lintegral_enorm (hf_meas i))

end MeasureTheory

end TauCeti
