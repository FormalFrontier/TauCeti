/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# `L¹` convergence: from `∫ ‖f i - g‖` to `eLpNorm _ 1`

`L¹` convergence is often produced in the Bochner form `∫ ω, ‖f i ω - g ω‖ ∂μ → 0` but consumed
in the seminorm form `eLpNorm (f i - g) 1 μ → 0` (for instance by
`MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm`).

* `tendsto_eLpNorm_one_of_tendsto_integral_norm_sub` converts the former into the latter.

The conversion is `MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm`, whose home is
`Mathlib.MeasureTheory.Integral.Bochner.Basic`, plus continuity of `ENNReal.ofReal` at `0`.
-/

public section

noncomputable section

open MeasureTheory Filter

open scoped ENNReal Topology

namespace TauCeti

namespace MeasureTheory

/-- **`L¹` convergence in Bochner form is `eLpNorm _ 1` convergence.** If `∫ ‖f i - g‖ → 0` along
`l`, with every `f i` and `g` integrable, then `eLpNorm (f i - g) 1 μ → 0`. -/
theorem tendsto_eLpNorm_one_of_tendsto_integral_norm_sub {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} {l : Filter ι} {f : ι → Ω → E} {g : Ω → E}
    (hf : ∀ i, Integrable (f i) μ) (hg : Integrable g μ)
    (h : Tendsto (fun i => ∫ ω, ‖f i ω - g ω‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (f i - g) 1 μ) l (𝓝 0) := by
  have heq : ∀ i, eLpNorm (f i - g) 1 μ = ENNReal.ofReal (∫ ω, ‖f i ω - g ω‖ ∂μ) := by
    intro i
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hf i).sub hg)]
    simp [Pi.sub_apply]
  simp_rw [heq]
  simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp h

end MeasureTheory

end TauCeti
