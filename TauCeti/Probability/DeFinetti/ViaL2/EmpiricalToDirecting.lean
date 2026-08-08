/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.L2.Cesaro.ToCondExp
public import TauCeti.Probability.DeFinetti.DirectingMeasure.Basic

/-!
# Cesàro averages of an indicator converge to the directing measure

`Contractable.tendsto_integral_abs_blockAverage_sub_condExp` identifies the `L¹` limit of the
fixed-start Cesàro windows of an observable with `μ[f ∘ X 0 | tailProcess X]`, and
`directingMeasure_ae_eq_condExp` identifies `ω ↦ (directingMeasure μ X ω).real B` with the same
conditional expectation when the observable is the indicator `𝟙_B`. Composing the two gives the
statement in the form the `L²` route consumes: the empirical averages of `𝟙_B ∘ X` converge in
`L¹` to the directing measure's evaluation at `B`.

The point is that no directing measure is *constructed* here. `directingMeasure` is Mathlib's
`condDistrib` conditioned on `tailProcess X`, which the martingale route also uses but does not
own; this file only observes that the `L²` averaging limit lands on it.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **The Cesàro averages of an indicator converge to the directing measure.** For a contractable
process on a standard Borel state space and a measurable set `B`, the fixed-start Cesàro windows of
`𝟙_B ∘ X` converge in `L¹` to `ω ↦ (directingMeasure μ X ω).real B`. -/
theorem Contractable.tendsto_integral_abs_blockAverage_indicator_sub_directingMeasure
    [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hX : Contractable μ X) (hX_meas : ∀ i, Measurable (X i)) {B : Set α} (hB : MeasurableSet B)
    (r : ℕ) :
    Tendsto
      (fun m => ∫ ω, |blockAverage (fun i ω => Set.indicator B (fun _ => (1 : ℝ)) (X i ω))
          (fun j : Fin (m + 1) => r + j) ω
        - (directingMeasure μ X ω).real B| ∂μ)
      atTop (𝓝 0) := by
  have hf : Measurable (Set.indicator B (fun _ => (1 : ℝ))) :=
    (measurable_const.indicator hB)
  have hf_bdd : ∃ C, ∀ x, ‖Set.indicator B (fun _ => (1 : ℝ)) x‖ ≤ C :=
    ⟨1, fun x => by simpa only [norm_one] using norm_indicator_le_norm_self (fun _ => (1 : ℝ)) x⟩
  -- This route still reads a fixed start; the moving-selection form is available upstream and is
  -- generalised here separately.
  have hlim := hX.tendsto_integral_abs_blockAverage_sub_condExp hX_meas hf hf_bdd
    (fun _ j => r + (j : ℕ))
    (Eventually.of_forall fun _ => (add_right_injective r).comp Fin.val_injective)
  -- Normalise the composition wrapper so the rewrite matches without relying on defeq.
  have hdir : (fun ω => (directingMeasure μ X ω).real B)
      =ᵐ[μ] μ[fun ω => Set.indicator B (fun _ => (1 : ℝ)) (X 0 ω) | tailProcess X] := by
    simpa only [Function.comp_def] using directingMeasure_ae_eq_condExp (μ := μ) (X := X)
      (tailProcess_le_ambient 0 fun k _ => hX_meas k) (hX_meas 0) hB
  refine hlim.congr fun m => integral_congr_ae ?_
  filter_upwards [hdir] with ω hω
  rw [hω]

end Probability

end TauCeti
