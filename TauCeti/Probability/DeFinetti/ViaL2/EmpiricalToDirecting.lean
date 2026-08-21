/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.L2.Cesaro.ToCondExp
public import TauCeti.Probability.DeFinetti.DirectingMeasure.Basic

/-!
# Block averages of an indicator converge to the directing measure

`Contractable.tendsto_integral_abs_blockAverage_sub_condExp` identifies the `L¹` limit of the block
averages of an observable with `μ[f ∘ X 0 | tailProcess X]`, along **any** selection that is
injective for all sufficiently large lengths — the selection may move with the length.
`directingMeasure_ae_eq_condExp` identifies `ω ↦ (directingMeasure μ X ω).real B` with the same
conditional expectation when the observable is the indicator `𝟙_B`. Composing the two gives the
statement in the form the `L²` route consumes: the empirical averages of `𝟙_B ∘ X` converge in
`L¹` to the directing measure's evaluation at `B`.

Fixed-start windows (`fixedStart r`) and disjoint windows (`disjointWindow c`) are both instances.
The disjoint ones are what a finite-block factorization needs, and fixed starts cannot supply them:
windows from two distinct fixed starts overlap once the common length exceeds the gap between the
starts. The limit does not depend on the selection, so every one of them converges to the same
directing-measure evaluation.

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

/-- **The block averages of an indicator converge to the directing measure.** For a contractable
process on a standard Borel state space and a measurable set `B`, the block averages of `𝟙_B ∘ X`
along any eventually-injective selection converge in `L¹` to `ω ↦ (directingMeasure μ X ω).real B`.

The selection may move with the length, so this covers the disjoint windows a block factorization
needs as well as fixed-start ones; the limit is the same for every selection. -/
theorem Contractable.tendsto_integral_abs_blockAverage_indicator_sub_directingMeasure
    [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hX : Contractable μ X) (hX_meas : ∀ i, Measurable (X i)) {B : Set α} (hB : MeasurableSet B)
    (k : ∀ n : ℕ, Fin (n + 1) → ℕ) (hk : ∀ᶠ n in atTop, Function.Injective (k n)) :
    Tendsto
      (fun m => ∫ ω, |blockAverage (fun i ω => Set.indicator B (fun _ => (1 : ℝ)) (X i ω)) (k m) ω
        - (directingMeasure μ X ω).real B| ∂μ)
      atTop (𝓝 0) := by
  have hf : Measurable (Set.indicator B (fun _ => (1 : ℝ))) :=
    (measurable_const.indicator hB)
  have hf_bdd : ∃ C, ∀ x, ‖Set.indicator B (fun _ => (1 : ℝ)) x‖ ≤ C :=
    ⟨1, fun x => by simpa only [norm_one] using norm_indicator_le_norm_self (fun _ => (1 : ℝ)) x⟩
  have hlim := hX.tendsto_integral_abs_blockAverage_sub_condExp hX_meas hf hf_bdd k hk
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
