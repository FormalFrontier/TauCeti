/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.CondExp

/-!
# Indicator form of the conditional law of a contractable coordinate

`TauCeti.Probability.Exchangeability.CondExp` shows that for a contractable process `X` the
conditional expectations of `f ∘ X j` and `f ∘ X k` given the future — or given the process tail —
agree, for an arbitrary measurable real observable `f`. This file records the indicator
specializations `Contractable.condExp_indicator_future_eq` and
`Contractable.condExp_indicator_tailProcess_eq`, which are the shape the de Finetti
directing-measure construction and the finite-block factorizations consume.

Adapted from `cameronfreer/exchangeability` (`DeFinetti/ViaMartingale/CondExpConvergence.lean`,
`condexp_convergence` and `extreme_members_equal_on_tail_via_tower`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`).
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Indicator form of `Contractable.condExp_comp_future_ae_eq`, the shape the finite-block
factorizations use. -/
theorem Contractable.condExp_indicator_future_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) {r j k : ℕ}
    (hj : j < r) (hk : k < r) {B : Set α} (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ X j | tailFamily X r]
      =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ X k | tailFamily X r] :=
  hX.condExp_comp_future_ae_eq hX_meas hj hk (measurable_const.indicator hB)

/-- Indicator form of `Contractable.condExp_comp_tailProcess_ae_eq`, the shape the directing-measure
construction uses. -/
theorem Contractable.condExp_indicator_tailProcess_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) {j k : ℕ}
    {B : Set α} (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ X j | tailProcess X]
      =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ X k | tailProcess X] :=
  hX.condExp_comp_tailProcess_ae_eq hX_meas (measurable_const.indicator hB)

end Probability

end TauCeti
