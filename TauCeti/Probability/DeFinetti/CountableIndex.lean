/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.DeFinetti.Theorem
public import TauCeti.Probability.Exchangeability.Family
import Mathlib.Logic.Denumerable

/-!
# De Finetti's theorem for countable index types

De Finetti's theorem is independent of the particular enumeration of a countably infinite index
type. This file transports the sequence theorem along an equivalence with `ℕ`.

## Main results

* `conditionallyIIDFamily_of_exchangeableFamily_of_equiv_nat` gives the transport along an
  explicit equivalence `ι ≃ ℕ`.
* `conditionallyIIDFamily_of_exchangeableFamily` chooses such an equivalence from `[Countable ι]`
  and `[Infinite ι]`.

This implements the Layer 8 target “de Finetti for other countable index types” in
`TauCetiRoadmap/Exchangeability/README.md`. The proof reuses the sequence theorem
`conditionallyIID_of_exchangeable`; no new measure-theoretic argument is required.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **De Finetti's theorem transported along an explicit enumeration.** Under a finite measure,
an exchangeable family with measurable coordinates whose index type is equivalent to `ℕ` is
conditionally i.i.d. -/
theorem conditionallyIIDFamily_of_exchangeableFamily_of_equiv_nat
    [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ι → Ω → α} (hX : ExchangeableFamily μ X) (e : ι ≃ ℕ)
    (hX_meas : ∀ i, Measurable (X i)) :
    ConditionallyIIDFamily μ X := by
  let Y : ℕ → Ω → α := fun n => X (e.symm n)
  have hY_family : ExchangeableFamily μ Y := by
    simpa only [Y] using hX.comp_injective (f := e.symm) e.symm.injective
  have hY : Exchangeable μ Y := hY_family.exchangeable
  obtain ⟨ν, hν⟩ :=
    (conditionallyIID_of_exchangeable hY fun n => hX_meas (e.symm n)).exists_directing
  refine ConditionallyIIDFamily.of_directing (ν := ν) ?_
  simpa only [Y, Equiv.symm_apply_apply] using
    hν.conditionallyIIDWithFamily.comp_injective (f := e) e.injective

/-- **De Finetti's theorem for countably infinite index types.** Under a finite measure, every
exchangeable family with measurable coordinates indexed by a countably infinite type, with values
in a nonempty standard Borel space, is conditionally i.i.d. -/
theorem conditionallyIIDFamily_of_exchangeableFamily
    [Countable ι] [Infinite ι] [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ι → Ω → α}
    (hX : ExchangeableFamily μ X) (hX_meas : ∀ i, Measurable (X i)) :
    ConditionallyIIDFamily μ X :=
  conditionallyIIDFamily_of_exchangeableFamily_of_equiv_nat
    hX (Classical.choice (inferInstance : Nonempty (ι ≃ ℕ))) hX_meas

end Probability

end TauCeti
