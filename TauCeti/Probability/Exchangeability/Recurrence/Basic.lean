/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Stationary
public import TauCeti.Probability.Recurrent

/-!
# Exchangeable and contractable processes are recurrent

A contractable process has a shift-invariant path law, so on a countable state space the
Poincaré recurrence theorem of `TauCeti.Probability.Recurrent` applies to it. Exchangeable
processes are contractable, so they are recurrent too.

## Main results

* `TauCeti.Probability.Contractable.recurrent` and
  `TauCeti.Probability.Exchangeable.recurrent` — contractable and exchangeable processes on a
  countable state space are recurrent.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.
* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 8, "Markov exchangeability".
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [Countable α]
  [MeasurableSingletonClass α] {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}

/-- **A contractable process on a countable state space is recurrent.** -/
theorem Contractable.recurrent (hX : Contractable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    Recurrent μ X :=
  recurrent_of_measurePreserving_shift hX_meas (hX.measurePreserving_shift hX_meas)

/-- **An exchangeable process on a countable state space is recurrent.** Together with
`Exchangeable.markovExchangeable` this says that the Diaconis–Freedman hypotheses hold for every
exchangeable process on a countable state space. -/
theorem Exchangeable.recurrent (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    Recurrent μ X :=
  (hX.contractable hX_meas).recurrent hX_meas

end Probability

end TauCeti

end

end
