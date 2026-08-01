/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
-- Non-public: the mixture-side bridges `MixedIIDWith.exchangeable` and `MixedIIDWith.contractable`
-- are used only inside the proofs below.
import TauCeti.Probability.Exchangeability.MixedIID.Implications

/-!
# Basic implications from conditional i.i.d.-ness

The symmetry consequences of the conditional predicate: a conditionally i.i.d. sequence is
exchangeable, and it is contractable.

The witness-level forms compose the projection `mixedIIDWith_of_conditionallyIIDWith` with the
corresponding `MixedIIDWith` implication, so the directing measure is carried through unchanged; the
existential forms destruct `exists_directing` and apply them. This is the same layering as the
mixture side, where `MixedIIDWith.exchangeable` does the work and `MixedIID.exchangeable` destructs
the existential.

The file is therefore the conditional counterpart of
`TauCeti.Probability.Exchangeability.MixedIID.Implications`, and sits one layer above
`ConditionallyIID.Basic` for the same reason that file sits above `MixedIID.Basic`: the projection
belongs with the predicate, the implications out of it do not.

## Main results

* `ConditionallyIIDWith.exchangeable`, `ConditionallyIIDWith.contractable` — at a named directing
  measure.
* `ConditionallyIID.exchangeable`, `ConditionallyIID.contractable` — their existential corollaries.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- A sequence with a named directing measure is exchangeable. -/
theorem ConditionallyIIDWith.exchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : ConditionallyIIDWith μ X ν) : Exchangeable μ X :=
  (mixedIIDWith_of_conditionallyIIDWith h).exchangeable

/-- A conditionally i.i.d. sequence is exchangeable. -/
theorem ConditionallyIID.exchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : ConditionallyIID μ X) : Exchangeable μ X :=
  let ⟨_, hν⟩ := h.exists_directing
  hν.exchangeable

/-- A sequence with a named directing measure is contractable. -/
theorem ConditionallyIIDWith.contractable {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : ConditionallyIIDWith μ X ν) : Contractable μ X :=
  (mixedIIDWith_of_conditionallyIIDWith h).contractable

/-- A conditionally i.i.d. sequence is contractable. -/
theorem ConditionallyIID.contractable {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : ConditionallyIID μ X) : Contractable μ X :=
  let ⟨_, hν⟩ := h.exists_directing
  hν.contractable


end Probability

end TauCeti
