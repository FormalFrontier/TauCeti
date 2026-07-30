/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
-- Non-public: the mixture-side bridges `MixedIID.exchangeable` and `MixedIID.contractable` are
-- used only inside the proofs below.
import TauCeti.Probability.Exchangeability.MixedIID.Implications

/-!
# Basic implications from conditional i.i.d.-ness

The symmetry consequences of the conditional predicate: a conditionally i.i.d. sequence is
exchangeable, and it is contractable.

Both factor through `mixedIID_of_conditionallyIID`, so this file is the conditional counterpart of
`TauCeti.Probability.Exchangeability.MixedIID.Implications`, and sits one layer above it for the
same reason that file sits above `MixedIID.Basic`: the projection belongs with the predicate, the
implications out of it do not.

## Main results

* `ConditionallyIID.exchangeable`
* `ConditionallyIID.contractable`
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- A conditionally i.i.d. sequence is exchangeable. -/
theorem ConditionallyIID.exchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : ConditionallyIID μ X) : Exchangeable μ X :=
  (mixedIID_of_conditionallyIID h).exchangeable

/-- A conditionally i.i.d. sequence is contractable. -/
theorem ConditionallyIID.contractable {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : ConditionallyIID μ X) : Contractable μ X :=
  (mixedIID_of_conditionallyIID h).contractable


end Probability

end TauCeti
