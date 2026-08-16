/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.DeFinetti.ViaL2.ConditionallyIID
import TauCeti.Probability.Exchangeability.ConditionallyIID.Implications
import TauCeti.Probability.Exchangeability.Contractability

/-!
# De Finetti's theorem via `L²` averaging

This file is the endpoint of the martingale-free `L²` route to de Finetti's theorem. The route's
substantive conclusion,
`Contractable.conditionallyIIDWith_directingProbabilityMeasure`, names the tail-conditional
directing measure and proves the joint-law disintegration of every finite block. Here that named
witness is packaged into `ConditionallyIID`, and the standard exchangeable and equivalence forms
are derived from the elementary implication lattice.

The suffix `_viaL2` records the proof route. The corresponding unsuffixed public theorems in
`TauCeti.Probability.DeFinetti.Theorem` use the reverse-martingale route and are deliberately not
imported here. Thus importing this module gives a complete de Finetti theorem without importing
reverse-martingale convergence or the unsuffixed summit.

## Main results

* `conditionallyIID_of_contractable_viaL2` — a contractable process is conditionally i.i.d.;
* `deFinetti_viaL2` — an exchangeable process is conditionally i.i.d.;
* `deFinetti_RyllNardzewski_equivalence_viaL2` — contractability is equivalent to the conjunction
  of exchangeability and conditional i.i.d.-ness.

These route wrappers are the final target of Layer 3 of
`TauCetiRoadmap/Exchangeability/README.md`. They are not adapted from the legacy theorem wrappers in
`cameronfreer/exchangeability`: those wrappers conclude only the mixture identity, whereas the
results here package Tau Ceti's stronger joint-law disintegration.

## References

* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 1,
  Theorem 1.1.
* C. Ryll-Nardzewski, "On stationary sequences of random variables and the de Finetti
  equivalence", 1957.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **The contractable form of de Finetti's theorem via `L²` averaging.** A contractable process
valued in a nonempty standard Borel space is conditionally i.i.d.

The directing measure witnessing the conclusion is
`directingProbabilityMeasure μ X`; its stronger witness-level statement is
`Contractable.conditionallyIIDWith_directingProbabilityMeasure`. -/
theorem conditionallyIID_of_contractable_viaL2 [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n)) :
    ConditionallyIID μ X :=
  ConditionallyIID.of_directing
    (hX.conditionallyIIDWith_directingProbabilityMeasure hX_meas)

/-- **De Finetti's theorem via `L²` averaging.** An exchangeable process valued in a nonempty
standard Borel space is conditionally i.i.d. -/
theorem deFinetti_viaL2 [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX_meas : ∀ n, Measurable (X n))
    (hX : Exchangeable μ X) :
    ConditionallyIID μ X :=
  conditionallyIID_of_contractable_viaL2
    (hX.contractable fun n => (hX_meas n).aemeasurable) hX_meas

/-- **The de Finetti--Ryll-Nardzewski equivalence via `L²` averaging.** For a measurable process
on a nonempty standard Borel state space, contractability is equivalent to being both exchangeable
and conditionally i.i.d. -/
theorem deFinetti_RyllNardzewski_equivalence_viaL2 [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hX_meas : ∀ n, Measurable (X n)) :
    Contractable μ X ↔ Exchangeable μ X ∧ ConditionallyIID μ X := by
  constructor
  · intro hX
    have hX_cond := conditionallyIID_of_contractable_viaL2 hX hX_meas
    exact ⟨hX_cond.exchangeable, hX_cond⟩
  · exact fun hX => hX.2.contractable

end Probability

end TauCeti

end
