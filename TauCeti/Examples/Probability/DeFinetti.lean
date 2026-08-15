/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.DeFinetti

/-!
# Worked examples: the de Finetti public API

Every example here imports **only** `TauCeti.Probability.DeFinetti`. That is the point: the file
checks that the curated facade is by itself enough to name and apply the Layer 7 endpoints, so a
consumer never has to reach into the modules behind it.

Nothing is proved here. Each example applies an existing theorem, and the file declares nothing of
its own; a failure to elaborate would mean the facade is missing an export, not that a proof broke.

## What is checked

* the four process predicates are nameable from the facade;
* `deFinetti`, and both route-suffixed summits, prove conditional i.i.d.-ness from the same
  hypotheses — `deFinetti_viaL2` through `L²` averaging and the tail, `deFinetti_viaKoopman`
  through Koopman operators and the shift-invariant σ-algebra;
* the de Finetti--Ryll-Nardzewski equivalence, the mixture representation, and its uniqueness.

The *mathematical* worked examples the roadmap asks for live with the objects they concern, not
here: the conditionally i.i.d. coin-flip construction is in
`Exchangeability/ConditionallyIID/CoinFlips.lean`, the constant-witness characterisation of i.i.d.
in `ConditionallyIID/Const.lean`, and the stationary-but-not-exchangeable 3-cycle in
`Exchangeability/ThreeCycle.lean`.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, **Layer 7** (public API and examples), whose
  suggested home for this file is `TauCeti/Examples/Probability/DeFinetti.lean`.
-/

public section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

-- Every Layer 7 endpoint is reachable from the facade alone.
section Reachable
example : Prop := ∀ (μ : Measure Ω) (X : ℕ → Ω → α), Exchangeable μ X
example : Prop := ∀ (μ : Measure Ω) (X : ℕ → Ω → α), Contractable μ X
example : Prop := ∀ (μ : Measure Ω) (X : ℕ → Ω → α), ConditionallyIID μ X
example : Prop := ∀ (μ : Measure Ω) (X : ℕ → Ω → α), MixedIID μ X
end Reachable

-- The summit, and both named routes, from the same hypotheses.
example [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX_meas : ∀ n, Measurable (X n)) (hX : Exchangeable μ X) :
    ConditionallyIID μ X :=
  deFinetti hX_meas hX

example [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX_meas : ∀ n, Measurable (X n)) (hX : Exchangeable μ X) :
    ConditionallyIID μ X :=
  deFinetti_viaL2 hX_meas hX

example [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX_meas : ∀ n, Measurable (X n)) (hX : Exchangeable μ X) :
    ConditionallyIID μ X :=
  deFinetti_viaKoopman hX_meas hX

-- Contractability, exchangeability and conditional i.i.d.-ness are related as the
-- de Finetti--Ryll-Nardzewski equivalence describes.
example [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX_meas : ∀ n, Measurable (X n)) (hX : Contractable μ X) :
    Exchangeable μ X ∧ ConditionallyIID μ X :=
  (deFinetti_RyllNardzewski_equivalence hX_meas).mp hX

-- A contractable process is a mixture of i.i.d. laws.
example [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) :
    MixedIID μ X :=
  mixedIID_of_contractable hX hX_meas

-- The mixing law of an exchangeable process is unique.
example [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Exchangeable μ X) (hX_meas : ∀ n, Measurable (X n)) :
    ∃! π : ProbabilityMeasure (ProbabilityMeasure α),
      pathLaw μ X = (π : Measure (ProbabilityMeasure α)).bind
        fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α) :=
  deFinetti_mixture hX hX_meas

end Probability

end TauCeti

end
