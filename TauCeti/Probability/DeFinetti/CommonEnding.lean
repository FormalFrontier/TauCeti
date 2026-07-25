/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.MixedIID.Basic

/-!
# The rectangle common ending for de Finetti

This file provides the first shared de Finetti common-ending adapter.  If a measurable random
probability measure `ν : Ω → ProbabilityMeasure α` has the expected rectangle factorization for
every finite injective block of a process, then the process is `MixedIID`.

The work is done by the `MixedIIDWith` rectangle characterization
(`mixedIIDWith_of_forall_rectangles`, next to its definition): rectangles generate the
finite product σ-algebra by Mathlib's `generateFrom_pi` / `isPiSystem_pi`, and Tau Ceti's
product-kernel API evaluates the mixture on rectangles.  This file packages that as the existential
wrapper.  This advances `TauCetiRoadmap/Exchangeability/README.md`, Layer 1, the mixture common
de Finetti ending `mixedIID_of_mixingRepresentative`. The joint-rectangle strengthening
`conditionallyIID_of_jointRectangles`, which the roadmap pairs with it, awaits the conditional
predicate.

This is adapted from the rectangle common-ending strategy in
`cameronfreer/exchangeability` (`DeFinetti/CommonEnding.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`), but stated over Tau Ceti's current
`MixedIIDWith` and `ProbabilityMeasure.pi` APIs.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Common de Finetti ending.** Rectangle-wise product-kernel factorization against a named
mixing representative supplies a `MixedIID` witness for the process. -/
theorem mixedIID_of_mixingRepresentative {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α} (hν : Measurable ν)
    (h_rect : ∀ (m : ℕ) (k : Fin m → ℕ), Function.Injective k →
      ∀ B : Fin m → Set α, (∀ i, MeasurableSet (B i)) →
        blockLaw μ X k (Set.univ.pi B) =
          ∫⁻ ω, ∏ i : Fin m, (ν ω : Measure α) (B i) ∂μ) :
    MixedIID μ X :=
  MixedIID.of_mixingRepresentative (mixedIIDWith_of_forall_rectangles hν h_rect)

end Probability

end TauCeti
