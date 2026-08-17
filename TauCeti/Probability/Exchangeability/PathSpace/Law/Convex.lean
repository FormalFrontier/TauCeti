/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.PathSpace.Law.Basic
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Convex

/-!
# The convex structure on exchangeable path laws

Exchangeable probability laws on `ℕ → α` are closed under convex combination
(`ExchangeableLaw.smul_add_smul`), so the subtype they form carries the convex structure of
`ProbabilityMeasure`. This file names that combination.

It is generic path-law API: nothing here mentions the de Finetti representation. Keeping it out of
`DeFinetti/Correspondence.lean` is what lets a client use the convex structure without depending on
the correspondence theory, even though the affinity of `deFinettiEquiv` is what it was built for.

## Main results

* `exchangeableLawConvexCombo` — the combination, with `toMeasure_exchangeableLawConvexCombo`
  exposing its underlying measure.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- The **convex combination of two exchangeable path laws**, in the subtype of exchangeable
probability measures on `ℕ → α`. Exchangeability is preserved because the defining permutation
invariance is linear (`ExchangeableLaw.smul_add_smul`). -/
def exchangeableLawConvexCombo {a b : ℝ≥0∞} (hab : a + b = 1)
    (ρ₁ ρ₂ : {ρ : ProbabilityMeasure (ℕ → α) // ExchangeableLaw (ρ : Measure (ℕ → α))}) :
    {ρ : ProbabilityMeasure (ℕ → α) // ExchangeableLaw (ρ : Measure (ℕ → α))} :=
  ⟨ProbabilityMeasure.convexCombo hab ρ₁ ρ₂, by
    rw [ProbabilityMeasure.toMeasure_convexCombo]
    exact ρ₁.2.smul_add_smul ρ₂.2 a b⟩

/-- The underlying measure of a convex combination of exchangeable laws. -/
@[simp]
theorem toMeasure_exchangeableLawConvexCombo {a b : ℝ≥0∞} (hab : a + b = 1)
    (ρ₁ ρ₂ : {ρ : ProbabilityMeasure (ℕ → α) // ExchangeableLaw (ρ : Measure (ℕ → α))}) :
    ((exchangeableLawConvexCombo hab ρ₁ ρ₂ : ProbabilityMeasure (ℕ → α)) : Measure (ℕ → α))
      = a • ((ρ₁ : ProbabilityMeasure (ℕ → α)) : Measure (ℕ → α))
        + b • ((ρ₂ : ProbabilityMeasure (ℕ → α)) : Measure (ℕ → α)) :=
  ProbabilityMeasure.toMeasure_convexCombo hab _ _

end Probability

end TauCeti
