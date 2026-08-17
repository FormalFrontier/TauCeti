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

* `ExchangeableLaw.smul_add_smul` — the unbundled closure of exchangeability under nonnegative
  linear combination, the prerequisite for the bundling.
* `exchangeableLawConvexComb` — the combination, with `toMeasure_exchangeableLawConvexComb`
  exposing its underlying measure.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- **Exchangeable laws are closed under convex combination**, and more generally under any
nonnegative linear combination: the defining invariance is an equation between pushforwards, and
`Measure.map` along the (measurable) reindexing is additive and homogeneous. -/
theorem ExchangeableLaw.smul_add_smul {ρ₁ ρ₂ : Measure (ℕ → α)} (h₁ : ExchangeableLaw ρ₁)
    (h₂ : ExchangeableLaw ρ₂) (a b : ℝ≥0∞) : ExchangeableLaw (a • ρ₁ + b • ρ₂) :=
  .intro fun π => by
    have hmeas : Measurable (permReindex (α := α) π) := measurable_reindex π
    rw [Measure.map_add _ _ hmeas, Measure.map_smul, Measure.map_smul,
      h₁.map_permReindex π, h₂.map_permReindex π]

/-- The **convex combination of two exchangeable path laws**, in the subtype of exchangeable
probability measures on `ℕ → α`. Exchangeability is preserved because the defining permutation
invariance is linear (`ExchangeableLaw.smul_add_smul`). -/
def exchangeableLawConvexComb {a b : ℝ≥0∞} (hab : a + b = 1)
    (ρ₁ ρ₂ : {ρ : ProbabilityMeasure (ℕ → α) // ExchangeableLaw (ρ : Measure (ℕ → α))}) :
    {ρ : ProbabilityMeasure (ℕ → α) // ExchangeableLaw (ρ : Measure (ℕ → α))} :=
  ⟨ProbabilityMeasure.convexComb hab ρ₁ ρ₂, by
    rw [ProbabilityMeasure.toMeasure_convexComb]
    exact ρ₁.2.smul_add_smul ρ₂.2 a b⟩

/-- The underlying measure of a convex combination of exchangeable laws. -/
@[simp]
theorem toMeasure_exchangeableLawConvexComb {a b : ℝ≥0∞} (hab : a + b = 1)
    (ρ₁ ρ₂ : {ρ : ProbabilityMeasure (ℕ → α) // ExchangeableLaw (ρ : Measure (ℕ → α))}) :
    ((exchangeableLawConvexComb hab ρ₁ ρ₂ : ProbabilityMeasure (ℕ → α)) : Measure (ℕ → α))
      = a • ((ρ₁ : ProbabilityMeasure (ℕ → α)) : Measure (ℕ → α))
        + b • ((ρ₂ : ProbabilityMeasure (ℕ → α)) : Measure (ℕ → α)) :=
  ProbabilityMeasure.toMeasure_convexComb hab _ _

end Probability

end TauCeti
