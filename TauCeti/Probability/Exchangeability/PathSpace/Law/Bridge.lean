/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.Contractability
public import TauCeti.Probability.Exchangeability.FullyExchangeable
public import TauCeti.Probability.Exchangeability.PathSpace.ContractableLaw
public import TauCeti.Probability.Exchangeability.PathSpace.Law.Basic

/-!
# Process-level ↔ path-law bridges for exchangeability

This file connects the process-level `FullyExchangeable`/`Exchangeable` predicates with the
path-space `ExchangeableLaw` predicate: a process is fully exchangeable exactly when its
`pathLaw` is an exchangeable path-space law, and (under a finite base law) finite exchangeability
is the same statement. It also connects process-level contractability with the path-space
`ContractableLaw` predicate.

The bridges realize the Layer 0 roadmap item asking for process-level ↔ path-law bridges in both
directions. They reuse the existing `FullyExchangeable` path-law bridge from
`FullyExchangeable.lean` and the contractability bridge from `Contractability.lean`; no
measure-theoretic infrastructure is vendored.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- A fully exchangeable process has an exchangeable path law. -/
theorem FullyExchangeable.exchangeableLaw_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : FullyExchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    ExchangeableLaw (pathLaw μ X) :=
  ExchangeableLaw.intro fun π => hX.map_permReindex_pathLaw hX_meas π

/-- A process is fully exchangeable iff its path law is an exchangeable path-space measure. -/
theorem fullyExchangeable_iff_exchangeableLaw_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    FullyExchangeable μ X ↔ ExchangeableLaw (pathLaw μ X) := by
  rw [fullyExchangeable_iff_forall_map_permReindex_pathLaw μ hX_meas, exchangeableLaw_iff]

/-- For finite laws, finite exchangeability of a process is equivalent to exchangeability of
its path law. -/
theorem exchangeable_iff_exchangeableLaw_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    Exchangeable μ X ↔ ExchangeableLaw (pathLaw μ X) := by
  rw [exchangeable_iff_fullyExchangeable hX_meas,
    fullyExchangeable_iff_exchangeableLaw_pathLaw μ hX_meas]

/-- A process whose path law is exchangeable is fully exchangeable. -/
theorem fullyExchangeable_of_exchangeableLaw_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_meas : ∀ i, AEMeasurable (X i) μ) (hρ : ExchangeableLaw (pathLaw μ X)) :
    FullyExchangeable μ X :=
  (fullyExchangeable_iff_exchangeableLaw_pathLaw μ hX_meas).2 hρ

/-- A process whose path law is exchangeable is finitely exchangeable under a finite base law. -/
theorem exchangeable_of_exchangeableLaw_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX_meas : ∀ i, AEMeasurable (X i) μ)
    (hρ : ExchangeableLaw (pathLaw μ X)) :
    Exchangeable μ X :=
  (exchangeable_iff_exchangeableLaw_pathLaw hX_meas).2 hρ

/-- A contractable process has a contractable path law. -/
theorem Contractable.contractableLaw_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Contractable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    ContractableLaw (pathLaw μ X) :=
  ContractableLaw.intro fun _ hφ => (hX.measurePreserving_reindex hX_meas hφ).map_eq

/-- Contractability of a process is equivalent to contractability of its path law. -/
theorem contractable_iff_contractableLaw_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    Contractable μ X ↔ ContractableLaw (pathLaw μ X) := by
  rw [contractable_iff_forall_map_reindex_pathLaw hX_meas, contractableLaw_iff]

/-- If a process has a contractable path law, then the process is contractable. -/
theorem contractable_of_contractableLaw_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX_meas : ∀ i, AEMeasurable (X i) μ)
    (hρ : ContractableLaw (pathLaw μ X)) :
    Contractable μ X :=
  (contractable_iff_contractableLaw_pathLaw hX_meas).2 hρ

end Probability

end TauCeti
