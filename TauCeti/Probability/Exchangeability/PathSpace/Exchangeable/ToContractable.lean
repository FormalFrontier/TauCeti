/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.PathSpace.ContractableLaw

/-!
# Exchangeable path laws are contractable

This file records the path-space form of the Layer 0 bridge from exchangeability to
contractability: an exchangeable finite measure on one-sided path space is invariant under
every strictly increasing reindexing of time. The process-level theorem remains available in
`TauCeti.Probability.Exchangeability.Contractability`; this file is the corresponding
`ExchangeableLaw` to `ContractableLaw` adapter.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- An exchangeable finite path law is contractable: invariance under all permutations implies
invariance under every strictly increasing time reindexing. -/
theorem ExchangeableLaw.contractableLaw {ρ : Measure (ℕ → α)} [IsFiniteMeasure ρ]
    (hρ : ExchangeableLaw ρ) :
    ContractableLaw ρ := by
  rw [contractableLaw_iff_forall_map_prefixProj_of_strictMono]
  intro n k hk
  exact hρ.map_prefixProj_of_injective k hk.injective

end Probability

end TauCeti
