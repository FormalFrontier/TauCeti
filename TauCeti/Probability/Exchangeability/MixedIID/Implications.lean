/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.MixedIID.Basic

/-!
# Basic implications from mixed i.i.d.-ness

This file records the first implication out of the Layer 0 mixed-i.i.d. API:
mixed i.i.d. processes are exchangeable.  The definition
`MixedIIDWith μ X ν` already states that every injective finite coordinate selection
has the same product-mixture law, so the exchangeability proof is just the specialization to
the permuted and identity selections of `Fin n`.

The resulting exchangeability theorem is one of the Layer 0 bridges listed in
`TauCetiRoadmap/Exchangeability/Suggested.lean`; the contractability corollaries use the same
injective-block identity, since strictly increasing finite selections are injective.

These declarations follow the `cameronfreer/exchangeability` Layer 0 implication lattice
pinned at `e0532e59ceff23edab44dda9ab0655debbc9cc22`, but use Tau Ceti's current
`MixedIIDWith` API, where the finite-block mixture identity is already stated for
arbitrary injective selections.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

private theorem injective_perm_val {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective fun i : Fin n => (σ i).val := by
  intro i j hij
  exact σ.injective (Fin.ext hij)

private theorem injective_fin_val {n : ℕ} :
    Function.Injective fun i : Fin n => i.val := by
  intro i j hij
  exact Fin.ext hij

/-- Under a named mixing representative, the prefix law has the common finite-product mixture
law. -/
theorem MixedIIDWith.prefixLaw_eq_mixture {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : MixedIIDWith μ X ν) (n : ℕ) :
    prefixLaw μ X n =
      μ.bind fun ω => (ProbabilityMeasure.pi fun _ : Fin n => ν ω).toMeasure := by
  rw [prefixLaw_def]
  exact h.blockLaw_eq_mixture (fun i : Fin n => i.val) injective_fin_val

/-- Under a named mixing representative, every injective finite block has the same law as the
corresponding prefix. -/
theorem MixedIIDWith.blockLaw_eq_prefixLaw_of_injective {μ : Measure Ω}
    {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α} (h : MixedIIDWith μ X ν)
    {m : ℕ} {k : Fin m → ℕ} (hk : Function.Injective k) :
    blockLaw μ X k = prefixLaw μ X m := by
  rw [h.blockLaw_eq_mixture k hk, h.prefixLaw_eq_mixture m]

/-- A mixed i.i.d. process has the same law along every injective finite block as along the
corresponding prefix. -/
theorem MixedIID.blockLaw_eq_prefixLaw_of_injective {μ : Measure Ω}
    {X : ℕ → Ω → α} (h : MixedIID μ X) {m : ℕ} {k : Fin m → ℕ}
    (hk : Function.Injective k) :
    blockLaw μ X k = prefixLaw μ X m := by
  obtain ⟨ν, hν⟩ := h.exists_mixingRepresentative
  exact hν.blockLaw_eq_prefixLaw_of_injective hk

/-- A named mixing representative makes the law of each finite prefix invariant under
permutations of that prefix. -/
theorem MixedIIDWith.exchangeableAt {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : MixedIIDWith μ X ν) (n : ℕ) :
    ExchangeableAt μ X n := by
  intro σ
  exact h.blockLaw_eq_prefixLaw_of_injective (injective_perm_val σ)

/-- A process with a named mixing representative is exchangeable. -/
theorem MixedIIDWith.exchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : MixedIIDWith μ X ν) : Exchangeable μ X := by
  intro n
  exact h.exchangeableAt n

/-- A mixed i.i.d. process is exchangeable. This is the Layer 0 bridge from the mixed-i.i.d.
API to finite exchangeability (the roadmap's `exchangeable_of_mixedIID`). -/
theorem MixedIID.exchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : MixedIID μ X) : Exchangeable μ X := by
  obtain ⟨ν, hν⟩ := h.exists_mixingRepresentative
  exact hν.exchangeable

/-- A process with a named mixing representative is contractable: strictly increasing finite
selections are injective finite selections. -/
theorem MixedIIDWith.contractable {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : MixedIIDWith μ X ν) : Contractable μ X := by
  intro m k hk
  exact h.blockLaw_eq_prefixLaw_of_injective hk.injective

/-- A mixed i.i.d. process is contractable: strictly increasing finite selections are
injective finite selections. -/
theorem MixedIID.contractable {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : MixedIID μ X) : Contractable μ X := by
  intro m k hk
  exact h.blockLaw_eq_prefixLaw_of_injective hk.injective

end Probability

end TauCeti
