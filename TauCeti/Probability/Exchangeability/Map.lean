/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.Contractability

/-!
# Coordinatewise maps of exchangeable processes

This file records that the Layer 0 symmetry notions for sequence laws are preserved by
applying a measurable map to every coordinate of the process. It supplies the process-level
closure API promised by the Exchangeability roadmap from the law-level lemmas
`map_blockLaw`, `map_prefixLaw`, and `map_pathLaw` in `Basic.lean`.

These statements follow `TauCetiRoadmap/Exchangeability/README.md`, Layer 0, the item
asking for closure of the symmetry classes under coordinatewise pushforward. The proofs use
only Tau Ceti's existing finite-dimensional law API and Mathlib's `Measure.map`
composition lemmas.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]

/-- Finite exchangeability at a fixed length is preserved by a coordinatewise measurable
map of the value space. -/
theorem ExchangeableAt.map_values {μ : Measure Ω} {X : ℕ → Ω → α} {n : ℕ}
    (h : ExchangeableAt μ X n) {f : α → β} (hf : Measurable f)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) :
    ExchangeableAt μ (fun n ω => f (X n ω)) n := by
  intro σ
  calc
    blockLaw μ (fun n ω => f (X n ω)) (fun i : Fin n => (σ i).val) =
        (blockLaw μ X (fun i : Fin n => (σ i).val)).map
          (fun x : Fin n → α => fun i => f (x i)) := by
      exact (map_blockLaw μ (fun i : Fin n => (σ i).val) hf (fun i => hX (σ i))).symm
    _ = (prefixLaw μ X n).map (fun x : Fin n → α => fun i => f (x i)) := by
      rw [h.permute σ]
    _ = prefixLaw μ (fun n ω => f (X n ω)) n := by
      exact map_prefixLaw μ hf n hX

/-- Finite exchangeability is preserved by a coordinatewise measurable map of the value
space. -/
theorem Exchangeable.map_values {μ : Measure Ω} {X : ℕ → Ω → α} (h : Exchangeable μ X)
    {f : α → β} (hf : Measurable f) (hX : ∀ i, AEMeasurable (X i) μ) :
    Exchangeable μ (fun n ω => f (X n ω)) := by
  intro n
  exact (h.exchangeableAt n).map_values hf (fun i => hX i.val)

/-- Full exchangeability is preserved by a coordinatewise measurable map of the value
space. -/
theorem FullyExchangeable.map_values {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : FullyExchangeable μ X) {f : α → β} (hf : Measurable f)
    (hX : ∀ i, AEMeasurable (X i) μ) :
    FullyExchangeable μ (fun n ω => f (X n ω)) := by
  intro π
  calc
    μ.map (fun ω i => f (X (π i) ω)) =
        (pathLaw μ (fun n ω => X (π n) ω)).map
          (fun x : ℕ → α => fun i => f (x i)) := by
      exact (map_pathLaw μ hf (fun i => hX (π i))).symm
    _ = (pathLaw μ X).map (fun x : ℕ → α => fun i => f (x i)) := by
      rw [pathLaw_def, h.permute π]
    _ = pathLaw μ (fun n ω => f (X n ω)) := by
      exact map_pathLaw μ hf hX

/-- Contractability is preserved by a coordinatewise measurable map of the value space. -/
theorem Contractable.map_values {μ : Measure Ω} {X : ℕ → Ω → α} (h : Contractable μ X)
    {f : α → β} (hf : Measurable f) (hX : ∀ i, AEMeasurable (X i) μ) :
    Contractable μ (fun n ω => f (X n ω)) := by
  intro m k hk
  calc
    blockLaw μ (fun n ω => f (X n ω)) k =
        (blockLaw μ X k).map (fun x : Fin m → α => fun i => f (x i)) := by
      exact (map_blockLaw μ k hf (fun i => hX (k i))).symm
    _ = (prefixLaw μ X m).map (fun x : Fin m → α => fun i => f (x i)) := by
      rw [h.map hk]
    _ = prefixLaw μ (fun n ω => f (X n ω)) m := by
      exact map_prefixLaw μ hf m (fun i => hX i.val)

end Probability

end TauCeti
