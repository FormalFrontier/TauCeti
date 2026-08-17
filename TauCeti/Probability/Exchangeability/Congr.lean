/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.Basic

/-!
# Symmetry notions under a coordinatewise almost-everywhere change of process

Every symmetry predicate of Layer 0 is a statement about the finite-dimensional laws of `X`, or —
for `FullyExchangeable` — about its path law, so each sees the coordinates only modulo `μ`-a.e.
equality. This file records that: replacing each `X i` by a coordinatewise a.e. equal `Y i` changes
neither `blockLaw`, `prefixLaw` and `pathLaw` nor any of `ExchangeableAt`, `Exchangeable`,
`FullyExchangeable` and `Contractable`.

Changing a random variable on a null set is routine — most often to replace an a.e. measurable
coordinate by a measurable version — and without these lemmas a valid process becomes unusable at
the interfaces that demand exact measurability. The representation predicates get the same treatment
beside their own definitions, in `MixedIID/Congr.lean` and `ConditionallyIID/Congr.lean`.

## Main results

* `blockLaw_congr`, `prefixLaw_congr`, `pathLaw_congr` — the finite-dimensional and path laws are
  unchanged.
* `ExchangeableAt.congr`, `Exchangeable.congr`, `FullyExchangeable.congr`, `Contractable.congr` —
  the symmetry predicates transport.

## Implementation

Everything reduces to `Measure.map_congr`: a coordinate selection `Fin m → ι` is countable, so
`ae_all_iff` turns the coordinatewise hypotheses into a single a.e. statement about the tuple map,
and the same argument over `ℕ` handles the path map.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Coordinatewise a.e. equal families have the same finite-dimensional block laws. -/
theorem blockLaw_congr {μ : Measure Ω} {X Y : ι → Ω → α} (h : ∀ i, X i =ᵐ[μ] Y i) {m : ℕ}
    (k : Fin m → ι) : blockLaw μ X k = blockLaw μ Y k := by
  rw [blockLaw_def, blockLaw_def]
  refine Measure.map_congr ?_
  filter_upwards [ae_all_iff.2 fun i : Fin m => h (k i)] with ω hω using funext hω

/-- Coordinatewise a.e. equal processes have the same prefix laws. -/
theorem prefixLaw_congr {μ : Measure Ω} {X Y : ℕ → Ω → α} (h : ∀ i, X i =ᵐ[μ] Y i) (n : ℕ) :
    prefixLaw μ X n = prefixLaw μ Y n := by
  rw [prefixLaw_def, prefixLaw_def]
  exact blockLaw_congr h _

/-- Coordinatewise a.e. equal processes have the same path law. -/
theorem pathLaw_congr {μ : Measure Ω} {X Y : ℕ → Ω → α} (h : ∀ i, X i =ᵐ[μ] Y i) :
    pathLaw μ X = pathLaw μ Y := by
  rw [pathLaw_def, pathLaw_def]
  refine Measure.map_congr ?_
  filter_upwards [ae_all_iff.2 h] with ω hω using funext hω

/-- Exchangeability at a fixed length transports along a coordinatewise a.e. change of process. -/
theorem ExchangeableAt.congr {μ : Measure Ω} {X Y : ℕ → Ω → α} {n : ℕ}
    (hX : ExchangeableAt μ X n) (h : ∀ i, X i =ᵐ[μ] Y i) : ExchangeableAt μ Y n := fun σ => by
  rw [← blockLaw_congr h, ← prefixLaw_congr h]
  exact hX σ

/-- Exchangeability transports along a coordinatewise a.e. change of process. -/
theorem Exchangeable.congr {μ : Measure Ω} {X Y : ℕ → Ω → α} (hX : Exchangeable μ X)
    (h : ∀ i, X i =ᵐ[μ] Y i) : Exchangeable μ Y := fun n => (hX n).congr h

/-- Full exchangeability transports along a coordinatewise a.e. change of process. -/
theorem FullyExchangeable.congr {μ : Measure Ω} {X Y : ℕ → Ω → α} (hX : FullyExchangeable μ X)
    (h : ∀ i, X i =ᵐ[μ] Y i) : FullyExchangeable μ Y := fun σ => by
  rw [← pathLaw_congr h, ← hX σ]
  exact Measure.map_congr
    (by filter_upwards [ae_all_iff.2 fun i => (h (σ i)).symm] with ω hω using funext hω)

/-- Contractability transports along a coordinatewise a.e. change of process. -/
theorem Contractable.congr {μ : Measure Ω} {X Y : ℕ → Ω → α} (hX : Contractable μ X)
    (h : ∀ i, X i =ᵐ[μ] Y i) : Contractable μ Y := fun m k hk => by
  rw [← blockLaw_congr h, ← prefixLaw_congr h]
  exact hX m k hk

end Probability

end TauCeti
