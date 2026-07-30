/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
import TauCeti.Probability.Exchangeability.Contractability

/-!
# Exchangeable families

This file extends the sequence-level symmetry predicates to families indexed by an arbitrary type.
An `ExchangeableFamily` has the same law along any two finite injective selections of indices.
The existing `ConditionallyIIDWith` and `ConditionallyIID` predicates are already index-generic;
this file relates them to exchangeable families.

## Main results

* `exchangeableFamily_iff_exchangeable` identifies the family predicate over `ℕ` with the existing
  sequence predicate.
* `ConditionallyIIDWith.exchangeableFamily` and `ConditionallyIID.exchangeableFamily` give the
  easy implication from conditional i.i.d.-ness to exchangeability.
* `ExchangeableFamily.comp_injective` reindexes a family along an injection; the corresponding
  conditional i.i.d. lemmas are in `ConditionallyIID.Basic`.

This is the family exchangeability API needed for the Layer 8 target “de Finetti for other
countable index types” in `TauCetiRoadmap/Exchangeability/README.md`. The countable-index theorem
itself is in `TauCeti.Probability.DeFinetti.CountableIndex`.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α ι κ : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- A family is exchangeable when its law is unchanged after replacing any finite injective
selection of indices by another of the same size. -/
def ExchangeableFamily (μ : Measure Ω) (X : ι → Ω → α) : Prop :=
  ∀ (m : ℕ) (k l : Fin m → ι), Function.Injective k → Function.Injective l →
    μ.map (fun ω i => X (k i) ω) = μ.map fun ω i => X (l i) ω

/-- Constructor for exchangeability of an arbitrary family. -/
theorem ExchangeableFamily.intro {μ : Measure Ω} {X : ι → Ω → α}
    (h : ∀ (m : ℕ) (k l : Fin m → ι), Function.Injective k → Function.Injective l →
      μ.map (fun ω i => X (k i) ω) = μ.map fun ω i => X (l i) ω) :
    ExchangeableFamily μ X :=
  h

/-- Simp normal form for exchangeability of an arbitrary family. -/
@[simp]
theorem exchangeableFamily_iff {μ : Measure Ω} {X : ι → Ω → α} :
    ExchangeableFamily μ X ↔
      ∀ (m : ℕ) (k l : Fin m → ι), Function.Injective k → Function.Injective l →
        μ.map (fun ω i => X (k i) ω) = μ.map fun ω i => X (l i) ω :=
  Iff.rfl

/-- The finite-block law equality defining an exchangeable family. -/
@[grind =>]
theorem ExchangeableFamily.blockLaw_eq {μ : Measure Ω} {X : ι → Ω → α}
    (h : ExchangeableFamily μ X) {m : ℕ} (k l : Fin m → ι)
    (hk : Function.Injective k) (hl : Function.Injective l) :
    μ.map (fun ω i => X (k i) ω) = μ.map fun ω i => X (l i) ω :=
  h m k l hk hl

/-- A conditionally i.i.d. family with a named directing measure is exchangeable. -/
theorem ConditionallyIIDWith.exchangeableFamily
    {μ : Measure Ω} {X : ι → Ω → α} {ν : Ω → ProbabilityMeasure α}
    (h : ConditionallyIIDWith μ X ν) : ExchangeableFamily μ X := by
  refine ExchangeableFamily.intro fun m k l hk hl => ?_
  calc
    μ.map (fun ω i => X (k i) ω) =
        (μ.map fun ω => (ν ω, fun i : Fin m => X (k i) ω)).snd := by
      rw [Measure.snd_map_prodMk₀ h.measurable_directing.aemeasurable]
    _ = (μ.bind fun ω =>
          (Measure.dirac (ν ω)).prod
            (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure).snd := by
      rw [h.jointLaw_eq_disintegration k hk]
    _ = (μ.map fun ω => (ν ω, fun i : Fin m => X (l i) ω)).snd := by
      rw [h.jointLaw_eq_disintegration l hl]
    _ = μ.map fun ω i => X (l i) ω := by
      rw [Measure.snd_map_prodMk₀ h.measurable_directing.aemeasurable]

/-- A conditionally i.i.d. family is exchangeable. -/
theorem ConditionallyIID.exchangeableFamily
    {μ : Measure Ω} {X : ι → Ω → α} (h : ConditionallyIID μ X) :
    ExchangeableFamily μ X :=
  let ⟨_, hν⟩ := h.exists_directing
  hν.exchangeableFamily

/-- Exchangeability is preserved by reindexing a family along an injection. -/
theorem ExchangeableFamily.comp_injective {μ : Measure Ω} {X : ι → Ω → α}
    (h : ExchangeableFamily μ X) {f : κ → ι} (hf : Function.Injective f) :
    ExchangeableFamily μ fun j => X (f j) := by
  refine ExchangeableFamily.intro fun m k l hk hl => ?_
  simpa only [Function.comp_apply] using
    h.blockLaw_eq (f ∘ k) (f ∘ l) (hf.comp hk) (hf.comp hl)

/-! ## Comparison with the sequence predicates -/

/-- An exchangeable family indexed by `ℕ` is an exchangeable sequence. -/
theorem ExchangeableFamily.exchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : ExchangeableFamily μ X) : Exchangeable μ X := by
  intro n σ
  simpa only [blockLaw_def, prefixLaw_def] using
    h.blockLaw_eq (fun i : Fin n => (σ i).val) Fin.val
      (fun _ _ hij => σ.injective (Fin.ext hij)) Fin.val_injective

/-- An exchangeable sequence with a.e. measurable coordinates is exchangeable as an
`ℕ`-indexed family. -/
theorem Exchangeable.exchangeableFamily {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (h : Exchangeable μ X) (hX : ∀ i, AEMeasurable (X i) μ) :
    ExchangeableFamily μ X := by
  refine ExchangeableFamily.intro fun m k l hk hl => ?_
  rw [← blockLaw_def, ← blockLaw_def]
  exact (h.blockLaw_eq_prefixLaw_of_injective hX k hk).trans
    (h.blockLaw_eq_prefixLaw_of_injective hX l hl).symm

/-- For a finite measure and a.e. measurable coordinates, exchangeability as an `ℕ`-indexed family
is equivalent to the existing sequence predicate. -/
theorem exchangeableFamily_iff_exchangeable {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : ∀ i, AEMeasurable (X i) μ) :
    ExchangeableFamily μ X ↔ Exchangeable μ X :=
  ⟨ExchangeableFamily.exchangeable, fun h => h.exchangeableFamily hX⟩

end Probability

end TauCeti
