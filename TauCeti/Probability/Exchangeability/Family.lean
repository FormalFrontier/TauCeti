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
`ConditionallyIIDWithFamily` strengthens this to the joint-law disintegration with a named
directing measure, and `ConditionallyIIDFamily` is its existential wrapper.

## Main results

* `exchangeableFamily_iff_exchangeable` identifies the family predicate over `ℕ` with the existing
  sequence predicate.
* `conditionallyIIDWithFamily_iff_conditionallyIIDWith` and
  `conditionallyIIDFamily_iff_conditionallyIID` give the corresponding identifications for the
  conditional predicates.
* `ConditionallyIIDWithFamily.exchangeableFamily` and
  `ConditionallyIIDFamily.exchangeableFamily` give the easy implication from conditional
  i.i.d.-ness to exchangeability.
* `ExchangeableFamily.comp_injective`, `ConditionallyIIDWithFamily.comp_injective`, and
  `ConditionallyIIDFamily.comp_injective` reindex a family along an injection.

These are the index-generic definitions needed for the Layer 8 target “de Finetti for other
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

/-- Conditional i.i.d.-ness of an arbitrary family with a specified directing measure. Along every
finite injective selection of indices, the joint law of the directing measure and the selected
block is the disintegration `∫ δ_ν ⊗ νⁿ dμ`. -/
def ConditionallyIIDWithFamily (μ : Measure Ω) (X : ι → Ω → α)
    (ν : Ω → ProbabilityMeasure α) : Prop :=
  Measurable ν ∧
    ∀ (m : ℕ) (k : Fin m → ι), Function.Injective k →
      μ.map (fun ω => (ν ω, fun i : Fin m => X (k i) ω)) =
        μ.bind fun ω =>
          (Measure.dirac (ν ω)).prod (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure

/-- Constructor for conditional i.i.d.-ness of an arbitrary family with a named directing
measure. -/
theorem ConditionallyIIDWithFamily.intro {μ : Measure Ω} {X : ι → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (hν : Measurable ν)
    (h : ∀ (m : ℕ) (k : Fin m → ι), Function.Injective k →
      μ.map (fun ω => (ν ω, fun i : Fin m => X (k i) ω)) =
        μ.bind fun ω =>
          (Measure.dirac (ν ω)).prod (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure) :
    ConditionallyIIDWithFamily μ X ν :=
  ⟨hν, h⟩

/-- Simp normal form for conditional i.i.d.-ness of a family with a named directing measure. -/
@[simp]
theorem conditionallyIIDWithFamily_iff {μ : Measure Ω} {X : ι → Ω → α}
    {ν : Ω → ProbabilityMeasure α} :
    ConditionallyIIDWithFamily μ X ν ↔
      Measurable ν ∧
        ∀ (m : ℕ) (k : Fin m → ι), Function.Injective k →
          μ.map (fun ω => (ν ω, fun i : Fin m => X (k i) ω)) =
            μ.bind fun ω =>
              (Measure.dirac (ν ω)).prod
                (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure :=
  Iff.rfl

/-- The directing measure of a conditionally i.i.d. family is measurable. -/
@[grind →]
theorem ConditionallyIIDWithFamily.measurable_directing
    {μ : Measure Ω} {X : ι → Ω → α} {ν : Ω → ProbabilityMeasure α}
    (h : ConditionallyIIDWithFamily μ X ν) : Measurable ν :=
  h.1

/-- The joint-law disintegration defining conditional i.i.d.-ness of a family. -/
@[grind =>]
theorem ConditionallyIIDWithFamily.jointLaw_eq_disintegration
    {μ : Measure Ω} {X : ι → Ω → α} {ν : Ω → ProbabilityMeasure α}
    (h : ConditionallyIIDWithFamily μ X ν) {m : ℕ} (k : Fin m → ι)
    (hk : Function.Injective k) :
    μ.map (fun ω => (ν ω, fun i : Fin m => X (k i) ω)) =
      μ.bind fun ω =>
        (Measure.dirac (ν ω)).prod (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure :=
  h.2 m k hk

/-- A conditionally i.i.d. family with a named directing measure is exchangeable. -/
theorem ConditionallyIIDWithFamily.exchangeableFamily
    {μ : Measure Ω} {X : ι → Ω → α} {ν : Ω → ProbabilityMeasure α}
    (h : ConditionallyIIDWithFamily μ X ν) : ExchangeableFamily μ X := by
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

/-- Conditional i.i.d.-ness of a family: existence of a directing measure. -/
def ConditionallyIIDFamily (μ : Measure Ω) (X : ι → Ω → α) : Prop :=
  ∃ ν : Ω → ProbabilityMeasure α, ConditionallyIIDWithFamily μ X ν

/-- Constructor for conditional i.i.d.-ness of a family from a named directing measure. -/
theorem ConditionallyIIDFamily.of_directing {μ : Measure Ω} {X : ι → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : ConditionallyIIDWithFamily μ X ν) :
    ConditionallyIIDFamily μ X :=
  ⟨ν, h⟩

/-- Simp normal form for the existential conditional i.i.d. family predicate. -/
@[simp]
theorem conditionallyIIDFamily_iff {μ : Measure Ω} {X : ι → Ω → α} :
    ConditionallyIIDFamily μ X ↔
      ∃ ν : Ω → ProbabilityMeasure α, ConditionallyIIDWithFamily μ X ν :=
  Iff.rfl

/-- A conditionally i.i.d. family has a directing measure. -/
theorem ConditionallyIIDFamily.exists_directing {μ : Measure Ω} {X : ι → Ω → α}
    (h : ConditionallyIIDFamily μ X) :
    ∃ ν : Ω → ProbabilityMeasure α, ConditionallyIIDWithFamily μ X ν :=
  h

/-- A conditionally i.i.d. family is exchangeable. -/
theorem ConditionallyIIDFamily.exchangeableFamily
    {μ : Measure Ω} {X : ι → Ω → α} (h : ConditionallyIIDFamily μ X) :
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

/-- Conditional i.i.d.-ness with a named directing measure is preserved by reindexing the family
along an injection. The directing measure is unchanged. -/
theorem ConditionallyIIDWithFamily.comp_injective
    {μ : Measure Ω} {X : ι → Ω → α} {ν : Ω → ProbabilityMeasure α}
    (h : ConditionallyIIDWithFamily μ X ν) {f : κ → ι} (hf : Function.Injective f) :
    ConditionallyIIDWithFamily μ (fun j => X (f j)) ν := by
  refine ConditionallyIIDWithFamily.intro h.measurable_directing fun m k hk => ?_
  simpa only [Function.comp_apply] using
    h.jointLaw_eq_disintegration (f ∘ k) (hf.comp hk)

/-- Conditional i.i.d.-ness is preserved by reindexing a family along an injection. -/
theorem ConditionallyIIDFamily.comp_injective
    {μ : Measure Ω} {X : ι → Ω → α} (h : ConditionallyIIDFamily μ X)
    {f : κ → ι} (hf : Function.Injective f) :
    ConditionallyIIDFamily μ fun j => X (f j) :=
  let ⟨_, hν⟩ := h.exists_directing
  ConditionallyIIDFamily.of_directing (hν.comp_injective hf)

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

/-- A conditionally i.i.d. family indexed by `ℕ` is conditionally i.i.d. as a sequence, with the
same directing measure. -/
theorem ConditionallyIIDWithFamily.conditionallyIIDWith
    {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}
    (h : ConditionallyIIDWithFamily μ X ν) : ConditionallyIIDWith μ X ν :=
  ConditionallyIIDWith.intro h.measurable_directing fun _ k hk =>
    h.jointLaw_eq_disintegration k hk

/-- A conditionally i.i.d. sequence is a conditionally i.i.d. family indexed by `ℕ`, with the same
directing measure. -/
theorem ConditionallyIIDWith.conditionallyIIDWithFamily
    {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}
    (h : ConditionallyIIDWith μ X ν) : ConditionallyIIDWithFamily μ X ν :=
  ConditionallyIIDWithFamily.intro h.measurable_directing fun _ k hk =>
    h.jointLaw_eq_disintegration k hk

/-- The named-witness family and sequence conditional i.i.d. predicates agree over `ℕ`. -/
theorem conditionallyIIDWithFamily_iff_conditionallyIIDWith
    {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α} :
    ConditionallyIIDWithFamily μ X ν ↔ ConditionallyIIDWith μ X ν :=
  ⟨ConditionallyIIDWithFamily.conditionallyIIDWith,
    ConditionallyIIDWith.conditionallyIIDWithFamily⟩

/-- A conditionally i.i.d. family indexed by `ℕ` is conditionally i.i.d. as a sequence. -/
theorem ConditionallyIIDFamily.conditionallyIID
    {μ : Measure Ω} {X : ℕ → Ω → α} (h : ConditionallyIIDFamily μ X) :
    ConditionallyIID μ X :=
  let ⟨_, hν⟩ := h.exists_directing
  ConditionallyIID.of_directing hν.conditionallyIIDWith

/-- A conditionally i.i.d. sequence is a conditionally i.i.d. family indexed by `ℕ`. -/
theorem ConditionallyIID.conditionallyIIDFamily
    {μ : Measure Ω} {X : ℕ → Ω → α} (h : ConditionallyIID μ X) :
    ConditionallyIIDFamily μ X :=
  let ⟨_, hν⟩ := h.exists_directing
  ConditionallyIIDFamily.of_directing hν.conditionallyIIDWithFamily

/-- The existential family and sequence conditional i.i.d. predicates agree over `ℕ`. -/
theorem conditionallyIIDFamily_iff_conditionallyIID
    {μ : Measure Ω} {X : ℕ → Ω → α} :
    ConditionallyIIDFamily μ X ↔ ConditionallyIID μ X :=
  ⟨ConditionallyIIDFamily.conditionallyIID, ConditionallyIID.conditionallyIIDFamily⟩

end Probability

end TauCeti
