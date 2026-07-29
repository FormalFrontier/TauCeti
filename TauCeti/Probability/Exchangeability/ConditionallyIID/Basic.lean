/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.MixedIID.Basic
-- Non-public: `map_bind` is used only inside the projection proof.
import TauCeti.MeasureTheory.Measure.GiryMonad

/-!
# Conditionally i.i.d. sequences

The **conditional** strengthening of the mixture identity: a process is *conditionally i.i.d.*
with directing measure `ν` when, along every finite selection of distinct coordinates, the
**joint** law of `(ν, block)` is the disintegration `∫ δ_{ν ω} ⊗ (ν ω)^{⊗m} dμ(ω)` — conditionally
on `ν`, the block is i.i.d. `ν` (Kallenberg 2005, §1.1 eq. (2)).

Stating it as a joint-law identity means the definition needs no conditional expectations, and
sits in the same `bind`/`pi` vocabulary as `MixedIIDWith`.

## Why this is stronger than `MixedIIDWith`

`MixedIIDWith μ X ν` constrains only each block's **marginal** law. It therefore does not pin down
how `X` relates to `ν`: for a nondegenerate mixing law, an *independent copy* of a directing
measure also witnesses `MixedIIDWith`, while the process is not conditionally i.i.d. given that
copy. The arrow runs one way only, and `mixedIIDWith_of_conditionallyIIDWith` is that arrow —
obtained by integrating the `ν` coordinate out.

Terminology follows the roadmap: a `ν` witnessing only the mixture identity is a *mixing
representative*, whereas `ν` here is a genuine **directing measure**.

## Main results

* `ConditionallyIIDWith`, `ConditionallyIID` — the predicate and its existential wrapper, with
  their constructor, accessor, and simp-normal-form API.
* `mixedIIDWith_of_conditionallyIIDWith`, `mixedIID_of_conditionallyIID` — the easy projection down
  to the mixture identity.

This is a **Layer 0** contribution to `TauCetiRoadmap/Exchangeability/README.md` — the conditional
predicate for which the roadmap reserves the `ConditionallyIID` name, together with the easy
projection it pins alongside — which consumes the already-landed Layer 1 joint-kernel lemma
`measurable_dirac_prod_probabilityMeasure_pi_const_toMeasure`.

The Layer 1 joint-rectangle common ending `conditionallyIID_of_jointRectangles` lives in
`TauCeti.Probability.DeFinetti.ConditionalCommonEnding`. Still open here are the Layer 6 summit
theorems that *conclude* this predicate, `conditionallyIID_of_contractable` and
`conditionallyIID_of_exchangeable`; the `deFinetti*` handles that return with them; and
directing-measure uniqueness (`conditionallyIID_ae_unique`).
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Conditional i.i.d.-ness with a specified directing measure `ν`: the random measure `ν` is
measurable, and along every finite selection `k` of **distinct** coordinates the *joint* law of
`(ν, block)` is the `ν`-disintegration `∫ δ_{ν ω} ⊗ (ν ω)^{⊗m} dμ(ω)`.

Constraining the joint law, rather than just the block's marginal, is exactly what makes this the
conditional statement: see `MixedIIDWith` for the marginal-only version and
`mixedIIDWith_of_conditionallyIIDWith` for the arrow between them. -/
def ConditionallyIIDWith (μ : Measure Ω) (X : ℕ → Ω → α) (ν : Ω → ProbabilityMeasure α) : Prop :=
  Measurable ν ∧
    ∀ (m : ℕ) (k : Fin m → ℕ), Function.Injective k →
      μ.map (fun ω => (ν ω, fun i : Fin m => X (k i) ω)) =
        μ.bind fun ω =>
          (Measure.dirac (ν ω)).prod (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure

/-- Constructor: a measurable directing measure together with the joint-law disintegration. -/
theorem ConditionallyIIDWith.intro {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}
    (hν : Measurable ν)
    (h : ∀ (m : ℕ) (k : Fin m → ℕ), Function.Injective k →
      μ.map (fun ω => (ν ω, fun i : Fin m => X (k i) ω)) =
        μ.bind fun ω =>
          (Measure.dirac (ν ω)).prod (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure) :
    ConditionallyIIDWith μ X ν :=
  ⟨hν, h⟩

/-- Simp normal form for `ConditionallyIIDWith`. -/
@[simp]
theorem conditionallyIIDWith_iff {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} :
    ConditionallyIIDWith μ X ν ↔
      Measurable ν ∧
        ∀ (m : ℕ) (k : Fin m → ℕ), Function.Injective k →
          μ.map (fun ω => (ν ω, fun i : Fin m => X (k i) ω)) =
            μ.bind fun ω =>
              (Measure.dirac (ν ω)).prod
                (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure :=
  Iff.rfl

/-- Conditional i.i.d.-ness: existence of a directing measure. -/
def ConditionallyIID (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∃ ν : Ω → ProbabilityMeasure α, ConditionallyIIDWith μ X ν

/-- Constructor from a directing measure together with its witness. -/
theorem ConditionallyIID.of_directing {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : ConditionallyIIDWith μ X ν) : ConditionallyIID μ X :=
  ⟨ν, h⟩

/-- Simp normal form for the existential wrapper `ConditionallyIID`. -/
@[simp]
theorem conditionallyIID_iff {μ : Measure Ω} {X : ℕ → Ω → α} :
    ConditionallyIID μ X ↔ ∃ ν : Ω → ProbabilityMeasure α, ConditionallyIIDWith μ X ν :=
  Iff.rfl

/-- The directing measure of a `ConditionallyIIDWith` witness is measurable. -/
@[grind →]
theorem ConditionallyIIDWith.measurable_directing {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : ConditionallyIIDWith μ X ν) : Measurable ν :=
  h.1

/-- The defining joint-law disintegration of a `ConditionallyIIDWith` witness. -/
@[grind =>]
theorem ConditionallyIIDWith.jointLaw_eq_disintegration {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : ConditionallyIIDWith μ X ν)
    {m : ℕ} (k : Fin m → ℕ) (hk : Function.Injective k) :
    μ.map (fun ω => (ν ω, fun i : Fin m => X (k i) ω)) =
      μ.bind fun ω =>
        (Measure.dirac (ν ω)).prod (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure :=
  h.2 m k hk

/-- A `ConditionallyIID` process has a directing measure. -/
theorem ConditionallyIID.exists_directing {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : ConditionallyIID μ X) :
    ∃ ν : Ω → ProbabilityMeasure α, ConditionallyIIDWith μ X ν :=
  h

/-- **The easy arrow.** A directing measure is in particular a mixing representative: the mixture
identity is the joint disintegration with the `ν` coordinate integrated out.

Taking the second marginal of both sides does exactly that. On the left, `Measure.snd_map_prodMk₀`
discards the `ν` coordinate needing only measurability of `ν` itself — which the predicate
supplies — so no hypothesis on the coordinates of `X` is required. On the right, naturality of
`bind` pushes the marginal inside the mixture, where each `δ_{ν ω}` factor integrates away. -/
theorem mixedIIDWith_of_conditionallyIIDWith {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : ConditionallyIIDWith μ X ν) : MixedIIDWith μ X ν := by
  refine MixedIIDWith.intro h.measurable_directing fun m k hk => ?_
  have hK : AEMeasurable (fun ω =>
      (Measure.dirac (ν ω)).prod (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure) μ :=
    (TauCeti.MeasureTheory.measurable_dirac_prod_probabilityMeasure_pi_const_toMeasure ν
      h.measurable_directing).aemeasurable
  calc blockLaw μ X k
      = (μ.map fun ω => (ν ω, fun i : Fin m => X (k i) ω)).snd := by
        rw [blockLaw_def, Measure.snd_map_prodMk₀ h.measurable_directing.aemeasurable]
    _ = (μ.bind fun ω => (Measure.dirac (ν ω)).prod
          (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure).snd := by
        rw [h.jointLaw_eq_disintegration k hk]
    _ = μ.bind fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure := by
        simp only [Measure.snd]
        rw [TauCeti.MeasureTheory.map_bind hK measurable_snd]
        simp

/-- The existential form of the easy arrow. -/
theorem mixedIID_of_conditionallyIID {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : ConditionallyIID μ X) : MixedIID μ X := by
  obtain ⟨ν, hν⟩ := h.exists_directing
  exact MixedIID.of_mixingRepresentative (mixedIIDWith_of_conditionallyIIDWith hν)

end Probability

end TauCeti
