/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.MixedIID.Basic
-- Non-public: `map_bind` is used only inside the proof below.
import TauCeti.MeasureTheory.Measure.GiryMonad

/-!
# Coordinatewise maps of mixed i.i.d. sequences

This file completes the Layer 0 closure API for the exchangeability symmetry classes: applying a
measurable map `f : α → β` to every coordinate of a mixed i.i.d. process gives another mixed
i.i.d. process, whose mixing representative is the coordinatewise pushforward
`ω ↦ (ν ω).map f` of the original mixing representative `ν`.

`TauCeti.Probability.Exchangeability.Map` already records this closure for `ExchangeableAt`,
`Exchangeable`, `FullyExchangeable`, and `Contractable`.  `MixedIID` is the remaining
symmetry class from the roadmap item asking for closure of each class under the coordinatewise
pushforward `X ↦ (f ∘ Xᵢ)` (`TauCetiRoadmap/Exchangeability/README.md`, Layer 0). The
transformation of the mixing representative is the expected one: the mixture identity for the
mapped process is the original identity with each product factor pushed forward by `f`.

The proof runs at the level of the finite-block mixture identity. It reuses `map_blockLaw`
(the coordinatewise pushforward of a block law), the random-product measurability of
`TauCeti.MeasureTheory.Measure.ProductKernel`, the naturality of `bind`
(`TauCeti.MeasureTheory.map_bind`), and Mathlib's product pushforward `Measure.pi_map_pi`.
It needs no material from `cameronfreer/exchangeability` beyond the existing `MixedIIDWith` API
this repository already carries.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]

/-- Mixed i.i.d.-ness with a named mixing representative is preserved by a coordinatewise
measurable map of the value space: if `X` is mixed i.i.d. with mixing representative `ν`, then
`fun i ω => f (X i ω)` is mixed i.i.d. with mixing representative the coordinatewise
pushforward `fun ω => (ν ω).map f`. -/
theorem MixedIIDWith.map_values {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : MixedIIDWith μ X ν)
    {f : α → β} (hf : Measurable f) (hX : ∀ i, AEMeasurable (X i) μ) :
    MixedIIDWith μ (fun i ω => f (X i ω)) fun ω => (ν ω).map hf.aemeasurable := by
  refine MixedIIDWith.intro ?_ ?_
  · -- The pushforward mixing representative is measurable in the Giry structure.
    have hν : Measurable fun ω => (ν ω : Measure α) :=
      measurable_subtype_coe.comp h.measurable_mixingRepresentative
    exact ((Measure.measurable_map f hf).comp hν).subtype_mk
  · intro m k hk
    have hXk : ∀ i : Fin m, AEMeasurable (X (k i)) μ := fun i => hX (k i)
    have hFmeas : Measurable fun x : Fin m → α => fun i => f (x i) :=
      measurable_pi_lambda _ fun i => hf.comp (measurable_pi_apply i)
    have hg : AEMeasurable
        (fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure) μ :=
      MeasureTheory.aemeasurable_probabilityMeasure_pi_toMeasure_of_measurable (fun _ : Fin m => ν)
        (fun _ => h.measurable_mixingRepresentative)
    calc
      blockLaw μ (fun i ω => f (X i ω)) k
          = (blockLaw μ X k).map fun x : Fin m → α => fun i => f (x i) :=
            (map_blockLaw μ k hf hXk).symm
      _ = (μ.bind fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure).map
            fun x : Fin m → α => fun i => f (x i) := by rw [h.blockLaw_eq_mixture k hk]
      _ = μ.bind fun ω =>
            ((ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure).map
              fun x : Fin m → α => fun i => f (x i) := TauCeti.MeasureTheory.map_bind hg hFmeas
      _ = μ.bind fun ω =>
            (ProbabilityMeasure.pi fun _ : Fin m => (ν ω).map hf.aemeasurable).toMeasure := by
            refine congrArg (μ.bind ·) (funext fun ω => ?_)
            haveI : IsProbabilityMeasure ((ν ω : Measure α).map f) :=
              (ν ω : Measure α).isProbabilityMeasure_map hf.aemeasurable
            simp only [ProbabilityMeasure.toMeasure_pi, ProbabilityMeasure.toMeasure_map]
            exact Measure.pi_map_pi fun _ : Fin m => hf.aemeasurable

/-- Mixed i.i.d.-ness is preserved by a coordinatewise measurable map of the value space. -/
theorem MixedIID.map_values {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : MixedIID μ X) {f : α → β} (hf : Measurable f) (hX : ∀ i, AEMeasurable (X i) μ) :
    MixedIID μ (fun i ω => f (X i ω)) := by
  obtain ⟨ν, hν⟩ := h.exists_mixingRepresentative
  exact MixedIID.of_mixingRepresentative (hν.map_values hf hX)

/-- **Transfer of mixed i.i.d.-ness along the path law.** If the coordinate process on path
space is mixed i.i.d. under `pathLaw μ X`, then `X` is mixed i.i.d. under `μ`. -/
theorem mixedIID_of_mixedIID_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_meas : ∀ n, Measurable (X n))
    (h : MixedIID (pathLaw μ X) fun n p => p n) :
    MixedIID μ X := by
  obtain ⟨ν, hν⟩ := h.exists_mixingRepresentative
  have hφ : Measurable (fun ω => fun i => X i ω : Ω → ℕ → α) := measurable_pi_lambda _ hX_meas
  refine MixedIID.of_mixingRepresentative
    (MixedIIDWith.intro (hν.measurable_mixingRepresentative.comp hφ) ?_)
  intro m k hk
  have hcoord : Measurable (fun p : ℕ → α => fun i : Fin m => p (k i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (k i)
  have hg : Measurable
      (fun p : ℕ → α => (ProbabilityMeasure.pi fun _ : Fin m => ν p).toMeasure) :=
    TauCeti.MeasureTheory.measurable_probabilityMeasure_pi_const_toMeasure ν
      hν.measurable_mixingRepresentative
  calc blockLaw μ X k
      = blockLaw (pathLaw μ X) (fun n p => p n) k := by
          simp only [blockLaw_def, pathLaw_def]
          rw [Measure.map_map hcoord hφ]
          rfl
    _ = (pathLaw μ X).bind fun p => (ProbabilityMeasure.pi fun _ : Fin m => ν p).toMeasure :=
          hν.blockLaw_eq_mixture k hk
    _ = μ.bind fun ω =>
          (ProbabilityMeasure.pi fun _ : Fin m => ν (fun i => X i ω)).toMeasure := by
          simp only [pathLaw_def, Measure.bind]
          rw [Measure.map_map hg hφ]
          rfl

end Probability

end TauCeti
