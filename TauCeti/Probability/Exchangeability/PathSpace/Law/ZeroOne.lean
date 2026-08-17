/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.PathSpace.HewittSavage
public import TauCeti.Probability.DeFinetti.BlockFactorization
public import TauCeti.Probability.Exchangeability.MixedIID.Mixture
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Ext
import TauCeti.Probability.Exchangeability.PathSpace.Exchangeable.ToContractable

/-!
# The zero-one characterization of product laws

An exchangeable law on `ℕ → α` has trivial exchangeable σ-algebra exactly when it is an infinite
product law:

`exchangeableSigma_trivial_iff_iid`.

## The two directions

The product-to-zero-one direction is Hewitt–Savage, packaged for the product law itself as
`exchangeableSigma_trivial_of_infinitePi`.

The converse is the substantive half, and it runs at the level of the *mixing law* rather than the
directing map. The canonical witness `directingProbabilityMeasure` is `tailProcess`-measurable, and
`pathTail_le_exchangeableSigma` puts the path tail inside `exchangeableSigma`, so every preimage
`ν ⁻¹' A` is an exchangeable event. Triviality therefore makes `ρ.map ν` a zero-one measure on
`ProbabilityMeasure α`, hence a Dirac measure by
`IsZeroOneMeasure.exists_eq_dirac_probabilityMeasure`, and the de Finetti mixture representation
`pathLaw_eq_bind_infinitePi_of_mixedIIDWith` collapses to a single product.

Working at the mixing-law level avoids needing a general "measurable into `ProbabilityMeasure α`
implies almost everywhere constant" interface: the Giry-specific Dirac theorem is exactly the tool
for this situation. Note that `mixedIID_mixingLaw_unique` alone does *not* give the converse —
uniqueness of the mixing law is not the same as its being a point mass.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 6, the
  `exchangeableSigma_trivial_iff_iid` interface among the equivalent characterizations of product
  laws.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- **A trivial exchangeable σ-algebra forces an i.i.d. law.** If every exchangeable event has
probability `0` or `1` under an exchangeable law `ρ`, then `ρ` is an infinite product `P^{⊗ℕ}`. -/
theorem infinitePi_of_exchangeableSigma_trivial [StandardBorelSpace α]
    {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ] (hρ : ExchangeableLaw ρ)
    (htriv : ∀ s, MeasurableSet[exchangeableSigma α] s → ρ s = 0 ∨ ρ s = 1) :
    ∃ P : ProbabilityMeasure α, ρ = Measure.infinitePi fun _ : ℕ => (P : Measure α) := by
  have : Nonempty α := (nonempty_of_isProbabilityMeasure ρ).map fun x => x 0
  have hcoord : ∀ n, Measurable (fun x : ℕ → α => x n) := fun n => measurable_pi_apply n
  have hpath : pathLaw ρ (fun n (x : ℕ → α) => x n) = ρ := by simp [pathLaw_def]
  have hexch : Exchangeable ρ (fun n (x : ℕ → α) => x n) :=
    (exchangeable_iff_exchangeableLaw_pathLaw fun n => (hcoord n).aemeasurable).2
      (by simpa [pathLaw_def] using hρ)
  have hmix : MixedIIDWith ρ (fun n (x : ℕ → α) => x n)
      (directingProbabilityMeasure ρ fun n (x : ℕ → α) => x n) :=
    mixedIIDWith_of_contractable (hexch.contractable fun n => (hcoord n).aemeasurable) hcoord
  set ν := directingProbabilityMeasure ρ fun n (x : ℕ → α) => x n with hν
  have hν_meas : Measurable ν := hmix.measurable_mixingRepresentative
  -- Preimages under the canonical witness are exchangeable events.
  have hpre : ∀ {A : Set (ProbabilityMeasure α)}, MeasurableSet A →
      MeasurableSet[exchangeableSigma α] (ν ⁻¹' A) := by
    intro A hA
    have htail : MeasurableSet[tailProcess fun n (x : ℕ → α) => x n] (ν ⁻¹' A) :=
      measurable_tailProcess_directingProbabilityMeasure hA
    exact pathTail_le_exchangeableSigma _ (by rwa [pathTail_eq_tailProcess])
  have hprob : IsProbabilityMeasure (ρ.map ν) :=
    Measure.isProbabilityMeasure_map hν_meas.aemeasurable
  have hzo : IsZeroOneMeasure (ρ.map ν) :=
    ⟨fun A hA => by rw [Measure.map_apply hν_meas hA]; exact htriv _ (hpre hA)⟩
  obtain ⟨P, hP⟩ :=
    TauCeti.MeasureTheory.IsZeroOneMeasure.exists_eq_dirac_probabilityMeasure (π := ρ.map ν)
  refine ⟨P, ?_⟩
  calc ρ = pathLaw ρ (fun n (x : ℕ → α) => x n) := hpath.symm
    _ = (ρ.map ν).bind fun Q => Measure.infinitePi fun _ : ℕ => (Q : Measure α) :=
        pathLaw_eq_bind_infinitePi_of_mixedIIDWith (fun n => (hcoord n).aemeasurable) hmix
    _ = Measure.infinitePi fun _ : ℕ => (P : Measure α) := by
        rw [hP, Measure.dirac_bind TauCeti.MeasureTheory.measurable_infinitePi_const]

/-- **The zero-one characterization of product laws.** For a standard Borel state space, an
exchangeable probability law on `ℕ → α` has trivial exchangeable σ-algebra exactly when it is an
infinite product law. -/
theorem exchangeableSigma_trivial_iff_iid [StandardBorelSpace α]
    {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ] (hρ : ExchangeableLaw ρ) :
    (∀ s, MeasurableSet[exchangeableSigma α] s → ρ s = 0 ∨ ρ s = 1) ↔
      ∃ P : ProbabilityMeasure α, ρ = Measure.infinitePi fun _ : ℕ => (P : Measure α) := by
  refine ⟨infinitePi_of_exchangeableSigma_trivial hρ, ?_⟩
  rintro ⟨P, rfl⟩ s hs
  exact exchangeableSigma_trivial_of_infinitePi P hs

end Probability

end TauCeti

end

end
