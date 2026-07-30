/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.Basic
public import TauCeti.MeasureTheory.Measure.ProductKernel

/-!
# Mixed i.i.d. families

A family is *mixed i.i.d.* when there is a measurable random probability measure
`ν : Ω → ProbabilityMeasure α` such that every finite block of **distinct** coordinates has, as
its law, the `ν`-mixture of the corresponding product measure. `MixedIIDWith μ X ν` names the
witness `ν`; `MixedIID` is the existential wrapper.

⚠ This is a property of the **unconditional** finite-dimensional laws: the mixture identity
constrains each finite block's marginal law, never the joint law of `(ν, X)`. It is therefore
*not* conditional independence, and is deliberately not named `ConditionallyIID` — that name
belongs to the genuine joint-law disintegration
`Law(ν, block) = ∫ δ_{ν ω} ⊗ (ν ω)^{⊗m} dμ(ω)` (Kallenberg 2005, §1.1 eq. (2)), which strictly
strengthens the identity below at a fixed `ν`: for a nondegenerate mixing law an *independent
copy* of a directing measure also witnesses `MixedIIDWith`, while the family is not
conditionally i.i.d. given it. Following the roadmap's terminology, a `ν` witnessing only the
mixture identity is a **mixing representative**; *directing measure* is reserved for the
conditional predicate's witness.

The index type is arbitrary, matching `ConditionallyIIDWith`: the definition quantifies only over
injective selections `Fin m → ι`, and nothing in it uses the order structure of `ℕ`. Sequence-level
users get the `ι = ℕ` case by unification. The *consequences* over `ℕ` — `prefixLaw_eq_mixture`,
`blockLaw_eq_prefixLaw_of_injective`, exchangeability and contractability, the path-law
representation, and mixing-law uniqueness — remain sequence-level, because those genuinely use
prefixes, shifts, or `ℕ`-indexed products.

This file adds the Layer 0 mixed-i.i.d. definitions and destructors, together with the Layer 1
rectangle-factorization characterization used by the common de Finetti ending. The
exchangeability implications live in `MixedIID/Implications.lean`.

These declarations follow the roadmap signatures in
`TauCetiRoadmap/Exchangeability/README.md` and
`TauCetiRoadmap/Exchangeability/Suggested.lean`, Layer 0, refining the existential
`MixedIID` of the roadmap into a named-witness relation (`MixedIIDWith`) plus its existential
wrapper. They are adapted from the `cameronfreer/exchangeability` Layer 0 sources pinned at
`e0532e59ceff23edab44dda9ab0655debbc9cc22`, with Tau Ceti API names and hypotheses.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace Probability

variable {Ω α ι κ : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Implementation helper for the rectangle characterization: two measures on a finite product
space are equal if they agree on all measurable rectangles `Set.univ.pi B`. Only the first measure
is assumed finite. -/
private theorem measure_eq_of_forall_univ_pi {ι : Type*} [Finite ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] {μ ν : Measure (∀ i, α i)} [IsFiniteMeasure μ]
    (h : ∀ B : ∀ i, Set (α i), (∀ i, MeasurableSet (B i)) →
      μ (Set.univ.pi B) = ν (Set.univ.pi B)) :
    μ = ν := by
  letI := Fintype.ofFinite ι
  refine Measure.ext_of_generateFrom_of_iUnion
    (C := Set.pi Set.univ '' Set.pi Set.univ fun i => {s : Set (α i) | MeasurableSet s})
    (B := fun _ : ℕ => Set.univ) generateFrom_pi.symm isPiSystem_pi ?_ ?_ ?_ ?_
  · simpa using (iUnion_const (Set.univ : Set (∀ i, α i)))
  · intro n
    exact ⟨fun _ => Set.univ, fun i _ => MeasurableSet.univ, by simp⟩
  · intro n
    exact measure_ne_top μ Set.univ
  · rintro _ ⟨B, hB, rfl⟩
    exact h B fun i => hB i (mem_univ i)

/-- Mixed i.i.d.-ness with a specified mixing representative `ν`: the random
measure `ν` is measurable, and along every finite selection `k` of **distinct** coordinates
the block law is the `ν`-mixture of the product measure
`ProbabilityMeasure.pi (fun _ => ν ω)`. Distinctness (`Function.Injective k`) is what product
laws need, in contrast with the order condition `StrictMono` of `Contractable`. -/
def MixedIIDWith (μ : Measure Ω) (X : ι → Ω → α) (ν : Ω → ProbabilityMeasure α) :
    Prop :=
  Measurable ν ∧
    ∀ (m : ℕ) (k : Fin m → ι), Function.Injective k →
      blockLaw μ X k = μ.bind fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure

/-- Constructor: a measurable mixing representative together with the finite-block mixture
identity. -/
theorem MixedIIDWith.intro {μ : Measure Ω} {X : ι → Ω → α} {ν : Ω → ProbabilityMeasure α}
    (hν : Measurable ν)
    (h : ∀ (m : ℕ) (k : Fin m → ι), Function.Injective k →
      blockLaw μ X k = μ.bind fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure) :
    MixedIIDWith μ X ν :=
  ⟨hν, h⟩

/-- Simp normal form for `MixedIIDWith`. -/
@[simp]
theorem mixedIIDWith_iff {μ : Measure Ω} {X : ι → Ω → α} {ν : Ω → ProbabilityMeasure α} :
    MixedIIDWith μ X ν ↔
      Measurable ν ∧
        ∀ (m : ℕ) (k : Fin m → ι), Function.Injective k →
          blockLaw μ X k = μ.bind fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure :=
  Iff.rfl

/-- Mixed i.i.d.-ness: existence of a mixing representative. -/
def MixedIID (μ : Measure Ω) (X : ι → Ω → α) : Prop :=
  ∃ ν : Ω → ProbabilityMeasure α, MixedIIDWith μ X ν

/-- Constructor from a mixing representative together with its witness. -/
theorem MixedIID.of_mixingRepresentative {μ : Measure Ω} {X : ι → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : MixedIIDWith μ X ν) : MixedIID μ X :=
  ⟨ν, h⟩

/-- Simp normal form for the existential wrapper `MixedIID`. -/
@[simp]
theorem mixedIID_iff {μ : Measure Ω} {X : ι → Ω → α} :
    MixedIID μ X ↔ ∃ ν : Ω → ProbabilityMeasure α, MixedIIDWith μ X ν :=
  Iff.rfl

/-- The mixing representative of a `MixedIIDWith` witness is measurable. -/
@[grind →]
theorem MixedIIDWith.measurable_mixingRepresentative {μ : Measure Ω} {X : ι → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : MixedIIDWith μ X ν) : Measurable ν :=
  h.1

/-- The defining finite-block mixture identity of a `MixedIIDWith` witness: along an injective
selection the block law is the `ν`-mixture of the product measure. The prefix specialization is
`MixedIIDWith.prefixLaw_eq_mixture`. -/
@[grind =>]
theorem MixedIIDWith.blockLaw_eq_mixture {μ : Measure Ω} {X : ι → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : MixedIIDWith μ X ν)
    {m : ℕ} (k : Fin m → ι) (hk : Function.Injective k) :
    blockLaw μ X k = μ.bind fun ω => (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure :=
  h.2 m k hk

/-- A `MixedIID` family has a mixing representative. -/
theorem MixedIID.exists_mixingRepresentative {μ : Measure Ω} {X : ι → Ω → α}
    (h : MixedIID μ X) :
    ∃ ν : Ω → ProbabilityMeasure α, MixedIIDWith μ X ν :=
  h

/-- A family is `MixedIIDWith μ X ν` once every injective finite block has the same
rectangle values as the corresponding random product-measure mixture. -/
theorem mixedIIDWith_of_forall_rectangles {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ι → Ω → α} {ν : Ω → ProbabilityMeasure α} (hν : Measurable ν)
    (h_rect : ∀ (m : ℕ) (k : Fin m → ι), Function.Injective k →
      ∀ B : Fin m → Set α, (∀ i, MeasurableSet (B i)) →
        blockLaw μ X k (Set.univ.pi B) =
          ∫⁻ ω, ∏ i : Fin m, (ν ω : Measure α) (B i) ∂μ) :
    MixedIIDWith μ X ν := by
  refine MixedIIDWith.intro hν ?_
  intro m k hk
  haveI : IsFiniteMeasure (blockLaw μ X k) := by
    rw [blockLaw_def]
    infer_instance
  refine measure_eq_of_forall_univ_pi ?_
  intro B hB
  rw [h_rect m k hk B hB]
  rw [TauCeti.MeasureTheory.bind_probabilityMeasure_pi_const_pi ν hν.aemeasurable B hB]

/-- A `MixedIIDWith` witness gives the expected rectangle factorization for every injective
finite block. -/
@[grind =>]
theorem MixedIIDWith.blockLaw_univ_pi {μ : Measure Ω} {X : ι → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : MixedIIDWith μ X ν)
    {m : ℕ} (k : Fin m → ι) (hk : Function.Injective k)
    (B : Fin m → Set α) (hB : ∀ i, MeasurableSet (B i)) :
    blockLaw μ X k (Set.univ.pi B) =
      ∫⁻ ω, ∏ i : Fin m, (ν ω : Measure α) (B i) ∂μ := by
  rw [h.blockLaw_eq_mixture k hk]
  have hν_ae : AEMeasurable ν μ := h.measurable_mixingRepresentative.aemeasurable
  rw [TauCeti.MeasureTheory.bind_probabilityMeasure_pi_const_pi ν hν_ae B hB]

/-- Rectangle factorization is equivalent to the named `MixedIIDWith` relation. -/
theorem mixedIIDWith_iff_forall_rectangles {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ι → Ω → α} {ν : Ω → ProbabilityMeasure α} :
    MixedIIDWith μ X ν ↔
      Measurable ν ∧
        ∀ (m : ℕ) (k : Fin m → ι), Function.Injective k →
          ∀ B : Fin m → Set α, (∀ i, MeasurableSet (B i)) →
            blockLaw μ X k (Set.univ.pi B) =
              ∫⁻ ω, ∏ i : Fin m, (ν ω : Measure α) (B i) ∂μ := by
  constructor
  · intro h
    exact ⟨h.measurable_mixingRepresentative, fun m k hk B hB => h.blockLaw_univ_pi k hk B hB⟩
  · rintro ⟨hν, h_rect⟩
    exact mixedIIDWith_of_forall_rectangles hν h_rect

/-- Rectangle factorization is equivalent to the existential `MixedIID` relation. -/
theorem mixedIID_iff_exists_forall_rectangles {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ι → Ω → α} :
    MixedIID μ X ↔
      ∃ ν : Ω → ProbabilityMeasure α, Measurable ν ∧
        ∀ (m : ℕ) (k : Fin m → ι), Function.Injective k →
          ∀ B : Fin m → Set α, (∀ i, MeasurableSet (B i)) →
            blockLaw μ X k (Set.univ.pi B) =
              ∫⁻ ω, ∏ i : Fin m, (ν ω : Measure α) (B i) ∂μ := by
  simp_rw [mixedIID_iff, mixedIIDWith_iff_forall_rectangles]

/-- **Reindexing a mixing representative along an injection.** A finite injective selection from the
reindexed family is a finite injective selection from the original, so the mixture identity is
inherited with the same witness. -/
theorem MixedIIDWith.comp_injective {μ : Measure Ω} {X : ι → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : MixedIIDWith μ X ν) {f : κ → ι}
    (hf : Function.Injective f) : MixedIIDWith μ (fun j => X (f j)) ν := by
  refine MixedIIDWith.intro h.measurable_mixingRepresentative fun m k hk => ?_
  simpa only [blockLaw_def, Function.comp_apply] using
    h.blockLaw_eq_mixture (f ∘ k) (hf.comp hk)

/-- **Reindexing a mixed i.i.d. family along an injection**, existential form. -/
theorem MixedIID.comp_injective {μ : Measure Ω} {X : ι → Ω → α} (h : MixedIID μ X) {f : κ → ι}
    (hf : Function.Injective f) : MixedIID μ (fun j => X (f j)) :=
  let ⟨_, hν⟩ := h.exists_mixingRepresentative
  MixedIID.of_mixingRepresentative (hν.comp_injective hf)

end Probability

end TauCeti
