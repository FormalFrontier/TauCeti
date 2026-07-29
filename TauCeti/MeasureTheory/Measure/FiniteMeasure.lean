/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.SetAlgebra
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

/-!
# Measurable singletons in spaces of finite measures

When the underlying σ-algebra is countably generated, singletons are measurable in
`FiniteMeasure α` and in `ProbabilityMeasure α`.

## Main results

* `MeasureTheory.FiniteMeasure.instMeasurableSingletonClass`
* `MeasureTheory.ProbabilityMeasure.instMeasurableSingletonClass`

## Implementation

The statement is really about *finite* measures; the probability-measure form is the subtype
corollary. Countable generation is exactly what the proof consumes — `StandardBorelSpace α` implies
it, but is stronger than needed.

A countable generating family need not be closed under intersection, so it is replaced by the set
algebra it generates (`MeasureTheory.generateSetAlgebra`), which is still countable, is a π-system,
and generates the same σ-algebra. A finite measure is then pinned down by its values there
(`ext_of_generate_finite`, with `Set.univ` supplied by the algebra), so `{μ}` is the countable
intersection of the equalizers `{ν | ν s = μ s}`. Each equalizer is measurable because evaluation at
a fixed measurable set is.
-/

public section

noncomputable section

open MeasureTheory MeasurableSpace Set

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- Evaluation at a fixed measurable set is measurable on `FiniteMeasure α`. Private: it exists
only to prove the instance below. -/
private theorem FiniteMeasure.measurable_coe_toMeasure {s : Set α} (hs : MeasurableSet s) :
    Measurable fun ν : FiniteMeasure α => (ν : Measure α) s :=
  (Measure.measurable_coe hs).comp measurable_subtype_coe

/-- **Singletons are measurable in the space of finite measures**, when the σ-algebra on `α` is
countably generated. -/
instance FiniteMeasure.instMeasurableSingletonClass [CountablyGenerated α] :
    MeasurableSingletonClass (FiniteMeasure α) where
  measurableSet_singleton μ := by
    classical
    set 𝒜 := generateSetAlgebra (countableGeneratingSet α) with h𝒜
    have hcount : 𝒜.Countable :=
      countable_generateSetAlgebra countable_countableGeneratingSet
    have halg : IsSetAlgebra 𝒜 := isSetAlgebra_generateSetAlgebra
    have hgen : ‹MeasurableSpace α› = generateFrom 𝒜 := by
      rw [h𝒜, generateFrom_generateSetAlgebra_eq, generateFrom_countableGeneratingSet]
    have hmeas : ∀ s ∈ 𝒜, MeasurableSet s := fun s hs => hgen ▸ measurableSet_generateFrom hs
    have hset : ({μ} : Set (FiniteMeasure α))
        = ⋂ s ∈ 𝒜, {ν : FiniteMeasure α | (ν : Measure α) s = (μ : Measure α) s} := by
      ext ν
      simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
      refine ⟨fun h s _ => by rw [h], fun h => ?_⟩
      haveI := ν.2
      refine Subtype.ext ?_
      exact ext_of_generate_finite 𝒜 hgen
        (fun s hs t ht _ => halg.inter_mem hs ht) (fun s hs => h s hs) (h _ halg.univ_mem)
    rw [hset]
    exact MeasurableSet.biInter hcount fun s hs =>
      (FiniteMeasure.measurable_coe_toMeasure (hmeas s hs)) (measurableSet_singleton _)

/-- **Singletons are measurable in the space of probability measures**, when the σ-algebra on `α`
is countably generated. Pulled back from the finite-measure instance along the injective measurable
map `ProbabilityMeasure.toFiniteMeasure`, so the argument is not repeated. -/
instance ProbabilityMeasure.instMeasurableSingletonClass [CountablyGenerated α] :
    MeasurableSingletonClass (ProbabilityMeasure α) where
  measurableSet_singleton μ := by
    have hmap : Measurable (ProbabilityMeasure.toFiniteMeasure (Ω := α)) :=
      measurable_subtype_coe.subtype_mk
    have hpre : ({μ} : Set (ProbabilityMeasure α))
        = ProbabilityMeasure.toFiniteMeasure ⁻¹' {μ.toFiniteMeasure} := by
      ext ν
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => by rw [h], fun h =>
        Subtype.ext (congrArg (fun x : FiniteMeasure α => (x : Measure α)) h)⟩
    rw [hpre]
    exact hmap (measurableSet_singleton _)


end MeasureTheory
