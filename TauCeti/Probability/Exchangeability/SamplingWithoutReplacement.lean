/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.ExchangeableAtMonotone
public import TauCeti.Probability.UniformSampling
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Finite exchangeability as sampling without replacement

This file identifies every shorter marginal of a finite exchangeable process with sampling
without replacement from its observed finite population. Given a population law
`ρ : Measure (κ → α)`, `sampleWithoutReplacement ρ` first draws `x ∼ ρ`, independently
draws a uniform injective selection `k : ι → κ`, and returns `x ∘ k`.

The main theorem says that if the first `n` coordinates of a process are exchangeable, then
sampling `m ≤ n` entries without replacement from that random `n`-tuple has exactly the original
`m`-prefix law. This is the representation half of the finite de Finetti argument: the companion
with-replacement law is the product of the empirical measure, and the collision estimate in
`TauCeti.Probability.UniformSampling` then controls their difference.

The proof averages the exchangeable law over all injective selections. Every selection has the
same law by `ExchangeableAt.blockLaw_eq_prefixLaw_of_injective`, so the average has that law too.

## Main declarations

* `sampleWithoutReplacement` — sample a random finite population at uniformly chosen distinct
  indices;
* `sampleWithoutReplacement_apply` — its evaluation as the average of the selected laws;
* `ExchangeableAt.sampleWithoutReplacement_eq_prefixLaw` — the finite exchangeable
  without-replacement representation.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 8, “finite de Finetti bounds”.
* P. Diaconis and D. Freedman, “Finite exchangeable sequences”, *Annals of Probability* 8
  (1980), 745–764.

No material is adapted from `cameronfreer/exchangeability`; its three de Finetti routes concern
infinite exchangeable sequences rather than quantitative finite approximation.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- Reindex a finite population by a simultaneously supplied selection of its indices.

This lemma is private because the function is only the implementation map in
`sampleWithoutReplacement`. The measurable-space hypothesis on the finite population index is
discrete: it lets the variable index be split into countably many measurable fibres. -/
private theorem measurable_samplePopulation {ι κ : Type*} [Countable κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] :
    Measurable (fun p : (ι → κ) × (κ → α) => fun i : ι => p.2 (p.1 i)) := by
  refine measurable_pi_lambda _ fun i => ?_
  intro s hs
  rw [show (fun p : (ι → κ) × (κ → α) => p.2 (p.1 i)) ⁻¹' s =
      ⋃ j : κ, {p | p.1 i = j} ∩ {p | p.2 j ∈ s} by ext p; simp]
  refine MeasurableSet.iUnion fun j => ?_
  have hselection : MeasurableSet
      ((fun p : (ι → κ) × (κ → α) => p.1 i) ⁻¹' {j}) :=
    ((measurable_pi_apply i).comp measurable_fst) (measurableSet_singleton j)
  have hpopulation : MeasurableSet
      ((fun p : (ι → κ) × (κ → α) => p.2 j) ⁻¹' s) :=
    ((measurable_pi_apply j).comp measurable_snd) hs
  simpa [Set.preimage] using hselection.inter hpopulation

/-- The law obtained by sampling a random finite population without replacement.

First draw a population `x : κ → α` with law `ρ`; independently and uniformly draw an injective
selection `k : ι → κ`; then return the sample `i ↦ x (k i)`. If no injective selection exists,
Mathlib's `uniformOn` convention makes this the zero measure. -/
def sampleWithoutReplacement {ι κ : Type*} [MeasurableSpace κ]
    (ρ : Measure (κ → α)) : Measure (ι → α) :=
  ((uniformOn {k : ι → κ | Function.Injective k}).prod ρ).map
    fun p i => p.2 (p.1 i)

/-- The defining pushforward form of `sampleWithoutReplacement`. -/
@[simp]
theorem sampleWithoutReplacement_def {ι κ : Type*} [MeasurableSpace κ]
    (ρ : Measure (κ → α)) :
    sampleWithoutReplacement ρ =
      ((uniformOn {k : ι → κ | Function.Injective k}).prod ρ).map
        fun p i => p.2 (p.1 i) :=
  (rfl)

/-- Sampling without replacement preserves probability mass whenever an injective selection
exists. -/
theorem isProbabilityMeasure_sampleWithoutReplacement {ι κ : Type*} [Finite ι] [Finite κ]
    [MeasurableSpace κ] [MeasurableSingletonClass κ] (ρ : Measure (κ → α))
    [IsProbabilityMeasure ρ] (e : ι ↪ κ) :
    IsProbabilityMeasure
      (sampleWithoutReplacement (ι := ι) (κ := κ) (α := α) ρ) := by
  let E : Set (ι → κ) := {k | Function.Injective k}
  let _ : IsProbabilityMeasure (uniformOn E) :=
    isProbabilityMeasure_uniformOn (Set.toFinite E) ⟨e, e.injective⟩
  rw [sampleWithoutReplacement_def]
  exact Measure.isProbabilityMeasure_map measurable_samplePopulation.aemeasurable

/-- Evaluating the without-replacement law averages the selected population laws over uniform
injective selections. -/
theorem sampleWithoutReplacement_apply {ι κ : Type*} [Finite κ]
    [MeasurableSpace κ] [MeasurableSingletonClass κ] {ρ : Measure (κ → α)} [SFinite ρ]
    {A : Set (ι → α)} (hA : MeasurableSet A) :
    sampleWithoutReplacement ρ A =
      ∫⁻ k, ρ ((fun x : κ → α => fun i : ι => x (k i)) ⁻¹' A)
        ∂uniformOn {k : ι → κ | Function.Injective k} := by
  rw [sampleWithoutReplacement_def, Measure.map_apply measurable_samplePopulation hA,
    Measure.prod_apply (measurable_samplePopulation hA)]
  rfl

/-- **Finite exchangeability is sampling without replacement.** If the first `n` coordinates are
exchangeable, then drawing `m ≤ n` distinct positions uniformly from that random `n`-tuple has
exactly the law of the first `m` coordinates.

This is an equality of measures, not merely an eventwise bound. The later finite de Finetti bound
compares its left-hand side with sampling *with* replacement, using the collision estimate in
`UniformSampling.lean`. -/
theorem ExchangeableAt.sampleWithoutReplacement_eq_prefixLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) :
    sampleWithoutReplacement (ι := Fin m) (prefixLaw μ X n) = prefixLaw μ X m := by
  let E : Set (Fin m → Fin n) := {k | Function.Injective k}
  have hEfin : E.Finite := Set.toFinite E
  have hEne : E.Nonempty :=
    ⟨Fin.castLE hmn, fun _ _ hxy => Fin.castLE_injective hmn hxy⟩
  let _ : IsProbabilityMeasure (uniformOn E) :=
    isProbabilityMeasure_uniformOn hEfin hEne
  let _ : IsFiniteMeasure (prefixLaw μ X n) := by
    rw [prefixLaw_def, blockLaw_def]
    exact Measure.isFiniteMeasure_map μ (fun ω => fun i : Fin n => X i.val ω)
  have hae : ∀ᵐ k ∂uniformOn E, Function.Injective k := by
    simpa only [uniformOn, E, Set.mem_ofPred_eq] using
      (ae_cond_mem (μ := Measure.count) hEfin.measurableSet)
  have hmap (k : Fin m → Fin n) (hk : Function.Injective k) :
      (prefixLaw μ X n).map (fun x : Fin n → α => fun i : Fin m => x (k i)) =
        prefixLaw μ X m := by
    rw [prefixLaw_def, map_blockLaw_reindex μ (fun i : Fin n => i.val) k hX]
    have heq : (fun i : Fin n => i.val) ∘ k = fun i : Fin m => (k i).val := by
      rfl
    rw [heq]
    exact h.blockLaw_eq_prefixLaw_of_injective k hk hX
  apply Measure.ext fun A hA => ?_
  rw [sampleWithoutReplacement_apply hA]
  calc
    ∫⁻ k, prefixLaw μ X n
          ((fun x : Fin n → α => fun i : Fin m => x (k i)) ⁻¹' A) ∂uniformOn E =
        ∫⁻ _k, prefixLaw μ X m A ∂uniformOn E := by
      apply lintegral_congr_ae
      filter_upwards [hae] with k hk
      rw [← Measure.map_apply
        (measurable_pi_lambda _ fun i : Fin m => measurable_pi_apply (k i)) hA, hmap k hk]
    _ = prefixLaw μ X m A := by simp

end Probability

end TauCeti
