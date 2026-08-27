/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.DeFinetti.Barycenter
public import TauCeti.Probability.Exchangeability.Recurrence.Excursion
-- Non-public: the mixture form of a path law is used only inside proofs.
import TauCeti.Probability.Exchangeability.MixedIID.Mixture

/-!
# A recurrent Markov exchangeable process is a mixture of processes with i.i.d. excursions

A recurrent process that starts at a state `a₀` returns to it infinitely often, so it is spelled
out by its excursions and by nothing else: reading the excursions off the path and concatenating
them back are mutually inverse (`TauCeti.pathOfExcursions_excursion` and
`TauCeti.excursion_pathOfExcursions`). This file turns that bijection into an identity of laws.
The path law of the process is the image of the path law of its excursion process under
concatenation (`TauCeti.Probability.Recurrent.pathLaw_eq_map_pathOfExcursions`), and for a
**Markov exchangeable** process the excursion process is exchangeable, hence conditionally i.i.d.
The resulting representation is

```text
pathLaw μ X = (deFinettiBarycenter π).map (pathOfExcursions a₀)
```

for a probability measure `π` on laws of finite words: draw an excursion law `P` from `π`, draw
excursions i.i.d. from `P`, and concatenate them
(`TauCeti.Probability.MarkovExchangeable.exists_pathLaw_eq_map_deFinettiBarycenter`). The mixing
law is carried on laws of words that almost surely avoid `a₀`
(`TauCeti.Probability.MarkovExchangeable.exists_pathLaw_eq_map_deFinettiBarycenter`, second
conjunct), so the concatenated path really has the drawn words as its excursions.

This is Diaconis and Freedman's decomposition step for Markov exchangeability: it exhibits a
recurrent Markov exchangeable process as a mixture of **regenerative** processes. What it does not
yet say is that the random excursion law is the excursion law of a Markov chain, which is the
remaining input of the Diaconis–Freedman representation
`TauCeti.Probability.MixedMarkovChain`.

## Main results

* `TauCeti.Probability.measurable_pathOfExcursions`: concatenating excursions is measurable over a
  countable discrete state space.
* `TauCeti.Probability.pathLaw_eq_map_pathOfExcursions`: the path law of a process that almost
  surely starts at and returns infinitely often to `a₀` is the image of its excursion law under
  concatenation.
* `TauCeti.Probability.ConditionallyIIDWith.ae_measure_setOf_mem_eq_zero_of_excursionProcess`: a
  directing measure of an excursion process almost surely charges no word through the base state.
* `TauCeti.Probability.MarkovExchangeable.exists_pathLaw_eq_map_deFinettiBarycenter`: **a recurrent
  Markov exchangeable process is a mixture of processes with i.i.d. excursions.**

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.
* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 8, "Markov exchangeability".

No material is adapted from `cameronfreer/exchangeability`, which treats exchangeable rather than
Markov exchangeable sequences.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-! ## Measurability of the concatenation map -/

/-- **Concatenating a sequence of excursions is measurable.** Each coordinate of the concatenated
sequence depends on finitely many excursions, and over a countable discrete state space the finite
words form a countable discrete space, on which every map is measurable. -/
theorem measurable_pathOfExcursions [Countable α] [MeasurableSingletonClass α] (a₀ : α) :
    Measurable (pathOfExcursions a₀ : (ℕ → List α) → ℕ → α) := by
  refine measurable_pi_lambda _ fun i => ?_
  have hfac : (fun b : ℕ → List α => pathOfExcursions a₀ b i) =
      (fun v : Fin (i + 1) → List α => loopPathAt a₀ (List.ofFn v) i) ∘
        fun (b : ℕ → List α) (j : Fin (i + 1)) => b j.val := by
    funext b
    have hi : i ≤ loopSteps ((List.range (i + 1)).map b) := by
      have hle := length_le_loopSteps ((List.range (i + 1)).map b)
      simp only [List.length_map, List.length_range] at hle
      omega
    rw [Function.comp_apply, pathOfExcursions_eq_loopPathAt a₀ b hi]
    congr 1
    refine List.ext_getElem (by simp) fun j hj hj' => ?_
    rw [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  rw [hfac]
  exact Measurable.of_discrete.comp (measurable_pi_lambda _ fun j => measurable_pi_apply _)

/-! ## The path law of a recurrent process -/

variable {μ : Measure Ω} {X : ℕ → Ω → α} {a₀ : α}

/-- **The path law of a process returning infinitely often to `a₀` is the image of its excursion
law.** Almost every sample path starts at and returns infinitely often to `a₀`, so concatenating
its excursions recovers it. -/
theorem pathLaw_eq_map_pathOfExcursions [Countable α] [MeasurableSingletonClass α]
    (hX : ∀ i, AEMeasurable (X i) μ) (hreturns : ∀ᵐ ω ∂μ, {n | X n ω = a₀}.Infinite)
    (h0 : ∀ᵐ ω ∂μ, X 0 ω = a₀) :
    pathLaw μ X = (pathLaw μ (excursionProcess X a₀)).map (pathOfExcursions a₀) := by
  have hΦ : AEMeasurable (fun ω k => excursionProcess X a₀ k ω) μ :=
    aemeasurable_pi_lambda _ fun k => aemeasurable_excursionProcess hX a₀ k
  have hae : (pathOfExcursions a₀ ∘ fun ω k => excursionProcess X a₀ k ω) =ᵐ[μ]
      fun ω i => X i ω := by
    filter_upwards [h0, hreturns] with ω hω0 hωinf
    simpa [Function.comp_def] using pathOfExcursions_excursion hωinf hω0
  rw [pathLaw_def, pathLaw_def,
    AEMeasurable.map_map_of_aemeasurable (measurable_pathOfExcursions a₀).aemeasurable hΦ,
    Measure.map_congr hae]

/-- **The path law of a recurrent process started at `a₀` is the image of its excursion law.** -/
theorem Recurrent.pathLaw_eq_map_pathOfExcursions [Countable α] [MeasurableSingletonClass α]
    (hrec : Recurrent μ X) (hX : ∀ i, AEMeasurable (X i) μ) (h0 : ∀ᵐ ω ∂μ, X 0 ω = a₀) :
    pathLaw μ X = (pathLaw μ (excursionProcess X a₀)).map (pathOfExcursions a₀) := by
  apply TauCeti.Probability.pathLaw_eq_map_pathOfExcursions hX _ h0
  filter_upwards [h0, hrec.ae_infinite_setOf_eq] with ω hω0 hωinf
  have h := hωinf 0
  rwa [hω0] at h

/-! ## Excursion laws avoid the base state -/

/-- **A directing measure of an excursion process charges no word through the base state.** An
excursion never visits the state it is an excursion from, so almost every mixing representative of
the excursion process gives the words through `a₀` mass zero. -/
theorem ConditionallyIIDWith.ae_measure_setOf_mem_eq_zero_of_excursionProcess
    [Countable α] [MeasurableSingletonClass α]
    {ν : Ω → ProbabilityMeasure (List α)}
    (h : ConditionallyIIDWith μ (excursionProcess X a₀) ν) :
    ∀ᵐ ω ∂μ, (ν ω : Measure (List α)) {l : List α | a₀ ∈ l} = 0 := by
  set S : Set (List α) := {l : List α | a₀ ∈ l} with hS
  have hSmeas : MeasurableSet S := MeasurableSet.of_discrete
  have hmix := mixedIIDWith_of_conditionallyIIDWith h
  have hrect := hmix.blockLaw_univ_pi (fun _ : Fin 1 => (0 : ℕ))
    (fun i j _ => Subsingleton.elim i j) (fun _ : Fin 1 => S) fun _ => hSmeas
  -- The block law of a single excursion gives the rectangle no mass: an excursion avoids `a₀`.
  have hzero : blockLaw μ (excursionProcess X a₀) (fun _ : Fin 1 => (0 : ℕ))
      (Set.univ.pi fun _ : Fin 1 => S) = 0 := by
    have hf : AEMeasurable
        (fun ω => fun _ : Fin 1 => excursionProcess X a₀ 0 ω) μ :=
      aemeasurable_pi_lambda _ fun _ => h.aemeasurable 0
    rw [blockLaw_def, Measure.map_apply_of_aemeasurable hf
      (MeasurableSet.univ_pi fun _ => hSmeas)]
    convert measure_empty (μ := μ)
    refine Set.eq_empty_of_forall_notMem fun ω hω => ?_
    have hmem := (Set.mem_univ_pi.1 hω) 0
    simp only [hS, Set.mem_ofPred_eq, excursionProcess_apply] at hmem
    exact not_mem_excursion (fun n => X n ω) a₀ 0 hmem
  rw [hzero] at hrect
  have hmeasν : Measurable fun ω => (ν ω : Measure (List α)) S :=
    (Measure.measurable_coe hSmeas).comp
      (measurable_subtype_coe.comp hmix.measurable_mixingRepresentative)
  have hint : ∫⁻ ω, (ν ω : Measure (List α)) S ∂μ = 0 := by
    have hsplit : ∫⁻ ω, (ν ω : Measure (List α)) S ∂μ
        = ∫⁻ ω, ∏ _i : Fin 1, (ν ω : Measure (List α)) S ∂μ :=
      lintegral_congr fun ω => by rw [Fin.prod_univ_one]
    rw [hsplit, ← hrect]
  filter_upwards [(lintegral_eq_zero_iff hmeasν).1 hint] with ω hω using hω

/-! ## The representation -/

/-- **A recurrent Markov exchangeable process is a mixture of processes with i.i.d. excursions.**
Its path law is obtained by drawing an excursion law `P` from a mixing law `π`, drawing excursions
i.i.d. from `P`, and concatenating them. The mixing law is carried on laws that almost surely avoid
the base state, so the concatenated path has the drawn words as its excursions.

This is the decomposition step of the Diaconis–Freedman representation. Identifying the random
excursion law with the excursion law of a Markov chain, which upgrades this to
`TauCeti.Probability.MixedMarkovChain`, is a separate statement. -/
theorem MarkovExchangeable.exists_pathLaw_eq_map_deFinettiBarycenter [IsProbabilityMeasure μ]
    (h : MarkovExchangeable μ X) (hrec : Recurrent μ X) (h0 : ∀ᵐ ω ∂μ, X 0 ω = a₀) :
    ∃ π : Measure (ProbabilityMeasure (List α)), IsProbabilityMeasure π ∧
      (∀ᵐ P : ProbabilityMeasure (List α) ∂π,
        (P : Measure (List α)) {l : List α | a₀ ∈ l} = 0) ∧
      pathLaw μ X = (deFinettiBarycenter π).map (pathOfExcursions a₀) := by
  let _ : Countable α := h.countable
  have : MeasurableSingletonClass α := h.measurableSingletonClass
  obtain ⟨ν, hν⟩ := (h.conditionallyIID_excursionProcess hrec h0).exists_directing
  have hmix := mixedIIDWith_of_conditionallyIIDWith hν
  have hν_meas : Measurable ν := hmix.measurable_mixingRepresentative
  have hSmeas : MeasurableSet {l : List α | a₀ ∈ l} := MeasurableSet.of_discrete
  refine ⟨μ.map ν, Measure.isProbabilityMeasure_map hν_meas.aemeasurable, ?_, ?_⟩
  · refine (ae_map_iff hν_meas.aemeasurable ?_).2
      hν.ae_measure_setOf_mem_eq_zero_of_excursionProcess
    exact ((Measure.measurable_coe hSmeas).comp measurable_subtype_coe)
      (measurableSet_singleton (0 : ENNReal))
  · rw [hrec.pathLaw_eq_map_pathOfExcursions h.aemeasurable h0,
      pathLaw_eq_bind_infinitePi_of_mixedIIDWith hmix, deFinettiBarycenter_def]

end Probability

end TauCeti

end

end
