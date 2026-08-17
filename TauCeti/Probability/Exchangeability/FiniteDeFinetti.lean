/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.ProductKernel
public import TauCeti.Probability.Exchangeability.SamplingWithoutReplacement
public import TauCeti.Probability.Process.EmpiricalMeasure

/-!
# Quantitative finite de Finetti approximation

Let `x : κ → α` be a nonempty finite population. Its empirical distribution is the pushforward
of the uniform law on `κ` by `x`. Sampling `ι` entries from that distribution independently is
therefore the same as choosing a uniform map `ι → κ` and reading the selected entries of `x`.

For a random population with law `ρ`, `sampleWithReplacement ρ` mixes these finite product laws
over `ρ`. The law `sampleWithoutReplacement ρ` already represents every shorter marginal of a
finite exchangeable process. The collision coupling between uniform maps and uniform injective
maps consequently gives, for every measurable event `A`,

```text
prefixLaw μ X m A ≤ sampleWithReplacement (prefixLaw μ X n) A + choose(m, 2) / n
sampleWithReplacement (prefixLaw μ X n) A ≤ prefixLaw μ X m A + choose(m, 2) / n.
```

Thus every `m`-coordinate marginal of an `n`-exchangeable process is quantitatively approximated
by a mixture of `m`-fold product measures of empirical distributions. The bound is deliberately
eventwise rather than packaged in a new total-variation definition.

## Main declarations

* `TauCeti.Probability.empiricalPopulation`: the empirical probability measure of a nonempty
  finite population;
* `TauCeti.Probability.sampleWithReplacement`: the mixture of finite powers of those empirical
  measures;
* `TauCeti.Probability.ExchangeableAt.prefixLaw_le_sampleWithReplacement_add` and
  `TauCeti.Probability.ExchangeableAt.sampleWithReplacement_le_prefixLaw_add`: the two sides of
  the finite de Finetti bound.

## References

* P. Diaconis and D. Freedman, “Finite exchangeable sequences”, *Annals of Probability* 8
  (1980), 745–764.

No material is adapted from `cameronfreer/exchangeability`; that development concerns infinite
exchangeable sequences rather than quantitative finite approximation.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

section EmpiricalPopulation

variable {κ : Type*} [Fintype κ] [Nonempty κ] [MeasurableSpace κ]
  [MeasurableSingletonClass κ]

variable {ι : Type*} [Fintype ι]

/-- Independently sampling from a finite empirical population is the same as choosing a uniform
map into the population and reading the selected entries. -/
theorem pi_empiricalPopulation_eq_map_uniformOn (x : κ → α) :
    (ProbabilityMeasure.pi fun _ : ι => empiricalPopulation x).toMeasure =
      (uniformOn (Set.univ : Set (ι → κ))).map fun k i => x (k i) := by
  rw [ProbabilityMeasure.toMeasure_pi]
  simp_rw [empiricalPopulation_eq_map_uniformOn]
  rw [← Measure.pi_map_pi fun _ : ι => (measurable_of_countable x).aemeasurable]
  rw [← uniformOn_pi (f := fun _ : ι => (Set.univ : Set κ))]
  congr 2
  simp

end EmpiricalPopulation

section Sampling

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]

/-- Sampling with replacement from a random finite population.

For a population law `ρ`, this is the `ρ`-mixture of the `ι`-fold product of each population's
empirical probability measure. -/
def sampleWithReplacement (ρ : Measure (κ → α)) : Measure (ι → α) :=
  ρ.bind fun x => (ProbabilityMeasure.pi fun _ : ι => empiricalPopulation x).toMeasure

/-- The product-measure mixture defining sampling with replacement is a measurable kernel. -/
theorem aemeasurable_pi_empiricalPopulation (ρ : Measure (κ → α)) :
    AEMeasurable
      (fun x => (ProbabilityMeasure.pi fun _ : ι => empiricalPopulation x).toMeasure) ρ :=
  (TauCeti.MeasureTheory.measurable_probabilityMeasure_pi_toMeasure
      (fun _ : ι => empiricalPopulation) (fun _ => measurable_empiricalPopulation)).aemeasurable

/-- Sampling with replacement from a random population preserves probability mass. -/
theorem isProbabilityMeasure_sampleWithReplacement (ρ : Measure (κ → α))
    [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (sampleWithReplacement (ι := ι) ρ) :=
  isProbabilityMeasure_bind
    (aemeasurable_pi_empiricalPopulation (ι := ι) (κ := κ) (α := α) ρ)
    (.of_forall fun _ => inferInstance)

/-- Evaluation of the with-replacement law as an average over the random finite population. -/
theorem sampleWithReplacement_apply {ρ : Measure (κ → α)} {A : Set (ι → α)}
    (hA : MeasurableSet A) :
    sampleWithReplacement ρ A =
      ∫⁻ x, (ProbabilityMeasure.pi fun _ : ι => empiricalPopulation x).toMeasure A ∂ρ :=
  Measure.bind_apply hA (aemeasurable_pi_empiricalPopulation ρ)

section DiscretePopulation

variable [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- Sampling with replacement is the pushforward obtained by first choosing a uniform map into
the population and independently drawing the population itself. -/
theorem sampleWithReplacement_eq_map_prod (ρ : Measure (κ → α)) [SFinite ρ] :
    sampleWithReplacement ρ =
      ((uniformOn (Set.univ : Set (ι → κ))).prod ρ).map
        fun p i => p.2 (p.1 i) := by
  apply Measure.ext fun A hA => ?_
  rw [sampleWithReplacement, Measure.bind_apply hA (aemeasurable_pi_empiricalPopulation ρ)]
  rw [Measure.map_apply measurable_reindexPopulation hA]
  rw [Measure.prod_apply_symm (measurable_reindexPopulation hA)]
  apply lintegral_congr
  intro x
  -- Expose the fixed-population section of the joint preimage so `Measure.map_apply` matches it.
  change (ProbabilityMeasure.pi fun _ : ι => empiricalPopulation x).toMeasure A =
    uniformOn (Set.univ : Set (ι → κ)) ((fun k i => x (k i)) ⁻¹' A)
  rw [← Measure.map_apply
      (μ := uniformOn (Set.univ : Set (ι → κ)))
      (f := fun k i => x (k i))
      (measurable_pi_lambda _ fun i =>
        (measurable_of_countable x).comp (measurable_pi_apply i)) hA,
    ← pi_empiricalPopulation_eq_map_uniformOn]

omit [Nonempty κ] [Fintype ι] [Fintype κ] in
/-- Evaluation of the without-replacement law by conditioning first on the population. -/
theorem sampleWithoutReplacement_apply_population [Finite κ]
    {ρ : Measure (κ → α)} [SFinite ρ]
    {A : Set (ι → α)} (hA : MeasurableSet A) :
    sampleWithoutReplacement ρ A =
      ∫⁻ x, uniformOn {k : ι → κ | Function.Injective k}
        ((fun k i => x (k i)) ⁻¹' A) ∂ρ := by
  rw [sampleWithoutReplacement_def, Measure.map_apply measurable_reindexPopulation hA]
  rw [Measure.prod_apply_symm (measurable_reindexPopulation hA)]
  rfl

/-- Evaluation of the with-replacement law by conditioning first on the population. -/
theorem sampleWithReplacement_apply_population {ρ : Measure (κ → α)} [SFinite ρ]
    {A : Set (ι → α)} (hA : MeasurableSet A) :
    sampleWithReplacement ρ A =
      ∫⁻ x, uniformOn (Set.univ : Set (ι → κ))
        ((fun k i => x (k i)) ⁻¹' A) ∂ρ := by
  rw [sampleWithReplacement_eq_map_prod, Measure.map_apply measurable_reindexPopulation hA]
  rw [Measure.prod_apply_symm (measurable_reindexPopulation hA)]
  rfl

/-- **Finite sampling bound, without replacement to with replacement.** For every measurable
event, sampling without replacement from a random finite population has mass at most its
with-replacement mass plus the collision bound `choose |ι| 2 / |κ|`. -/
theorem sampleWithoutReplacement_le_sampleWithReplacement_add
    {ρ : Measure (κ → α)} [IsProbabilityMeasure ρ] {A : Set (ι → α)} (hA : MeasurableSet A) :
    sampleWithoutReplacement ρ A ≤ sampleWithReplacement ρ A +
      (Fintype.card ι).choose 2 / Fintype.card κ := by
  rw [sampleWithoutReplacement_apply_population hA,
    sampleWithReplacement_apply_population hA]
  let c : ℝ≥0∞ := (Fintype.card ι).choose 2 / Fintype.card κ
  let f : (κ → α) → ℝ≥0∞ := fun x =>
    uniformOn (Set.univ : Set (ι → κ)) ((fun k i => x (k i)) ⁻¹' A)
  have hf : Measurable f := by
    exact measurable_measure_prodMk_right (measurable_reindexPopulation hA)
  calc
    (∫⁻ x, uniformOn {k : ι → κ | Function.Injective k}
        ((fun k i => x (k i)) ⁻¹' A) ∂ρ) ≤ ∫⁻ x, f x + c ∂ρ :=
      lintegral_mono fun x => uniformOn_injective_le_add_choose_two_div _
    _ = (∫⁻ x, f x ∂ρ) + ∫⁻ _x, c ∂ρ := lintegral_add_left hf _
    _ = (∫⁻ x, f x ∂ρ) + c := by simp

/-- **Finite sampling bound, with replacement to without replacement.** For every measurable
event, sampling with replacement from a random finite population has mass at most its
without-replacement mass plus the collision bound `choose |ι| 2 / |κ|`. -/
theorem sampleWithReplacement_le_sampleWithoutReplacement_add
    {ρ : Measure (κ → α)} [IsProbabilityMeasure ρ] {A : Set (ι → α)} (hA : MeasurableSet A) :
    sampleWithReplacement ρ A ≤ sampleWithoutReplacement ρ A +
      (Fintype.card ι).choose 2 / Fintype.card κ := by
  rw [sampleWithoutReplacement_apply_population hA,
    sampleWithReplacement_apply_population hA]
  let c : ℝ≥0∞ := (Fintype.card ι).choose 2 / Fintype.card κ
  let f : (κ → α) → ℝ≥0∞ := fun x =>
    uniformOn {k : ι → κ | Function.Injective k} ((fun k i => x (k i)) ⁻¹' A)
  have hf : Measurable f := by
    exact measurable_measure_prodMk_right (measurable_reindexPopulation hA)
  calc
    (∫⁻ x, uniformOn (Set.univ : Set (ι → κ))
        ((fun k i => x (k i)) ⁻¹' A) ∂ρ) ≤ ∫⁻ x, f x + c ∂ρ :=
      lintegral_mono fun x => uniformOn_univ_le_injective_add_choose_two_div _
    _ = (∫⁻ x, f x ∂ρ) + ∫⁻ _x, c ∂ρ := lintegral_add_left hf _
    _ = (∫⁻ x, f x ∂ρ) + c := by simp

end DiscretePopulation

end Sampling

section FiniteExchangeability

/-- **Quantitative finite de Finetti bound, exchangeable law to empirical mixture.** If the first
`n` coordinates of a process are exchangeable and `m ≤ n`, then every measurable event under the
`m`-prefix law has mass at most its mass under the mixture of `m`-fold products of the empirical
distribution of the first `n` coordinates, plus `choose m 2 / n`. -/
theorem ExchangeableAt.prefixLaw_le_sampleWithReplacement_add
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} [NeZero n] (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) {A : Set (Fin m → α)}
    (hA : MeasurableSet A) :
    prefixLaw μ X m A ≤ sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A +
      m.choose 2 / n := by
  let _ : IsProbabilityMeasure (prefixLaw μ X n) := by
    rw [prefixLaw_def, blockLaw_def]
    exact Measure.isProbabilityMeasure_map (aemeasurable_pi_lambda _ hX)
  rw [← h.sampleWithoutReplacement_eq_prefixLaw hmn hX]
  simpa using sampleWithoutReplacement_le_sampleWithReplacement_add
    (ρ := prefixLaw μ X n) hA

/-- **Quantitative finite de Finetti bound, empirical mixture to exchangeable law.** Under the
same hypotheses, every measurable event under the empirical-product mixture has mass at most its
mass under the `m`-prefix law plus `choose m 2 / n`. -/
theorem ExchangeableAt.sampleWithReplacement_le_prefixLaw_add
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} [NeZero n] (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) {A : Set (Fin m → α)}
    (hA : MeasurableSet A) :
    sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A ≤ prefixLaw μ X m A +
      m.choose 2 / n := by
  let _ : IsProbabilityMeasure (prefixLaw μ X n) := by
    rw [prefixLaw_def, blockLaw_def]
    exact Measure.isProbabilityMeasure_map (aemeasurable_pi_lambda _ hX)
  rw [← h.sampleWithoutReplacement_eq_prefixLaw hmn hX]
  simpa using sampleWithReplacement_le_sampleWithoutReplacement_add
    (ρ := prefixLaw μ X n) hA

end FiniteExchangeability

end Probability

end TauCeti
