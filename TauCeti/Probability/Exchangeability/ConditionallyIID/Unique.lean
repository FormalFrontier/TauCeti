/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Moments
-- Non-public: `measurable_probabilityMeasure_toMeasure_apply_toReal` evaluates a random measure at
-- a fixed measurable set in the `.toReal` form.
import TauCeti.MeasureTheory.Measure.ProbabilityMeasureExt
-- Non-public: the countable set algebra that compares two random measures set by set.
import Mathlib.MeasureTheory.SetAlgebra
-- Non-public: `tendsto_const_div_atTop_nhds_zero_nat` closes the `O(1/n)` squeeze.
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Almost sure uniqueness of the directing measure

A **directing measure** — a witness of `ConditionallyIIDWith μ X ν` — is pinned down almost
everywhere: any two of them agree `μ`-a.e. This is the sharp uniqueness statement that the
mixture predicate `MixedIIDWith` fails to have, where only the *mixing law* `μ.map ν` is unique
(`mixedIID_mixingLaw_unique`); an independent copy of a directing measure is another mixing
representative but not another directing measure.

## Main results

* `ConditionallyIIDWith.lintegral_mul_indicator_iInter` — the weighted block identity: testing the
  joint-law disintegration against `g (ν ω)` times the indicator of a block rectangle turns the
  block into the `m`-th power `(ν ω) B ^ m`. Its one- and two-coordinate specializations are
  `ConditionallyIIDWith.lintegral_mul_indicator_single` and
  `ConditionallyIIDWith.lintegral_mul_indicator_pair`.
* `ConditionallyIIDWith.integral_empiricalFrequency_sub_sq` — the `L²` rate: the empirical
  frequency of a measurable set `B` along the first `n` coordinates approximates `(ν ·) B` with
  mean square error exactly `(∫ (ν ·) B - ∫ ((ν ·) B) ^ 2) / n`.
* `conditionallyIID_ae_unique` — two directing measures of the same process are a.e. equal.

## Implementation

The directing measure is recovered from the process by a law of large numbers, and the joint-law
form of `ConditionallyIIDWith` gives the second-moment version of that law directly, with no
conditional expectations. Writing `q ω = (ν ω) B` and `eᵢ` for the indicator of `Xᵢ ∈ B`, the
weighted block identity supplies the three moments

```text
∫ eᵢ = ∫ q,      ∫ eᵢ eⱼ = ∫ q²  (i ≠ j),      ∫ q eᵢ = ∫ q²,
```

the last of which is the genuinely *conditional* input: it is the joint law of `(ν, Xᵢ)`, not the
marginal law of `Xᵢ`, that the mixture predicate would leave free. The centred variables `eᵢ - q`
are therefore uncorrelated with common variance `∫ q - ∫ q²`, so the averages of `eᵢ` converge to
`q` with mean square error `O(1/n)`, hence in `L²` at rate `O(1/√n)`. Both directing measures are
approximated by the *same* averages, so the triangle inequality forces `∫ (q - q')² = 0` for every
measurable `B`, and a countable generating set algebra promotes that to a.e. equality of the random
measures themselves.

The hypothesis `[MeasurableSpace.CountablyGenerated α]` is what the final promotion needs;
`TauCetiRoadmap/Exchangeability/README.md`, Layer 6, states `conditionallyIID_ae_unique` with
`[StandardBorelSpace α] [Nonempty α]`, which is stronger — `countablyGenerated_of_standardBorel`
supplies the instance, and nonemptiness is never used, since no measure is constructed here.
The coordinates are only assumed a.e. measurable (`∀ i, AEMeasurable (X i) μ`), as elsewhere in the
measure-theoretic exchangeability API: every statement here sees `X` through integrals, hence only
modulo `μ`-a.e. equality.
-/

public section

noncomputable section

open Filter MeasurableSpace MeasureTheory Set Topology

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  {μ : Measure Ω} {X : ℕ → Ω → α} {ν ν' : Ω → ProbabilityMeasure α} {B : Set α}

/-! ### Uniqueness -/

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- **An average of indicators lies in `[0, 1]`.** Stated with the absolute value because that is
the form the `L²` estimates below consume. -/
private theorem abs_average_indicator_le_one (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) :
    |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (A i).indicator (1 : Ω → ℝ) ω| ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  have hne : (Finset.range n).Nonempty := Finset.nonempty_range_iff.mpr hpos.ne'
  -- The average is `𝔼 i ∈ range n`, so the generic expectation bounds apply term by term.
  have hexp : (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (A i).indicator (1 : Ω → ℝ) ω
      = Finset.expect (Finset.range n) fun i => (A i).indicator (1 : Ω → ℝ) ω := by
    rw [Finset.expect_eq_sum_div_card, Finset.card_range, div_eq_inv_mul]
  rw [hexp]
  refine le_trans (Finset.abs_expect_le _ _) (Finset.expect_le hne fun i _ => ?_)
  by_cases hmem : ω ∈ A i <;> simp [hmem]

/-- **A squared difference of bounded functions is integrable**, being bounded by `4` on a finite
measure space. -/
private theorem integrable_sub_sq_of_abs_le_one [IsFiniteMeasure μ] {u v : Ω → ℝ}
    (hu : AEMeasurable u μ) (hv : AEMeasurable v μ)
    (hu1 : ∀ᵐ ω ∂μ, |u ω| ≤ 1) (hv1 : ∀ᵐ ω ∂μ, |v ω| ≤ 1) :
    Integrable (fun ω => (u ω - v ω) ^ 2) μ := by
  refine Integrable.of_bound ((hu.sub hv).pow_const 2).aestronglyMeasurable 4 ?_
  filter_upwards [hu1, hv1] with ω hu1 hv1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [abs_le.mp hu1, abs_le.mp hv1]


/-- **An `L²` triangle bound.** If `q` and `q'` are within `c₁` and `c₂` of a common `Y` in mean
square, then they are within `2c₁ + 2c₂` of each other. The three squared differences are assumed
integrable; `hd` is not implied by `hi1` and `hi2`, which constrain only the squares `(Y - q)²` and
`(Y - q')²` and so do not make `q - q'` measurable. -/
private theorem integral_sub_sq_le_two_mul_add_two_mul_of_integral_sub_sq_le_of_integral_sub_sq_le
    {q q' Y : Ω → ℝ}
    (hd : Integrable (fun ω => (q ω - q' ω) ^ 2) μ)
    (hi1 : Integrable (fun ω => (Y ω - q ω) ^ 2) μ)
    (hi2 : Integrable (fun ω => (Y ω - q' ω) ^ 2) μ)
    {c₁ c₂ : ℝ} (h1 : ∫ ω, (Y ω - q ω) ^ 2 ∂μ ≤ c₁) (h2 : ∫ ω, (Y ω - q' ω) ^ 2 ∂μ ≤ c₂) :
    ∫ ω, (q ω - q' ω) ^ 2 ∂μ ≤ 2 * c₁ + 2 * c₂ := by
  -- The pointwise step is Mathlib's `add_sq_le` applied to `q - q' = (q - Y) + (Y - q')`.
  calc ∫ ω, (q ω - q' ω) ^ 2 ∂μ
      ≤ ∫ ω, (2 * (Y ω - q ω) ^ 2 + 2 * (Y ω - q' ω) ^ 2) ∂μ :=
        integral_mono hd ((hi1.const_mul 2).add (hi2.const_mul 2)) fun ω => by
          nlinarith [add_sq_le (a := q ω - Y ω) (b := Y ω - q' ω)]
    _ = 2 * ∫ ω, (Y ω - q ω) ^ 2 ∂μ + 2 * ∫ ω, (Y ω - q' ω) ^ 2 ∂μ := by
        rw [integral_add (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul,
          integral_const_mul]
    _ ≤ 2 * c₁ + 2 * c₂ := by linarith

/-- **The squared difference of two directing masses is integrable.** Each evaluation
`ω ↦ ((ρ ω) B).toReal` is measurable and takes values in `[0, 1]`, so the square of the difference
is bounded, hence integrable on a finite measure space. -/
private theorem integrable_toReal_directing_sub_sq [IsFiniteMeasure μ]
    {ρ ρ' : Ω → ProbabilityMeasure α} (hρ : Measurable ρ) (hρ' : Measurable ρ')
    (hB : MeasurableSet B) :
    Integrable (fun ω =>
      (((ρ ω : Measure α) B).toReal - ((ρ' ω : Measure α) B).toReal) ^ 2) μ := by
  have habs : ∀ (σ : Ω → ProbabilityMeasure α) (ω : Ω),
      |((σ ω : Measure α) B).toReal| ≤ 1 := fun σ ω => by
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    simpa using
      ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := (σ ω : Measure α)) (s := B))
  exact integrable_sub_sq_of_abs_le_one
    ((TauCeti.MeasureTheory.measurable_probabilityMeasure_toMeasure_apply_toReal hB).comp
      hρ).aemeasurable
    ((TauCeti.MeasureTheory.measurable_probabilityMeasure_toMeasure_apply_toReal hB).comp
      hρ').aemeasurable
    (ae_of_all _ (habs ρ)) (ae_of_all _ (habs ρ'))

/-- **The `L²` rate between two directing measures.** Two directing measures of the same process
are within `4 / n` of each other in mean square, for every `n ≥ 1`, on each fixed measurable set.
This is the scaffolding for `ae_measure_apply_eq`, which is its `n → ∞` limit. It stays private:
that theorem has the same hypotheses and makes the integrand a.e. zero, so once it is available
this bound is a trivial consequence and carries no independent content. -/
private theorem ConditionallyIIDWith.integral_directing_sub_sq_le_four_div
    [IsProbabilityMeasure μ]
    (hX : ∀ i, AEMeasurable (X i) μ) (h : ConditionallyIIDWith μ X ν)
    (h' : ConditionallyIIDWith μ X ν') (hB : MeasurableSet B) {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, (((ν ω : Measure α) B).toReal - ((ν' ω : Measure α) B).toReal) ^ 2 ∂μ ≤ 4 / n := by
  have hqm : ∀ ρ : Ω → ProbabilityMeasure α, Measurable ρ →
      Measurable fun ω => ((ρ ω : Measure α) B).toReal := fun _ hρ =>
    (TauCeti.MeasureTheory.measurable_probabilityMeasure_toMeasure_apply_toReal hB).comp hρ
  have habs : ∀ (ρ : Ω → ProbabilityMeasure α) (ω : Ω),
      |((ρ ω : Measure α) B).toReal| ≤ 1 := fun ρ ω => by
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    simpa using
      ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := (ρ ω : Measure α)) (s := B))
  have hem : ∀ m : ℕ, AEMeasurable (fun ω =>
      (m : ℝ)⁻¹ * ∑ i ∈ Finset.range m, (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω) μ := fun m =>
    aemeasurable_const.mul (Finset.aemeasurable_fun_sum _ fun i _ =>
      measurable_one.aemeasurable.indicator₀ ((hX i).nullMeasurableSet_preimage hB))
  have heb : ∀ (m : ℕ) (ω : Ω),
      |(m : ℝ)⁻¹ * ∑ i ∈ Finset.range m, (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω| ≤ 1 :=
    fun m ω => abs_average_indicator_le_one (fun i => X i ⁻¹' B) m ω
  have hdint : Integrable (fun ω =>
      (((ν ω : Measure α) B).toReal - ((ν' ω : Measure α) B).toReal) ^ 2) μ :=
    integrable_toReal_directing_sub_sq h.measurable_directing h'.measurable_directing hB
  -- Both errors are bounded by `1 / n`, so the general `2c₁ + 2c₂` bound specializes to `4 / n`.
  have hb : ∫ ω, (((ν ω : Measure α) B).toReal - ((ν' ω : Measure α) B).toReal) ^ 2 ∂μ
      ≤ 2 * (n : ℝ)⁻¹ + 2 * (n : ℝ)⁻¹ :=
    integral_sub_sq_le_two_mul_add_two_mul_of_integral_sub_sq_le_of_integral_sub_sq_le hdint
      (integrable_sub_sq_of_abs_le_one (hem n) (hqm ν h.measurable_directing).aemeasurable
        (ae_of_all _ (heb n)) (ae_of_all _ (habs ν)))
      (integrable_sub_sq_of_abs_le_one (hem n) (hqm ν' h'.measurable_directing).aemeasurable
        (ae_of_all _ (heb n)) (ae_of_all _ (habs ν')))
      (h.integral_empiricalFrequency_sub_sq_le (fun i _ => hX i) hB hn)
      (h'.integral_empiricalFrequency_sub_sq_le (fun i _ => hX i) hB hn)
  rw [div_eq_mul_inv]
  linarith

/-- Two directing measures of the same process assign the same mass to each fixed measurable set,
almost everywhere.

Both are approximated in `L²` by the *same* empirical frequencies, at a rate that does not depend
on the witness, so the triangle inequality forces their difference to vanish in `L²`. -/
theorem ConditionallyIIDWith.ae_measure_apply_eq [IsProbabilityMeasure μ]
    (hX : ∀ i, AEMeasurable (X i) μ) (h : ConditionallyIIDWith μ X ν)
    (h' : ConditionallyIIDWith μ X ν') (hB : MeasurableSet B) :
    (fun ω => (ν ω : Measure α) B) =ᵐ[μ] fun ω => (ν' ω : Measure α) B := by
  set d : Ω → ℝ := fun ω =>
    ((ν ω : Measure α) B).toReal - ((ν' ω : Measure α) B).toReal with hd_def
  have hdint : Integrable (fun ω => d ω ^ 2) μ := by
    simpa only [hd_def] using
      integrable_toReal_directing_sub_sq h.measurable_directing h'.measurable_directing hB
  -- `hd_def` turns the `set` wrapper `d` into the explicit difference the rate lemma is stated for.
  have hbound : ∀ n : ℕ, 1 ≤ n → ∫ ω, d ω ^ 2 ∂μ ≤ 4 / n := fun n hn => by
    simpa only [hd_def] using h.integral_directing_sub_sq_le_four_div hX h' hB (n := n) (by omega)
  have hle : ∫ ω, d ω ^ 2 ∂μ ≤ 0 :=
    ge_of_tendsto (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ))
      (eventually_atTop.2 ⟨1, fun n hn => hbound n hn⟩)
  have hae : (fun ω => d ω ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => by positivity) hdint).mp
      (le_antisymm hle (integral_nonneg fun ω => by positivity))
  filter_upwards [hae] with ω hω
  have hd0 : d ω = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hω
  refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp ?_
  simp only [hd_def] at hd0
  linarith

/-- Almost sure equality of two random probability measures follows from a.e. equality of their
masses on each fixed measurable set, when the σ-algebra is countably generated. Private: the final
promotion step, phrased for the two witnesses at hand.

The countable-set-algebra argument is adapted from `TauCeti.MeasureTheory.Measure.FiniteMeasure`,
where the same `generateSetAlgebra (countableGeneratingSet α)` idiom pins a finite measure down from
its values on a countable set algebra (there, to prove that singletons are measurable). -/
private theorem ae_eq_of_forall_apply_ae_eq [CountablyGenerated α]
    (h : ∀ s : Set α, MeasurableSet s →
      (fun ω => (ν ω : Measure α) s) =ᵐ[μ] fun ω => (ν' ω : Measure α) s) :
    ν =ᵐ[μ] ν' := by
  set 𝒜 := generateSetAlgebra (countableGeneratingSet α) with h𝒜
  have hcount : 𝒜.Countable := countable_generateSetAlgebra countable_countableGeneratingSet
  have halg : IsSetAlgebra 𝒜 := isSetAlgebra_generateSetAlgebra
  have hgen : ‹MeasurableSpace α› = generateFrom 𝒜 := by
    rw [h𝒜, generateFrom_generateSetAlgebra_eq, generateFrom_countableGeneratingSet]
  have hmeas : ∀ s ∈ 𝒜, MeasurableSet s := fun s hs => hgen ▸ measurableSet_generateFrom hs
  have hall : ∀ᵐ ω ∂μ, ∀ s ∈ 𝒜, (ν ω : Measure α) s = (ν' ω : Measure α) s := by
    rw [ae_ball_iff hcount]
    exact fun s hs => h s (hmeas s hs)
  filter_upwards [hall] with ω hω
  haveI := (ν ω).2
  refine Subtype.ext (ext_of_generate_finite 𝒜 hgen (fun s hs t ht _ => halg.inter_mem hs ht)
    (fun s hs => hω s hs) (hω _ halg.univ_mem))

/-- **The directing measure is almost surely unique.** Two witnesses of `ConditionallyIIDWith` for
the same process agree almost everywhere.

This is the uniqueness statement that belongs to the *conditional* predicate. Its mixture analogue
is false at the level of witnesses: for a nondegenerate mixing law an independent copy of a
directing measure is another mixing representative, and only the mixing law `μ.map ν` is determined
(`mixedIID_mixingLaw_unique`).

`TauCetiRoadmap/Exchangeability/README.md` (Layer 6) states this with `[StandardBorelSpace α]`,
which supplies `[MeasurableSpace.CountablyGenerated α]` through
`countablyGenerated_of_standardBorel`; the extra `[Nonempty α]` is not needed, since no measure on
`α` is constructed here. -/
theorem conditionallyIID_ae_unique [IsProbabilityMeasure μ] [CountablyGenerated α]
    (hX : ∀ i, AEMeasurable (X i) μ) (h : ConditionallyIIDWith μ X ν)
    (h' : ConditionallyIIDWith μ X ν') : ν =ᵐ[μ] ν' :=
  ae_eq_of_forall_apply_ae_eq fun _ hs => h.ae_measure_apply_eq hX h' hs

end Probability

end TauCeti
