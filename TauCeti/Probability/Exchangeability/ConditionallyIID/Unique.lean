/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
-- Non-public: the joint kernel's measurability is consumed only inside `Measure.lintegral_bind`.
import TauCeti.MeasureTheory.Measure.ProductKernel
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
are therefore uncorrelated with common variance `∫ q - ∫ q²`, so their averages converge to `0` in
`L²` at rate `1/n`. Both directing measures are approximated by the *same* averages, so the
triangle inequality forces `∫ (q - q')² = 0` for every measurable `B`, and a countable generating
set algebra promotes that to a.e. equality of the random measures themselves.

The hypothesis `[MeasurableSpace.CountablyGenerated α]` is what the final promotion needs;
`TauCetiRoadmap/Exchangeability/README.md`, Layer 6, states `conditionallyIID_ae_unique` with
`[StandardBorelSpace α] [Nonempty α]`, which is stronger — `countablyGenerated_of_standardBorel`
supplies the instance, and nonemptiness is never used, since no measure is constructed here.
-/

public section

noncomputable section

open Filter MeasurableSpace MeasureTheory Set Topology

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  {μ : Measure Ω} {X : ℕ → Ω → α} {ν ν' : Ω → ProbabilityMeasure α} {B : Set α}

/-! ### Weighted block identities -/

/-- **The weighted block identity.** Integrating the joint-law disintegration of
`ConditionallyIIDWith` against a weight `g (ν ω)` times the indicator of the event that a block of
`m` distinct coordinates lands in `B` replaces the block by the power `(ν ω) B ^ m`.

Taking `g = 1` recovers the block probabilities that `MixedIIDWith` already determines; the content
of the conditional predicate is that an arbitrary weight in the directing measure may be carried
along. -/
theorem ConditionallyIIDWith.lintegral_mul_indicator_iInter
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, Measurable (X i))
    {m : ℕ} {k : Fin m → ℕ} (hk : Function.Injective k)
    {g : ProbabilityMeasure α → ℝ≥0∞} (hg : Measurable g) (hB : MeasurableSet B) :
    ∫⁻ ω, g (ν ω) * (⋂ i : Fin m, X (k i) ⁻¹' B).indicator (1 : Ω → ℝ≥0∞) ω ∂μ
      = ∫⁻ ω, g (ν ω) * (ν ω : Measure α) B ^ m ∂μ := by
  have hν := h.measurable_directing
  have hR : MeasurableSet (Set.univ.pi fun _ : Fin m => B) := MeasurableSet.univ_pi fun _ => hB
  set F : ProbabilityMeasure α × (Fin m → α) → ℝ≥0∞ :=
    fun z => g z.1 * (Set.univ.pi fun _ : Fin m => B).indicator (1 : (Fin m → α) → ℝ≥0∞) z.2
    with hF_def
  have hF : Measurable F :=
    (hg.comp measurable_fst).mul ((measurable_one.indicator hR).comp measurable_snd)
  have hΦ : Measurable fun ω => (ν ω, fun i : Fin m => X (k i) ω) :=
    hν.prodMk (measurable_pi_lambda _ fun i => hX (k i))
  have hκ : AEMeasurable (fun ω =>
      (Measure.dirac (ν ω)).prod (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure) μ :=
    (TauCeti.MeasureTheory.measurable_dirac_prod_probabilityMeasure_pi_const_toMeasure ν
      hν).aemeasurable
  have key : ∫⁻ z, F z ∂(μ.map fun ω => (ν ω, fun i : Fin m => X (k i) ω))
      = ∫⁻ z, F z ∂(μ.bind fun ω =>
          (Measure.dirac (ν ω)).prod (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure) := by
    rw [h.jointLaw_eq_disintegration k hk]
  rw [lintegral_map hF hΦ, Measure.lintegral_bind hκ hF.aemeasurable] at key
  calc ∫⁻ ω, g (ν ω) * (⋂ i : Fin m, X (k i) ⁻¹' B).indicator (1 : Ω → ℝ≥0∞) ω ∂μ
      = ∫⁻ ω, F (ν ω, fun i : Fin m => X (k i) ω) ∂μ := by
        refine lintegral_congr fun ω => ?_
        have hind : (Set.univ.pi fun _ : Fin m => B).indicator (1 : (Fin m → α) → ℝ≥0∞)
            (fun i : Fin m => X (k i) ω)
            = (⋂ i : Fin m, X (k i) ⁻¹' B).indicator (1 : Ω → ℝ≥0∞) ω := by
          by_cases hmem : ∀ i : Fin m, X (k i) ω ∈ B
          · rw [Set.indicator_of_mem (by simpa using hmem),
              Set.indicator_of_mem (by simpa using hmem)]
            rfl
          · rw [Set.indicator_of_notMem (by simpa using hmem),
              Set.indicator_of_notMem (by simpa using hmem)]
        simp only [hF_def, hind]
    _ = ∫⁻ ω, ∫⁻ z, F z ∂((Measure.dirac (ν ω)).prod
          (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure) ∂μ := key
    _ = ∫⁻ ω, g (ν ω) * (ν ω : Measure α) B ^ m ∂μ := by
        refine lintegral_congr fun ω => ?_
        rw [Measure.dirac_prod, lintegral_map hF measurable_prodMk_left]
        simp only [hF_def]
        rw [lintegral_const_mul _ (measurable_one.indicator hR), lintegral_indicator_one hR,
          ProbabilityMeasure.toMeasure_pi, Measure.pi_pi]
        simp

/-- One-coordinate form of the weighted block identity. -/
theorem ConditionallyIIDWith.lintegral_mul_indicator_single
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, Measurable (X i)) (i : ℕ)
    {g : ProbabilityMeasure α → ℝ≥0∞} (hg : Measurable g) (hB : MeasurableSet B) :
    ∫⁻ ω, g (ν ω) * (X i ⁻¹' B).indicator (1 : Ω → ℝ≥0∞) ω ∂μ
      = ∫⁻ ω, g (ν ω) * (ν ω : Measure α) B ∂μ := by
  have hinj : Function.Injective (fun _ : Fin 1 => i) := fun a b _ => Subsingleton.elim a b
  simpa [Set.iInter_const] using h.lintegral_mul_indicator_iInter hX hinj hg hB

/-- Two-coordinate form of the weighted block identity, at distinct indices. -/
theorem ConditionallyIIDWith.lintegral_mul_indicator_pair
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, Measurable (X i)) {i j : ℕ} (hij : i ≠ j)
    {g : ProbabilityMeasure α → ℝ≥0∞} (hg : Measurable g) (hB : MeasurableSet B) :
    ∫⁻ ω, g (ν ω) * (X i ⁻¹' B ∩ X j ⁻¹' B).indicator (1 : Ω → ℝ≥0∞) ω ∂μ
      = ∫⁻ ω, g (ν ω) * (ν ω : Measure α) B ^ 2 ∂μ := by
  have hinj : Function.Injective ![i, j] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hset : (⋂ l : Fin 2, X (![i, j] l) ⁻¹' B) = X i ⁻¹' B ∩ X j ⁻¹' B := by
    ext ω
    simp [Fin.forall_fin_two]
  rw [← hset]
  exact h.lintegral_mul_indicator_iInter hX hinj hg hB

/-! ### The `L²` rate for empirical frequencies -/

/-- Transfer of an `ℝ≥0∞` integral identity between finite integrands to the Bochner integrals of
their real parts. Private: a bookkeeping step of the moment computation. -/
private theorem integral_toReal_eq_of_lintegral_eq {F G : Ω → ℝ≥0∞}
    (hF : AEMeasurable F μ) (hG : AEMeasurable G μ)
    (hFtop : ∀ ω, F ω ≠ ∞) (hGtop : ∀ ω, G ω ≠ ∞)
    (hFG : ∫⁻ ω, F ω ∂μ = ∫⁻ ω, G ω ∂μ) :
    ∫ ω, (F ω).toReal ∂μ = ∫ ω, (G ω).toReal ∂μ := by
  rw [integral_toReal hF (ae_of_all _ fun ω => (hFtop ω).lt_top),
    integral_toReal hG (ae_of_all _ fun ω => (hGtop ω).lt_top), hFG]

/-- The abstract second-moment computation behind the `L²` rate: if the centred variables
`eᵢ - q` are uncorrelated with common variance `c`, then their average over `Fin n` has mean
square `c / n`. Private: it is an algebraic repackaging with no probabilistic content of its own. -/
private theorem integral_sq_average_sub [IsProbabilityMeasure μ] {e : ℕ → Ω → ℝ} {q : Ω → ℝ}
    {c : ℝ} (he : ∀ i, Measurable (e i)) (hq : Measurable q)
    (heb : ∀ i ω, |e i ω| ≤ 1) (hqb : ∀ ω, |q ω| ≤ 1)
    (hcov : ∀ i j, ∫ ω, (e i ω - q ω) * (e j ω - q ω) ∂μ = if i = j then c else 0)
    {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, ((n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, e i ω) - q ω) ^ 2 ∂μ = (n : ℝ)⁻¹ * c := by
  classical
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hdb : ∀ i ω, |e i ω - q ω| ≤ 2 := by
    intro i ω
    have h1 := abs_le.mp (heb i ω)
    have h2 := abs_le.mp (hqb ω)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hInt : ∀ i j, Integrable (fun ω => (e i ω - q ω) * (e j ω - q ω)) μ := by
    intro i j
    refine Integrable.of_bound (((he i).sub hq).mul ((he j).sub hq)).aestronglyMeasurable 4
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [hdb i ω, hdb j ω, abs_nonneg (e i ω - q ω), abs_nonneg (e j ω - q ω)]
  have hstep : ∀ ω, ((n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, e i ω) - q ω) ^ 2
      = (n : ℝ)⁻¹ ^ 2 * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          (e i ω - q ω) * (e j ω - q ω) := by
    intro ω
    have h1 : (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, e i ω) - q ω
        = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (e i ω - q ω) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    rw [h1, mul_pow, sq (∑ i ∈ Finset.range n, (e i ω - q ω)), Finset.sum_mul_sum]
  simp_rw [hstep]
  rw [integral_const_mul,
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hInt i j]
  have hrow : ∀ i ∈ Finset.range n,
      ∫ ω, ∑ j ∈ Finset.range n, (e i ω - q ω) * (e j ω - q ω) ∂μ = c := by
    intro i hi
    rw [integral_finsetSum _ fun j _ => hInt i j]
    simp_rw [hcov]
    simp [Finset.sum_ite_eq, Finset.mem_range.mp hi]
  rw [Finset.sum_congr rfl hrow, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-- **The `L²` rate for empirical frequencies.** For a conditionally i.i.d. process with directing
measure `ν` and a measurable set `B`, the empirical frequency of `B` among the first `n`
coordinates approximates `ω ↦ (ν ω) B` with mean square error
`(∫ (ν ·) B - ∫ ((ν ·) B) ^ 2) / n`.

This is the second-moment law of large numbers for the conditional predicate, read straight off the
joint-law disintegration: the cross term `∫ (ν ·) B · 1_{Xᵢ ∈ B}` is the one moment that the
mixture identity alone does not determine. -/
theorem ConditionallyIIDWith.integral_empiricalFrequency_sub_sq [IsProbabilityMeasure μ]
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, Measurable (X i)) (hB : MeasurableSet B)
    {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, ((n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω)
          - ((ν ω : Measure α) B).toReal) ^ 2 ∂μ
      = (n : ℝ)⁻¹ * (∫ ω, ((ν ω : Measure α) B).toReal ∂μ
          - ∫ ω, ((ν ω : Measure α) B).toReal ^ 2 ∂μ) := by
  classical
  have hν := h.measurable_directing
  have hu : Measurable fun ω => (ν ω : Measure α) B :=
    (Measure.measurable_coe hB).comp (measurable_subtype_coe.comp hν)
  have hq : Measurable fun ω => ((ν ω : Measure α) B).toReal := hu.ennreal_toReal
  have he : ∀ i, Measurable ((X i ⁻¹' B).indicator (1 : Ω → ℝ)) := fun i =>
    measurable_one.indicator (hX i hB)
  have hutop : ∀ ω, (ν ω : Measure α) B ≠ ∞ := fun ω => measure_ne_top _ _
  have hindtop : ∀ (s : Set Ω) (ω : Ω), s.indicator (1 : Ω → ℝ≥0∞) ω ≠ ∞ := by
    intro s ω
    by_cases hmem : ω ∈ s <;> simp [hmem]
  have hindReal : ∀ (s : Set Ω) (ω : Ω),
      (s.indicator (1 : Ω → ℝ≥0∞) ω).toReal = s.indicator (1 : Ω → ℝ) ω := by
    intro s ω
    by_cases hmem : ω ∈ s <;> simp [hmem]
  -- the three moments supplied by the weighted block identity
  have hEq1 : ∀ i, ∫ ω, (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω ∂μ
      = ∫ ω, ((ν ω : Measure α) B).toReal ∂μ := by
    intro i
    have hlin : ∫⁻ ω, (X i ⁻¹' B).indicator (1 : Ω → ℝ≥0∞) ω ∂μ
        = ∫⁻ ω, (ν ω : Measure α) B ∂μ := by
      simpa using h.lintegral_mul_indicator_single (g := fun _ => 1) hX i measurable_const hB
    have := integral_toReal_eq_of_lintegral_eq (measurable_one.indicator (hX i hB)).aemeasurable
      hu.aemeasurable (hindtop _) hutop hlin
    simpa [hindReal] using this
  have hEq2 : ∀ i j, i ≠ j → ∫ ω, (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω
        * (X j ⁻¹' B).indicator (1 : Ω → ℝ) ω ∂μ
      = ∫ ω, ((ν ω : Measure α) B).toReal ^ 2 ∂μ := by
    intro i j hij
    have hlin : ∫⁻ ω, (X i ⁻¹' B ∩ X j ⁻¹' B).indicator (1 : Ω → ℝ≥0∞) ω ∂μ
        = ∫⁻ ω, (ν ω : Measure α) B ^ 2 ∂μ := by
      simpa using h.lintegral_mul_indicator_pair (g := fun _ => 1) hX hij measurable_const hB
    have := integral_toReal_eq_of_lintegral_eq
      (measurable_one.indicator ((hX i hB).inter (hX j hB))).aemeasurable
      (hu.pow_const 2).aemeasurable (hindtop _) (fun ω => by simp [hutop ω]) hlin
    have hprod : ∀ ω, ((X i ⁻¹' B ∩ X j ⁻¹' B).indicator (1 : Ω → ℝ≥0∞) ω).toReal
        = (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω * (X j ⁻¹' B).indicator (1 : Ω → ℝ) ω := by
      intro ω
      by_cases h1 : ω ∈ X i ⁻¹' B <;> by_cases h2 : ω ∈ X j ⁻¹' B <;>
        simp [h1, h2]
    simpa [hprod, ENNReal.toReal_pow] using this
  have hEq3 : ∀ i, ∫ ω, ((ν ω : Measure α) B).toReal
        * (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω ∂μ
      = ∫ ω, ((ν ω : Measure α) B).toReal ^ 2 ∂μ := by
    intro i
    have hg : Measurable fun p : ProbabilityMeasure α => (p : Measure α) B :=
      (Measure.measurable_coe hB).comp measurable_subtype_coe
    have hlin := h.lintegral_mul_indicator_single (g := fun p => (p : Measure α) B) hX i hg hB
    have := integral_toReal_eq_of_lintegral_eq
      (hu.mul (measurable_one.indicator (hX i hB))).aemeasurable (hu.mul hu).aemeasurable
      (fun ω => ENNReal.mul_ne_top (hutop ω) (hindtop _ ω))
      (fun ω => ENNReal.mul_ne_top (hutop ω) (hutop ω)) hlin
    simpa [ENNReal.toReal_mul, hindReal, sq] using this
  -- bounds
  have hq0 : ∀ ω, 0 ≤ ((ν ω : Measure α) B).toReal := fun _ => ENNReal.toReal_nonneg
  have hq1 : ∀ ω, ((ν ω : Measure α) B).toReal ≤ 1 := by
    intro ω
    simpa using
      ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := (ν ω : Measure α)) (s := B))
  have he0 : ∀ i ω, 0 ≤ (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω := fun i ω =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have he1 : ∀ i ω, (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω ≤ 1 := by
    intro i ω
    by_cases hmem : ω ∈ X i ⁻¹' B <;> simp [hmem]
  -- the centred variables are uncorrelated with common variance `∫ q - ∫ q²`
  have hcov : ∀ i j, ∫ ω, ((X i ⁻¹' B).indicator (1 : Ω → ℝ) ω - ((ν ω : Measure α) B).toReal)
        * ((X j ⁻¹' B).indicator (1 : Ω → ℝ) ω - ((ν ω : Measure α) B).toReal) ∂μ
      = if i = j then
          (∫ ω, ((ν ω : Measure α) B).toReal ∂μ - ∫ ω, ((ν ω : Measure α) B).toReal ^ 2 ∂μ)
        else 0 := by
    intro i j
    have hi1 : Integrable (fun ω => (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω
        * (X j ⁻¹' B).indicator (1 : Ω → ℝ) ω) μ := by
      refine Integrable.of_bound ((he i).mul (he j)).aestronglyMeasurable 1
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (he0 i ω), abs_of_nonneg (he0 j ω)]
      nlinarith [he0 i ω, he0 j ω, he1 i ω, he1 j ω]
    have hi2 : Integrable (fun ω => ((ν ω : Measure α) B).toReal
        * (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω) μ := by
      refine Integrable.of_bound (hq.mul (he i)).aestronglyMeasurable 1
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq0 ω), abs_of_nonneg (he0 i ω)]
      nlinarith [hq0 ω, hq1 ω, he0 i ω, he1 i ω]
    have hi3 : Integrable (fun ω => ((ν ω : Measure α) B).toReal
        * (X j ⁻¹' B).indicator (1 : Ω → ℝ) ω) μ := by
      refine Integrable.of_bound (hq.mul (he j)).aestronglyMeasurable 1
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq0 ω), abs_of_nonneg (he0 j ω)]
      nlinarith [hq0 ω, hq1 ω, he0 j ω, he1 j ω]
    have hi4 : Integrable (fun ω => ((ν ω : Measure α) B).toReal ^ 2) μ := by
      refine Integrable.of_bound (hq.pow_const 2).aestronglyMeasurable 1
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [hq0 ω, hq1 ω]
    have hexp : ∀ ω, ((X i ⁻¹' B).indicator (1 : Ω → ℝ) ω - ((ν ω : Measure α) B).toReal)
          * ((X j ⁻¹' B).indicator (1 : Ω → ℝ) ω - ((ν ω : Measure α) B).toReal)
        = (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω * (X j ⁻¹' B).indicator (1 : Ω → ℝ) ω
          - ((ν ω : Measure α) B).toReal * (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω
          - ((ν ω : Measure α) B).toReal * (X j ⁻¹' B).indicator (1 : Ω → ℝ) ω
          + ((ν ω : Measure α) B).toReal ^ 2 := by
      intro ω; ring
    have hiB : Integrable (fun ω => (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω
        * (X j ⁻¹' B).indicator (1 : Ω → ℝ) ω
        - ((ν ω : Measure α) B).toReal * (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω) μ := hi1.sub hi2
    have hiA : Integrable (fun ω => (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω
        * (X j ⁻¹' B).indicator (1 : Ω → ℝ) ω
        - ((ν ω : Measure α) B).toReal * (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω
        - ((ν ω : Measure α) B).toReal * (X j ⁻¹' B).indicator (1 : Ω → ℝ) ω) μ := hiB.sub hi3
    rw [integral_congr_ae (ae_of_all _ hexp), integral_add hiA hi4,
      integral_sub hiB hi3, integral_sub hi1 hi2]
    by_cases hij : i = j
    · subst hij
      have hsq : ∀ ω, (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω
          * (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω = (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω := by
        intro ω
        by_cases hmem : ω ∈ X i ⁻¹' B <;> simp [hmem]
      rw [if_pos rfl, integral_congr_ae (ae_of_all _ hsq), hEq1 i, hEq3 i]
      ring
    · rw [if_neg hij, hEq2 i j hij, hEq3 i, hEq3 j]
      ring
  exact integral_sq_average_sub he hq
    (fun i ω => abs_le.mpr ⟨by linarith [he0 i ω], he1 i ω⟩)
    (fun ω => abs_le.mpr ⟨by linarith [hq0 ω], hq1 ω⟩) hcov hn

/-- The mean square error of `ConditionallyIIDWith.integral_empiricalFrequency_sub_sq` is at most
`1 / n`: the variance factor is a difference of moments of a `[0, 1]`-valued variable. -/
theorem ConditionallyIIDWith.integral_empiricalFrequency_sub_sq_le [IsProbabilityMeasure μ]
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, Measurable (X i)) (hB : MeasurableSet B)
    {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, ((n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω)
          - ((ν ω : Measure α) B).toReal) ^ 2 ∂μ ≤ (n : ℝ)⁻¹ := by
  have hν := h.measurable_directing
  have hq : Measurable fun ω => ((ν ω : Measure α) B).toReal :=
    ((Measure.measurable_coe hB).comp (measurable_subtype_coe.comp hν)).ennreal_toReal
  have hq0 : ∀ ω, 0 ≤ ((ν ω : Measure α) B).toReal := fun _ => ENNReal.toReal_nonneg
  have hq1 : ∀ ω, ((ν ω : Measure α) B).toReal ≤ 1 := by
    intro ω
    simpa using
      ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := (ν ω : Measure α)) (s := B))
  have hqint : Integrable (fun ω => ((ν ω : Measure α) B).toReal) μ :=
    Integrable.of_bound hq.aestronglyMeasurable 1 <| ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hq0 ω], hq1 ω⟩
  have hA : ∫ ω, ((ν ω : Measure α) B).toReal ∂μ ≤ 1 := by
    have := integral_mono hqint (integrable_const (1 : ℝ)) hq1
    simpa using this
  have hC : 0 ≤ ∫ ω, ((ν ω : Measure α) B).toReal ^ 2 ∂μ :=
    integral_nonneg fun ω => by positivity
  have hn' : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  rw [h.integral_empiricalFrequency_sub_sq hX hB hn]
  nlinarith [hA, hC, hn']

/-! ### Uniqueness -/

/-- Two directing measures of the same process assign the same mass to each fixed measurable set,
almost everywhere.

Both are approximated in `L²` by the *same* empirical frequencies, at a rate that does not depend
on the witness, so the triangle inequality forces their difference to vanish in `L²`. -/
theorem ConditionallyIIDWith.ae_measure_apply_eq [IsProbabilityMeasure μ]
    (hX : ∀ i, Measurable (X i)) (h : ConditionallyIIDWith μ X ν)
    (h' : ConditionallyIIDWith μ X ν') (hB : MeasurableSet B) :
    (fun ω => (ν ω : Measure α) B) =ᵐ[μ] fun ω => (ν' ω : Measure α) B := by
  have hqm : ∀ ρ : Ω → ProbabilityMeasure α, Measurable ρ →
      Measurable fun ω => ((ρ ω : Measure α) B).toReal := fun ρ hρ =>
    ((Measure.measurable_coe hB).comp (measurable_subtype_coe.comp hρ)).ennreal_toReal
  have hq0 : ∀ (ρ : Ω → ProbabilityMeasure α) (ω : Ω), 0 ≤ ((ρ ω : Measure α) B).toReal :=
    fun _ _ => ENNReal.toReal_nonneg
  have hq1 : ∀ (ρ : Ω → ProbabilityMeasure α) (ω : Ω), ((ρ ω : Measure α) B).toReal ≤ 1 := by
    intro ρ ω
    simpa using
      ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := (ρ ω : Measure α)) (s := B))
  have hem : ∀ n : ℕ, Measurable fun ω =>
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω := by
    intro n
    exact measurable_const.mul
      (Finset.measurable_sum _ fun i _ => measurable_one.indicator (hX i hB))
  have heb : ∀ (n : ℕ) (ω : Ω),
      |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω| ≤ 1 := by
    intro n ω
    have h0 : ∀ i, 0 ≤ (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω := fun i =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    have h1 : ∀ i, (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω ≤ 1 := by
      intro i
      by_cases hmem : ω ∈ X i ⁻¹' B <;> simp [hmem]
    have hs0 : 0 ≤ ∑ i ∈ Finset.range n, (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω :=
      Finset.sum_nonneg fun i _ => h0 i
    have hsn : ∑ i ∈ Finset.range n, (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω ≤ (n : ℝ) := by
      calc ∑ i ∈ Finset.range n, (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω
          ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun i _ => h1 i
        _ = (n : ℝ) := by simp
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast hpos
      rw [abs_of_nonneg (mul_nonneg (by positivity) hs0), ← div_eq_inv_mul, div_le_one hnpos]
      exact hsn
  set d : Ω → ℝ := fun ω =>
    ((ν ω : Measure α) B).toReal - ((ν' ω : Measure α) B).toReal with hd_def
  have hdm : Measurable d := (hqm ν h.measurable_directing).sub (hqm ν' h'.measurable_directing)
  have hdint : Integrable (fun ω => d ω ^ 2) μ := by
    refine Integrable.of_bound (hdm.pow_const 2).aestronglyMeasurable 1
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [hq0 ν ω, hq1 ν ω, hq0 ν' ω, hq1 ν' ω]
  have hbound : ∀ n : ℕ, 1 ≤ n → ∫ ω, d ω ^ 2 ∂μ ≤ 4 / n := by
    intro n hn
    have hn0 : n ≠ 0 := by omega
    set Y : Ω → ℝ := fun ω =>
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω
    have hi1 : Integrable (fun ω => (Y ω - ((ν ω : Measure α) B).toReal) ^ 2) μ := by
      refine Integrable.of_bound
        (((hem n).sub (hqm ν h.measurable_directing)).pow_const 2).aestronglyMeasurable 4
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [abs_le.mp (heb n ω), hq0 ν ω, hq1 ν ω]
    have hi2 : Integrable (fun ω => (Y ω - ((ν' ω : Measure α) B).toReal) ^ 2) μ := by
      refine Integrable.of_bound
        (((hem n).sub (hqm ν' h'.measurable_directing)).pow_const 2).aestronglyMeasurable 4
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [abs_le.mp (heb n ω), hq0 ν' ω, hq1 ν' ω]
    have hpt : ∀ ω, d ω ^ 2 ≤ 2 * (Y ω - ((ν ω : Measure α) B).toReal) ^ 2
        + 2 * (Y ω - ((ν' ω : Measure α) B).toReal) ^ 2 := by
      intro ω
      simp only [hd_def]
      nlinarith [sq_nonneg (((ν ω : Measure α) B).toReal + ((ν' ω : Measure α) B).toReal
        - 2 * Y ω)]
    calc ∫ ω, d ω ^ 2 ∂μ
        ≤ ∫ ω, (2 * (Y ω - ((ν ω : Measure α) B).toReal) ^ 2
            + 2 * (Y ω - ((ν' ω : Measure α) B).toReal) ^ 2) ∂μ :=
          integral_mono hdint (((hi1.const_mul 2).add (hi2.const_mul 2))) hpt
      _ = 2 * ∫ ω, (Y ω - ((ν ω : Measure α) B).toReal) ^ 2 ∂μ
            + 2 * ∫ ω, (Y ω - ((ν' ω : Measure α) B).toReal) ^ 2 ∂μ := by
          rw [integral_add (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul,
            integral_const_mul]
      _ ≤ 2 * (n : ℝ)⁻¹ + 2 * (n : ℝ)⁻¹ := by
          gcongr
          · exact h.integral_empiricalFrequency_sub_sq_le hX hB hn0
          · exact h'.integral_empiricalFrequency_sub_sq_le hX hB hn0
      _ = 4 / n := by rw [div_eq_mul_inv]; ring
  have hle : ∫ ω, d ω ^ 2 ∂μ ≤ 0 :=
    ge_of_tendsto (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ))
      (eventually_atTop.2 ⟨1, fun n hn => hbound n hn⟩)
  have hzero : ∫ ω, d ω ^ 2 ∂μ = 0 :=
    le_antisymm hle (integral_nonneg fun ω => by positivity)
  have hae : (fun ω => d ω ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => by positivity) hdint).mp hzero
  filter_upwards [hae] with ω hω
  have hd0 : d ω = 0 := by
    have : d ω ^ 2 = 0 := hω
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have : ((ν ω : Measure α) B).toReal = ((ν' ω : Measure α) B).toReal := by
    simp only [hd_def] at hd0
    linarith
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp this

/-- Almost sure equality of two random probability measures follows from a.e. equality of their
masses on each fixed measurable set, when the σ-algebra is countably generated. Private: the final
promotion step, phrased for the two witnesses at hand. -/
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
    (hX : ∀ i, Measurable (X i)) (h : ConditionallyIIDWith μ X ν)
    (h' : ConditionallyIIDWith μ X ν') : ν =ᵐ[μ] ν' :=
  ae_eq_of_forall_apply_ae_eq fun _ hs => h.ae_measure_apply_eq hX h' hs

end Probability

end TauCeti
