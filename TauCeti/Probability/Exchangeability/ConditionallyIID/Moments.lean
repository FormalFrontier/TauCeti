/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
-- Non-public: the `measurable_probabilityMeasure_toMeasure_apply` lemmas evaluate a random measure
-- at a fixed measurable set, in the `ℝ≥0∞` and `.toReal` forms.
import TauCeti.MeasureTheory.Measure.ProbabilityMeasureExt

/-!
# Conditional moment identities and the empirical-frequency rate

The second-moment consequences of the joint-law disintegration `ConditionallyIIDWith`, culminating
in an exact finite-sample formula for the mean square error of an empirical frequency.

## Main results

* `ConditionallyIIDWith.lintegral_mul_indicator_iInter` — the weighted block identity: testing the
  disintegration against `g (ν ω)` times the indicator of a block rectangle turns the block into
  the power `(ν ω) B ^ m`. Its one- and two-coordinate specializations are
  `ConditionallyIIDWith.lintegral_mul_indicator_single` and
  `ConditionallyIIDWith.lintegral_mul_indicator_pair`.
* `ConditionallyIIDWith.integral_empiricalFrequency_sub_sq` — the exact rate: the empirical
  frequency of a measurable set `B` along the first `n` coordinates approximates `(ν ·) B` with
  mean square error exactly `(∫ (ν ·) B - ∫ ((ν ·) B) ^ 2) / n`.
* `ConditionallyIIDWith.integral_empiricalFrequency_sub_sq_le` — its `≤ 1 / n` corollary.
* `ConditionallyIIDWith.tendsto_integral_empiricalFrequency_sub_sq` — the limit that corollary
  gives: fixed-set empirical frequencies converge to `(ν ·) B` in mean square.

## Implementation

The joint-law form of `ConditionallyIIDWith` gives the second moments directly, with no conditional
expectations. Writing `q ω = (ν ω) B` and `eᵢ` for the indicator of `Xᵢ ∈ B`, the weighted block
identity supplies

```text
∫ eᵢ = ∫ q,      ∫ eᵢ eⱼ = ∫ q²  (i ≠ j),      ∫ q eᵢ = ∫ q²,
```

the last of which is the genuinely *conditional* input: it constrains the joint law of `(ν, Xᵢ)`,
which the mixture predicate `MixedIIDWith` would leave free. The centred variables `eᵢ - q` are
therefore uncorrelated with common variance `∫ q - ∫ q²`, which is exactly the stated rate.

The identities are stated in `ℝ≥0∞` first, where the disintegration lives, and converted to Bochner
integrals by the private machinery below; the coordinates are only assumed a.e. measurable, as
elsewhere in the measure-theoretic exchangeability API.

These estimates are consumed by `ConditionallyIID.Unique` for a.e. uniqueness of the directing
measure.

The `O(1/n)` rate is **not** summable, so it gives mean-square convergence but not almost-sure
convergence; the latter needs a different argument. Convergence on a countable determining class,
empirical probability measures as objects, and weak convergence — which additionally requires a
chosen Polish topology, since `StandardBorelSpace α` asserts only that *some* compatible topology
exists — are all separate developments.
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
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, AEMeasurable (X i) μ)
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
  have hΦ : AEMeasurable (fun ω => (ν ω, fun i : Fin m => X (k i) ω)) μ :=
    hν.aemeasurable.prodMk (aemeasurable_pi_lambda _ fun i => hX (k i))
  have hκ : AEMeasurable (fun ω =>
      (Measure.dirac (ν ω)).prod (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure) μ :=
    (TauCeti.MeasureTheory.measurable_dirac_prod_probabilityMeasure_pi_const_toMeasure ν
      hν).aemeasurable
  have key : ∫⁻ z, F z ∂(μ.map fun ω => (ν ω, fun i : Fin m => X (k i) ω))
      = ∫⁻ z, F z ∂(μ.bind fun ω =>
          (Measure.dirac (ν ω)).prod (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure) := by
    rw [h.jointLaw_eq_disintegration k hk]
  rw [lintegral_map' hF.aemeasurable hΦ, Measure.lintegral_bind hκ hF.aemeasurable] at key
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
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, AEMeasurable (X i) μ) (i : ℕ)
    {g : ProbabilityMeasure α → ℝ≥0∞} (hg : Measurable g) (hB : MeasurableSet B) :
    ∫⁻ ω, g (ν ω) * (X i ⁻¹' B).indicator (1 : Ω → ℝ≥0∞) ω ∂μ
      = ∫⁻ ω, g (ν ω) * (ν ω : Measure α) B ∂μ := by
  have hinj : Function.Injective (fun _ : Fin 1 => i) := fun a b _ => Subsingleton.elim a b
  simpa [Set.iInter_const] using h.lintegral_mul_indicator_iInter hX hinj hg hB

/-- Two-coordinate form of the weighted block identity, at distinct indices. -/
theorem ConditionallyIIDWith.lintegral_mul_indicator_pair
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, AEMeasurable (X i) μ) {i j : ℕ} (hij : i ≠ j)
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

/-- A product of two `[0, 1]`-valued functions is integrable on a finite measure space, being
bounded by `1`. Every summand of the covariance expansion below is of this shape. -/
private theorem integrable_mul_of_nonneg_of_le_one [IsFiniteMeasure μ] {u v : Ω → ℝ}
    (hu : AEMeasurable u μ) (hv : AEMeasurable v μ)
    (hu01 : ∀ᵐ ω ∂μ, 0 ≤ u ω ∧ u ω ≤ 1) (hv01 : ∀ᵐ ω ∂μ, 0 ≤ v ω ∧ v ω ≤ 1) :
    Integrable (fun ω => u ω * v ω) μ := by
  refine Integrable.of_bound (hu.mul hv).aestronglyMeasurable 1 ?_
  filter_upwards [hu01, hv01] with ω ⟨hu0, hu1⟩ ⟨hv0, hv1⟩
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hu0, abs_of_nonneg hv0]
  nlinarith

/-- **Expanding a centred product.** Whenever the four products are integrable, the integral of
`(u - q)(v - q)` splits into the four moments of the product expansion. -/
private theorem integral_sub_mul_sub {u v q : Ω → ℝ}
    (hi1 : Integrable (fun ω => u ω * v ω) μ) (hi2 : Integrable (fun ω => q ω * u ω) μ)
    (hi3 : Integrable (fun ω => q ω * v ω) μ) (hi4 : Integrable (fun ω => q ω ^ 2) μ) :
    ∫ ω, (u ω - q ω) * (v ω - q ω) ∂μ
      = ∫ ω, u ω * v ω ∂μ - ∫ ω, q ω * u ω ∂μ - ∫ ω, q ω * v ω ∂μ
        + ∫ ω, q ω ^ 2 ∂μ := by
  have hexp : ∀ ω, (u ω - q ω) * (v ω - q ω)
      = u ω * v ω - q ω * u ω - q ω * v ω + q ω ^ 2 := fun ω => by ring
  have hiB : Integrable (fun ω => u ω * v ω - q ω * u ω) μ := hi1.sub hi2
  have hiA : Integrable (fun ω => u ω * v ω - q ω * u ω - q ω * v ω) μ := hiB.sub hi3
  rw [integral_congr_ae (ae_of_all _ hexp), integral_add hiA hi4,
    integral_sub hiB hi3, integral_sub hi1 hi2]

/-- The abstract second-moment computation behind the `L²` rate: if the centred variables
`eᵢ - q` are uncorrelated with common variance `c`, then their average over `Fin n` has mean
square `c / n`. Private: it is an algebraic repackaging with no probabilistic content of its own. -/
private theorem integral_sq_average_sub [IsProbabilityMeasure μ] {e : ℕ → Ω → ℝ} {q : Ω → ℝ}
    {c : ℝ} (he : ∀ i, AEMeasurable (e i) μ) (hq : AEMeasurable q μ)
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

omit [MeasurableSpace Ω] in
/-- The real part of a `{0, 1}`-valued `ℝ≥0∞` indicator is the corresponding real indicator. -/
private theorem toReal_indicator_one (s : Set Ω) (ω : Ω) :
    (s.indicator (1 : Ω → ℝ≥0∞) ω).toReal = s.indicator (1 : Ω → ℝ) ω := by
  -- Mathlib's `map_indicator` at `ENNReal.toRealHom`. `⇑ENNReal.toRealHom` and `.toReal` are
  -- definitionally but not syntactically equal, hence the `exact` rather than `rfl`.
  have h := map_indicator ENNReal.toRealHom s (1 : Ω → ℝ≥0∞) ω
  simp only [Function.comp_def] at h
  exact h

omit [MeasurableSpace Ω] in
/-- An `ℝ≥0∞` indicator of `1` is finite. -/
private theorem indicator_one_ne_top (s : Set Ω) (ω : Ω) :
    s.indicator (1 : Ω → ℝ≥0∞) ω ≠ ∞ := by
  by_cases hmem : ω ∈ s <;> simp [hmem]

variable {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α} {B : Set α}

/-- **First moment.** The integral of the indicator of `{Xᵢ ∈ B}` equals the integral of the
directing measure's mass on `B`. (`μ` is an arbitrary measure here; under a probability measure
this reads as the two having the same probability.) -/
private theorem ConditionallyIIDWith.integral_indicator_single
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, AEMeasurable (X i) μ) (hB : MeasurableSet B)
    (i : ℕ) :
    ∫ ω, (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω ∂μ
      = ∫ ω, ((ν ω : Measure α) B).toReal ∂μ := by
  have hu : Measurable fun ω => (ν ω : Measure α) B :=
    (TauCeti.MeasureTheory.measurable_probabilityMeasure_toMeasure_apply hB).comp
      h.measurable_directing
  have hlin : ∫⁻ ω, (X i ⁻¹' B).indicator (1 : Ω → ℝ≥0∞) ω ∂μ
      = ∫⁻ ω, (ν ω : Measure α) B ∂μ := by
    simpa using h.lintegral_mul_indicator_single (g := fun _ => 1) hX i measurable_const hB
  have := integral_toReal_eq_of_lintegral_eq
    (measurable_one.aemeasurable.indicator₀ ((hX i).nullMeasurableSet_preimage hB))
    hu.aemeasurable (indicator_one_ne_top _) (fun ω => measure_ne_top _ _) hlin
  simpa [toReal_indicator_one] using this

/-- **Pair moment.** For distinct indices the integral of the product of the two indicators
equals the integral of the squared mass — conditional independence, read at two indices. -/
private theorem ConditionallyIIDWith.integral_indicator_pair
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, AEMeasurable (X i) μ) (hB : MeasurableSet B)
    {i j : ℕ} (hij : i ≠ j) :
    ∫ ω, (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω * (X j ⁻¹' B).indicator (1 : Ω → ℝ) ω ∂μ
      = ∫ ω, ((ν ω : Measure α) B).toReal ^ 2 ∂μ := by
  have hu : Measurable fun ω => (ν ω : Measure α) B :=
    (TauCeti.MeasureTheory.measurable_probabilityMeasure_toMeasure_apply hB).comp
      h.measurable_directing
  have hlin : ∫⁻ ω, (X i ⁻¹' B ∩ X j ⁻¹' B).indicator (1 : Ω → ℝ≥0∞) ω ∂μ
      = ∫⁻ ω, (ν ω : Measure α) B ^ 2 ∂μ := by
    simpa using h.lintegral_mul_indicator_pair (g := fun _ => 1) hX hij measurable_const hB
  have := integral_toReal_eq_of_lintegral_eq
    (measurable_one.aemeasurable.indicator₀
      (((hX i).nullMeasurableSet_preimage hB).inter ((hX j).nullMeasurableSet_preimage hB)))
    (hu.pow_const 2).aemeasurable (indicator_one_ne_top _)
    (fun ω => by simp [measure_ne_top (ν ω : Measure α) B]) hlin
  have hprod : ∀ ω, ((X i ⁻¹' B ∩ X j ⁻¹' B).indicator (1 : Ω → ℝ≥0∞) ω).toReal
      = (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω * (X j ⁻¹' B).indicator (1 : Ω → ℝ) ω := by
    intro ω
    by_cases h1 : ω ∈ X i ⁻¹' B <;> by_cases h2 : ω ∈ X j ⁻¹' B <;> simp [h1, h2]
  simpa [hprod, ENNReal.toReal_pow] using this

/-- **Cross moment.** Weighting one coordinate's indicator by the directing mass integrates to the
same squared quantity — the moment the mixture identity alone does not determine. -/
private theorem ConditionallyIIDWith.integral_directing_mul_indicator
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, AEMeasurable (X i) μ) (hB : MeasurableSet B)
    (i : ℕ) :
    ∫ ω, ((ν ω : Measure α) B).toReal * (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω ∂μ
      = ∫ ω, ((ν ω : Measure α) B).toReal ^ 2 ∂μ := by
  have hu : Measurable fun ω => (ν ω : Measure α) B :=
    (TauCeti.MeasureTheory.measurable_probabilityMeasure_toMeasure_apply hB).comp
      h.measurable_directing
  have hg : Measurable fun p : ProbabilityMeasure α => (p : Measure α) B :=
    TauCeti.MeasureTheory.measurable_probabilityMeasure_toMeasure_apply hB
  have hlin := h.lintegral_mul_indicator_single (g := fun p => (p : Measure α) B) hX i hg hB
  have := integral_toReal_eq_of_lintegral_eq
    (hu.aemeasurable.mul
      (measurable_one.aemeasurable.indicator₀ ((hX i).nullMeasurableSet_preimage hB)))
    (hu.mul hu).aemeasurable
    (fun ω => ENNReal.mul_ne_top (measure_ne_top _ _) (indicator_one_ne_top _ ω))
    (fun ω => ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)) hlin
  simpa [ENNReal.toReal_mul, toReal_indicator_one, sq] using this

/-- **The centred indicators are uncorrelated, with common variance `∫ q - ∫ q²`.** Writing
`q ω = ((ν ω) B).toReal` for the directing mass of `B`, the centred variables
`1_{Xᵢ ∈ B} - q` have vanishing cross moments and common second moment `∫ q - ∫ q²`.

This is the covariance hypothesis of `integral_sq_average_sub`, and it is the only place the
conditional i.i.d. structure enters beyond measurability of the directing map. -/
private theorem ConditionallyIIDWith.integral_indicator_sub_directing_mul_indicator_sub_directing
    [IsFiniteMeasure μ] (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, AEMeasurable (X i) μ)
    (hB : MeasurableSet B) (i j : ℕ) :
    ∫ ω, ((X i ⁻¹' B).indicator (1 : Ω → ℝ) ω - ((ν ω : Measure α) B).toReal)
        * ((X j ⁻¹' B).indicator (1 : Ω → ℝ) ω - ((ν ω : Measure α) B).toReal) ∂μ
      = if i = j then
          (∫ ω, ((ν ω : Measure α) B).toReal ∂μ - ∫ ω, ((ν ω : Measure α) B).toReal ^ 2 ∂μ)
        else 0 := by
  classical
  have hq : Measurable fun ω => ((ν ω : Measure α) B).toReal :=
    (TauCeti.MeasureTheory.measurable_probabilityMeasure_toMeasure_apply_toReal hB).comp
      h.measurable_directing
  have he : ∀ i, AEMeasurable ((X i ⁻¹' B).indicator (1 : Ω → ℝ)) μ := fun i =>
    measurable_one.aemeasurable.indicator₀ ((hX i).nullMeasurableSet_preimage hB)
  have hb : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω
      ∧ (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω ≤ 1 := fun i => ae_of_all _ fun ω => by
    by_cases hmem : ω ∈ X i ⁻¹' B <;> simp [hmem]
  have hbq : ∀ᵐ ω ∂μ, 0 ≤ ((ν ω : Measure α) B).toReal
      ∧ ((ν ω : Measure α) B).toReal ≤ 1 := ae_of_all _ fun ω =>
    ⟨ENNReal.toReal_nonneg, measureReal_le_one⟩
  rw [integral_sub_mul_sub
    (integrable_mul_of_nonneg_of_le_one (he i) (he j) (hb i) (hb j))
    (integrable_mul_of_nonneg_of_le_one hq.aemeasurable (he i) hbq (hb i))
    (integrable_mul_of_nonneg_of_le_one hq.aemeasurable (he j) hbq (hb j))
    (by simpa [sq] using
      integrable_mul_of_nonneg_of_le_one hq.aemeasurable hq.aemeasurable hbq hbq)]
  by_cases hij : i = j
  · -- On the diagonal the indicator is idempotent, so the first moment appears in place of the
    -- pair moment and the variance is `∫ q - ∫ q²`.
    subst hij
    have hsq : ∀ ω, (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω
        * (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω = (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω := by
      intro ω
      by_cases hmem : ω ∈ X i ⁻¹' B <;> simp [hmem]
    rw [if_pos rfl, integral_congr_ae (ae_of_all _ hsq),
      h.integral_indicator_single hX hB i, h.integral_directing_mul_indicator hX hB i]
    ring
  · -- Off the diagonal the pair moment and both cross moments are `∫ q²`, so the four terms of
    -- the expansion cancel.
    rw [if_neg hij, h.integral_indicator_pair hX hB hij,
      h.integral_directing_mul_indicator hX hB i, h.integral_directing_mul_indicator hX hB j]
    ring

/-- **The `L²` rate for empirical frequencies.** For a conditionally i.i.d. process with directing
measure `ν` and a measurable set `B`, the empirical frequency of `B` among the first `n`
coordinates approximates `ω ↦ (ν ω) B` with mean square error
`(∫ (ν ·) B - ∫ ((ν ·) B) ^ 2) / n`.

This is the second-moment law of large numbers for the conditional predicate, read straight off the
joint-law disintegration: the cross term `∫ (ν ·) B · 1_{Xᵢ ∈ B}` is the one moment that the
mixture identity alone does not determine. -/
theorem ConditionallyIIDWith.integral_empiricalFrequency_sub_sq [IsProbabilityMeasure μ]
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, AEMeasurable (X i) μ) (hB : MeasurableSet B)
    {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, ((n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω)
          - ((ν ω : Measure α) B).toReal) ^ 2 ∂μ
      = (n : ℝ)⁻¹ * (∫ ω, ((ν ω : Measure α) B).toReal ∂μ
          - ∫ ω, ((ν ω : Measure α) B).toReal ^ 2 ∂μ) := by
  classical
  have hq : Measurable fun ω => ((ν ω : Measure α) B).toReal :=
    (TauCeti.MeasureTheory.measurable_probabilityMeasure_toMeasure_apply_toReal hB).comp
      h.measurable_directing
  have he : ∀ i, AEMeasurable ((X i ⁻¹' B).indicator (1 : Ω → ℝ)) μ := fun i =>
    measurable_one.aemeasurable.indicator₀ ((hX i).nullMeasurableSet_preimage hB)
  -- the `[0, 1]` bounds feeding the `|·| ≤ 1` hypotheses of `integral_sq_average_sub`
  have hq0 : ∀ ω, 0 ≤ ((ν ω : Measure α) B).toReal := fun _ => ENNReal.toReal_nonneg
  have hq1 : ∀ ω, ((ν ω : Measure α) B).toReal ≤ 1 := fun _ => measureReal_le_one
  have he0 : ∀ i ω, 0 ≤ (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω := fun i ω =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have he1 : ∀ i ω, (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω ≤ 1 := by
    intro i ω
    by_cases hmem : ω ∈ X i ⁻¹' B <;> simp [hmem]
  exact integral_sq_average_sub he hq.aemeasurable
    (fun i ω => abs_le.mpr ⟨by linarith [he0 i ω], he1 i ω⟩)
    (fun ω => abs_le.mpr ⟨by linarith [hq0 ω], hq1 ω⟩)
    (h.integral_indicator_sub_directing_mul_indicator_sub_directing hX hB) hn

/-- The mean square error of `ConditionallyIIDWith.integral_empiricalFrequency_sub_sq` is at most
`1 / n`: the variance factor is a difference of moments of a `[0, 1]`-valued variable. -/
theorem ConditionallyIIDWith.integral_empiricalFrequency_sub_sq_le [IsProbabilityMeasure μ]
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, AEMeasurable (X i) μ) (hB : MeasurableSet B)
    {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, ((n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω)
          - ((ν ω : Measure α) B).toReal) ^ 2 ∂μ ≤ (n : ℝ)⁻¹ := by
  have hq : Measurable fun ω => ((ν ω : Measure α) B).toReal :=
    (TauCeti.MeasureTheory.measurable_probabilityMeasure_toMeasure_apply_toReal hB).comp
      h.measurable_directing
  have hq0 : ∀ ω, 0 ≤ ((ν ω : Measure α) B).toReal := fun _ => ENNReal.toReal_nonneg
  have hq1 : ∀ ω, ((ν ω : Measure α) B).toReal ≤ 1 := fun _ => measureReal_le_one
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

/-! ### Convergence of empirical frequencies -/

/-- **Fixed-set empirical frequencies converge in mean square.** For a conditionally i.i.d. process,
the empirical frequency of a fixed measurable set `B` along the first `n` coordinates converges in
`L²` to the directing measure's evaluation `(ν ·) B`.

Indexed at `n + 1` so that no caller carries an `n ≠ 0` side condition. -/
theorem ConditionallyIIDWith.tendsto_integral_empiricalFrequency_sub_sq [IsProbabilityMeasure μ]
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, AEMeasurable (X i) μ) (hB : MeasurableSet B) :
    Tendsto (fun n : ℕ => ∫ ω, (((n + 1 : ℕ) : ℝ)⁻¹ *
          (∑ i ∈ Finset.range (n + 1), (X i ⁻¹' B).indicator (1 : Ω → ℝ) ω)
        - ((ν ω : Measure α) B).toReal) ^ 2 ∂μ) atTop (nhds 0) := by
  have hupper : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n => by
      rw [one_div]; norm_cast
  refine squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _) (fun n => ?_) hupper
  exact h.integral_empiricalFrequency_sub_sq_le hX hB (Nat.succ_ne_zero n)

end Probability

end TauCeti
