/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.CompletelyMonotone.LaplaceRepresentation
-- Non-public: tightness criteria for the shifted representing measures.
import Mathlib.MeasureTheory.Measure.TightNormed
-- Non-public: Bernstein's existence theorem supplies the representing measures of the shifts.
import TauCeti.Analysis.CompletelyMonotone.Bernstein.Theorem
-- Non-public: `finite_measure_cluster_limit` extracts the weak cluster point.
import TauCeti.MeasureTheory.Measure.Prokhorov

/-!
# Hausdorff--Bernstein--Widder theorem

This file proves the finite-measure form of the Hausdorff--Bernstein--Widder theorem for
completely monotone functions on the closed half-line: a function is continuous on `[0, ∞)`
and completely monotone on `(0, ∞)` if and only if it is the Laplace transform of a (unique)
finite positive measure on `ℝ≥0`.

The hard direction applies Bernstein's existence theorem
(`TauCeti.exists_representsLaplace_of_isCompletelyMonotone`) to the
positive shifts `t ↦ f (t + a)`, which satisfy the strong `IsCompletelyMonotone` predicate,
and passes to a weak cluster point of the representing measures as `a ↓ 0`; the tightness of
that family is an elementary Laplace-kernel tail estimate. The easy direction and the
uniqueness both live in `LaplaceRepresentation.lean`.

## Main declarations

* `TauCeti.exists_representsLaplace_of_isCompletelyMonotoneOnIci`
* `TauCeti.hausdorff_bernstein_widder`, `TauCeti.hausdorff_bernstein_widder_unique`

## References

The finite-measure representation is the Hausdorff--Bernstein--Widder theorem, after
S. Bernstein (1928) and D. V. Widder, *The Laplace Transform*, Chapter IV.

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem
  milestone).
-/

public section

open MeasureTheory Set Filter
open scoped BoundedContinuousFunction ContDiff ENNReal NNReal Topology

namespace TauCeti

/-! ## Hard direction: tightness of the shifted representing measures -/

/-- A finite family of finite measures is tight. -/
private lemma isTightMeasureSet_range_finite
    {ι : Type*} [Finite ι] (μ : ι → Measure ℝ≥0)
    (hfin : ∀ i, IsFiniteMeasure (μ i)) :
    IsTightMeasureSet (Set.range μ) := by
  classical
  let := Fintype.ofFinite ι
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  have hchoose : ∀ i, ∃ K : Set ℝ≥0, IsCompact K ∧ (μ i) Kᶜ ≤ ε := by
    intro i
    have : IsFiniteMeasure (μ i) := hfin i
    have htight : IsTightMeasureSet ({μ i} : Set (Measure ℝ≥0)) :=
      isTightMeasureSet_singleton
    obtain ⟨K, hKc, hKtail⟩ :=
      isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight ε hε
    exact ⟨K, hKc, hKtail (μ i) (by simp)⟩
  choose K hK_comp hK_tail using hchoose
  refine ⟨⋃ i, K i, isCompact_iUnion hK_comp, ?_⟩
  intro ν hν
  rcases hν with ⟨i, rfl⟩
  exact (measure_mono (compl_subset_compl.mpr (subset_iUnion K i))).trans (hK_tail i)

/-- The `∫⁻` of the bounded coordinate `p ↦ 1 - exp(-x·p)` against a measure that represents
`t ↦ f (t + δ)` by its Laplace transform equals `f δ - f (x + δ)` (for `x > 0`). This is the
Laplace-value identity behind the shifted-measure tail estimate. -/
private lemma lintegral_ofReal_one_sub_exp_representsLaplace
    {f : ℝ → ℝ} {μ : Measure ℝ≥0} [IsFiniteMeasure μ]
    {δ x : ℝ} (hμ : RepresentsLaplace (fun t : ℝ => f (t + δ)) μ) (hx : 0 < x) :
    ∫⁻ p : ℝ≥0, ENNReal.ofReal (1 - Real.exp (-(x * (p : ℝ)))) ∂μ
      = ENNReal.ofReal (f δ - f (x + δ)) := by
  have h_one : Integrable (fun _ : ℝ≥0 => (1 : ℝ)) μ := integrable_const 1
  have h_exp : Integrable (fun p : ℝ≥0 => Real.exp (-(x * (p : ℝ)))) μ :=
    integrable_exp_neg_mul μ hx.le
  have h_nonneg : 0 ≤ᵐ[μ] fun p : ℝ≥0 => 1 - Real.exp (-(x * (p : ℝ))) := by
    refine Filter.Eventually.of_forall fun p => ?_
    have hxp_nonneg : 0 ≤ x * (p : ℝ) := mul_nonneg hx.le p.2
    have hexp_le : Real.exp (-(x * (p : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr hxp_nonneg
    exact sub_nonneg.mpr hexp_le
  have hint : Integrable (fun p : ℝ≥0 => 1 - Real.exp (-(x * (p : ℝ)))) μ :=
    h_one.sub h_exp
  have h_int :
      ∫ p : ℝ≥0, (1 - Real.exp (-(x * (p : ℝ)))) ∂μ = f δ - f (x + δ) := by
    calc
      ∫ p : ℝ≥0, (1 - Real.exp (-(x * (p : ℝ)))) ∂μ
          = (∫ _p : ℝ≥0, (1 : ℝ) ∂μ) -
              ∫ p : ℝ≥0, Real.exp (-(x * (p : ℝ))) ∂μ := by
            rw [integral_sub h_one h_exp]
      _ = μ.real univ - laplaceTransform μ x := by
            simp [laplaceTransform_apply]
      _ = f δ - f (x + δ) := by
            have h0 := hμ.eq_laplaceTransform (t := 0) le_rfl
            have hxrep := hμ.eq_laplaceTransform (t := x) hx.le
            have h0' : f δ = μ.real univ := by
              simpa [laplaceTransform_zero] using h0
            rw [← h0', ← hxrep]
  rw [← ofReal_integral_eq_lintegral_ofReal hint h_nonneg, h_int]

/-- Markov tail bound: the mass outside the closed ball of radius `R` is controlled by the `∫⁻`
of `p ↦ 1 - exp(-x·p)` divided by its boundary value `1 - exp(-x·R)` (for `x, R > 0`). -/
private lemma measure_closedBall_compl_le_lintegral_div
    {μ : Measure ℝ≥0} [IsFiniteMeasure μ] {x R : ℝ} (hx : 0 < x) (hR : 0 < R) :
    μ (Metric.closedBall (0 : ℝ≥0) R)ᶜ ≤
      (∫⁻ p : ℝ≥0, ENNReal.ofReal (1 - Real.exp (-(x * (p : ℝ)))) ∂μ)
        / ENNReal.ofReal (1 - Real.exp (-(x * R))) := by
  set c : ℝ := 1 - Real.exp (-(x * R)) with hc_def
  have hc_pos : 0 < c := by
    have hxR : 0 < x * R := mul_pos hx hR
    have hexp_lt : Real.exp (-(x * R)) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    rw [hc_def]; linarith
  have hc_ne_zero : ENNReal.ofReal c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hc_pos
  have hc_ne_top : ENNReal.ofReal c ≠ (∞ : ENNReal) := ENNReal.ofReal_ne_top
  have hcoord_meas :
      AEMeasurable (fun p : ℝ≥0 => ENNReal.ofReal (1 - Real.exp (-(x * (p : ℝ))))) μ :=
    (ENNReal.measurable_ofReal.comp
      (by fun_prop : Measurable fun p : ℝ≥0 => 1 - Real.exp (-(x * (p : ℝ)))))
        |>.aemeasurable
  refine (measure_mono ?_).trans (meas_ge_le_lintegral_div hcoord_meas hc_ne_zero hc_ne_top)
  intro p hp
  have hpdist : R < dist p (0 : ℝ≥0) := by
    simpa [Metric.mem_closedBall, not_le] using hp
  have hdist : dist p (0 : ℝ≥0) = (p : ℝ) := by
    simp [NNReal.dist_eq]
  have hRp : R ≤ (p : ℝ) := by linarith
  have hxp : x * R ≤ x * (p : ℝ) := mul_le_mul_of_nonneg_left hRp hx.le
  have hexp_le : Real.exp (-(x * (p : ℝ))) ≤ Real.exp (-(x * R)) :=
    Real.exp_le_exp.mpr (neg_le_neg hxp)
  have hreal : c ≤ 1 - Real.exp (-(x * (p : ℝ))) := by
    rw [hc_def]; linarith
  exact ENNReal.ofReal_le_ofReal hreal

/-- Tail bound for a Laplace-representing measure of a positive shift: the mass outside the
ball of radius `R` is controlled by the Laplace gap `f δ - f (x + δ)`. This is the tightness
input, not a decay rate in `R`: the denominator tends to `1` as `R → ∞`.

The estimate is Markov's inequality on the bounded coordinate `p ↦ 1 - exp (-x * p)`, factored into
`measure_closedBall_compl_le_lintegral_div` (the Markov bound) and
`lintegral_ofReal_one_sub_exp_representsLaplace` (the Laplace-value identity). It is the tightness
input for shifting Bernstein's existence theorem back to the closed-half-line theorem. -/
private lemma shiftedMeasure_closedBall_compl_le
    {f : ℝ → ℝ} {μ : Measure ℝ≥0} [IsFiniteMeasure μ]
    {δ x R : ℝ} (hμ : RepresentsLaplace (fun t : ℝ => f (t + δ)) μ)
    (hx : 0 < x) (hR : 0 < R) :
    μ (Metric.closedBall (0 : ℝ≥0) R)ᶜ ≤
      ENNReal.ofReal ((f δ - f (x + δ)) / (1 - Real.exp (-(x * R)))) := by
  have hc_pos : 0 < 1 - Real.exp (-(x * R)) := by
    have hxR : 0 < x * R := mul_pos hx hR
    have hexp_lt : Real.exp (-(x * R)) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    linarith
  calc
    μ (Metric.closedBall (0 : ℝ≥0) R)ᶜ
        ≤ (∫⁻ p : ℝ≥0, ENNReal.ofReal (1 - Real.exp (-(x * (p : ℝ)))) ∂μ)
            / ENNReal.ofReal (1 - Real.exp (-(x * R))) :=
          measure_closedBall_compl_le_lintegral_div hx hR
    _ = ENNReal.ofReal (f δ - f (x + δ)) / ENNReal.ofReal (1 - Real.exp (-(x * R))) := by
          rw [lintegral_ofReal_one_sub_exp_representsLaplace hμ hx]
    _ = ENNReal.ofReal ((f δ - f (x + δ)) / (1 - Real.exp (-(x * R)))) := by
          rw [ENNReal.ofReal_div_of_pos hc_pos]

/-- The continuity-at-`0` step behind the tightness of the shifted representing measures: for any
`η > 0` there is a positive shift `x` and an index `N` beyond which the Laplace gap-quotient
`(f (aₙ) - f (x + aₙ)) / (1 - e⁻¹)` is at most `η`. Extracted from
`shiftedRepresentingMeasures_tight` so that theorem is the uniform-tail-plus-finite-prefix
compactness assembly. -/
private lemma exists_shift_uniform_gap_bound
    {f : ℝ → ℝ} (hf : IsCompletelyMonotoneOnIci f)
    {a : ℕ → ℝ} (ha_pos : ∀ n, 0 < a n)
    (ha_tendsto_nhds : Tendsto a atTop (nhds 0))
    (ha_tendsto_Ici : Tendsto a atTop (𝓝[Ici (0 : ℝ)] 0))
    {η : ℝ} (hη : 0 < η) :
    ∃ x, 0 < x ∧ ∃ N, ∀ n, N ≤ n →
      (f (a n) - f (x + a n)) / (1 - Real.exp (-1)) ≤ η := by
  have hf_tendsto0 : Tendsto (fun n => f (a n)) atTop (nhds (f 0)) :=
    (hf.continuousOn.continuousWithinAt (mem_Ici.mpr le_rfl)).tendsto.comp ha_tendsto_Ici
  let c0 : ℝ := 1 - Real.exp (-1)
  have hc0_pos : 0 < c0 := by
    have hexp_lt : Real.exp (-1) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    dsimp [c0]
    linarith
  have heta_pos : 0 < η * c0 / 2 := by positivity
  have hnear := (Metric.tendsto_nhds.mp hf_tendsto0) (η * c0 / 2) heta_pos
  obtain ⟨m, hm⟩ := eventually_atTop.1 hnear
  let x : ℝ := a m
  have hx_pos : 0 < x := ha_pos m
  have hx_mem : x ∈ Ici (0 : ℝ) := mem_Ici.mpr hx_pos.le
  have hx_close : dist (f x) (f 0) < η * c0 / 2 := hm m le_rfl
  have hgap_limit_lt : f 0 - f x < η * c0 / 2 := by
    rw [Real.dist_eq] at hx_close
    have hx_abs := abs_lt.mp hx_close
    linarith
  have hx_a_tendsto_nhds : Tendsto (fun n => x + a n) atTop (nhds x) := by
    simpa [add_zero] using tendsto_const_nhds.add ha_tendsto_nhds
  have hx_a_mem : ∀ᶠ n : ℕ in atTop, x + a n ∈ Ici (0 : ℝ) := by
    filter_upwards with n
    exact mem_Ici.mpr (add_nonneg hx_pos.le (ha_pos n).le)
  have hx_a_tendsto_Ici : Tendsto (fun n => x + a n) atTop (𝓝[Ici (0 : ℝ)] x) := by
    rw [nhdsWithin]
    exact tendsto_inf.2 ⟨hx_a_tendsto_nhds, tendsto_principal.mpr hx_a_mem⟩
  have hfx_tendsto : Tendsto (fun n => f (x + a n)) atTop (nhds (f x)) :=
    (hf.continuousOn.continuousWithinAt hx_mem).tendsto.comp hx_a_tendsto_Ici
  have hgap_tendsto :
      Tendsto (fun n => f (a n) - f (x + a n)) atTop (nhds (f 0 - f x)) :=
    hf_tendsto0.sub hfx_tendsto
  have hlim_lt : f 0 - f x < η * c0 := by
    nlinarith [hgap_limit_lt, hη, hc0_pos]
  have hgap_event :
      ∀ᶠ n : ℕ in atTop, (f (a n) - f (x + a n)) / c0 ≤ η := by
    filter_upwards [hgap_tendsto.eventually_lt_const hlim_lt] with n hn
    rw [div_le_iff₀ hc0_pos]
    exact le_of_lt hn
  obtain ⟨N, hN⟩ := eventually_atTop.1 hgap_event
  exact ⟨x, hx_pos, N, hN⟩

/-- The representing measures of positive shifts of a closed-half-line completely monotone
function are uniformly tight as the shifts tend to `0`.

The proof combines the finite initial-segment tightness with a uniform tail estimate for the
remaining shifts (`exists_shift_uniform_gap_bound`) and the Laplace-kernel tail bound
`shiftedMeasure_closedBall_compl_le`. -/
private lemma shiftedRepresentingMeasures_tight
    {f : ℝ → ℝ} (hf : IsCompletelyMonotoneOnIci f)
    {a : ℕ → ℝ} (ha_pos : ∀ n, 0 < a n)
    (ha_tendsto_nhds : Tendsto a atTop (nhds 0))
    (ha_tendsto_Ici : Tendsto a atTop (𝓝[Ici (0 : ℝ)] 0))
    {μ : ℕ → Measure ℝ≥0}
    (hμ : ∀ n, RepresentsLaplace (fun t : ℝ => f (t + a n)) (μ n)) :
    IsTightMeasureSet (Set.range μ) := by
  have hμ_fin : ∀ n, IsFiniteMeasure (μ n) := fun n => (hμ n).isFiniteMeasure
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases hε_top : ε = (∞ : ENNReal)
  · refine ⟨∅, isCompact_empty, ?_⟩
    intro ν _hν
    rw [hε_top]
    exact le_top
  have hε_real_pos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hε_top
  obtain ⟨x, hx_pos, N, hN⟩ :=
    exists_shift_uniform_gap_bound hf ha_pos ha_tendsto_nhds ha_tendsto_Ici hε_real_pos
  let μfin : {n // n < N} → Measure ℝ≥0 := fun n => μ n
  have hfin_tight : IsTightMeasureSet (Set.range μfin) :=
    isTightMeasureSet_range_finite μfin (fun n => hμ_fin n)
  obtain ⟨Kfin, hKfin_comp, hKfin_tail⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hfin_tight ε hε
  let R : ℝ := x⁻¹
  have hR_pos : 0 < R := inv_pos.mpr hx_pos
  refine ⟨Kfin ∪ Metric.closedBall (0 : ℝ≥0) R,
    hKfin_comp.union (isCompact_closedBall _ _), ?_⟩
  intro ν hν
  rcases hν with ⟨n, rfl⟩
  by_cases hnlt : n < N
  · have hmem_fin : μ n ∈ Set.range μfin := ⟨⟨n, hnlt⟩, rfl⟩
    have hsubset : (Kfin ∪ Metric.closedBall (0 : ℝ≥0) R)ᶜ ⊆ Kfinᶜ :=
      compl_subset_compl.mpr (subset_union_left)
    exact (measure_mono hsubset).trans (hKfin_tail (μ n) hmem_fin)
  · have hNn : N ≤ n := le_of_not_gt hnlt
    have hball_subset :
        (Kfin ∪ Metric.closedBall (0 : ℝ≥0) R)ᶜ ⊆
          (Metric.closedBall (0 : ℝ≥0) R)ᶜ :=
      compl_subset_compl.mpr (subset_union_right)
    have htail :=
      shiftedMeasure_closedBall_compl_le (hμ n) hx_pos hR_pos
    have hden : 1 - Real.exp (-(x * R)) = 1 - Real.exp (-1) := by
      dsimp [R]
      rw [mul_inv_cancel₀ hx_pos.ne']
    have hquot :
        ENNReal.ofReal
          ((f (a n) - f (x + a n)) / (1 - Real.exp (-(x * R)))) ≤ ε := by
      rw [hden]
      exact ENNReal.ofReal_le_of_le_toReal (hN n hNn)
    calc
      μ n (Kfin ∪ Metric.closedBall (0 : ℝ≥0) R)ᶜ
          ≤ μ n (Metric.closedBall (0 : ℝ≥0) R)ᶜ := measure_mono hball_subset
      _ ≤ ENNReal.ofReal
            ((f (a n) - f (x + a n)) / (1 - Real.exp (-(x * R)))) := htail
      _ ≤ ε := hquot

/-- Existence of a finite representing measure for the closed-half-line predicate.

Bernstein's existence theorem is applied to the positive shifts `t ↦ f (t + a)`, which satisfy
the stronger Tau Ceti predicate. As `a ↓ 0`, the representing measures are uniformly tight by an
elementary Laplace-kernel tail estimate and hence have a weak cluster point. Continuity at `0`
then identifies that cluster point as a representing measure for the original closed-half-line
function. -/
theorem exists_representsLaplace_of_isCompletelyMonotoneOnIci
    {f : ℝ → ℝ} (hf : IsCompletelyMonotoneOnIci f) :
    ∃ μ : Measure ℝ≥0, RepresentsLaplace f μ := by
  classical
  let a : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ha_pos : ∀ n, 0 < a n := by
    intro n
    dsimp [a]
    positivity
  have ha_tendsto_nhds : Tendsto a atTop (nhds 0) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
      exact Filter.tendsto_atTop_add_const_right atTop 1
        (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [a] using Filter.Tendsto.const_div_atTop hden (1 : ℝ)
  have ha_mem : ∀ᶠ n : ℕ in atTop, a n ∈ Ici (0 : ℝ) := by
    filter_upwards with n
    exact mem_Ici.mpr (ha_pos n).le
  have ha_tendsto_Ici : Tendsto a atTop (𝓝[Ici (0 : ℝ)] 0) := by
    rw [nhdsWithin]
    exact tendsto_inf.2 ⟨ha_tendsto_nhds, tendsto_principal.mpr ha_mem⟩
  have hshift_cm : ∀ n, IsCompletelyMonotone (fun t : ℝ => f (t + a n)) :=
    fun n => hf.shift_pos (ha_pos n)
  choose μ hμ using fun n =>
    exists_representsLaplace_of_isCompletelyMonotone (hshift_cm n)
  have hμ_fin : ∀ n, IsFiniteMeasure (μ n) := fun n => (hμ n).isFiniteMeasure
  let C : ℝ≥0 := ⟨f 0, hf.nonneg_zero⟩
  have hmass : ∀ n, (μ n) univ ≤ (C : ENNReal) := by
    intro n
    have : IsFiniteMeasure (μ n) := hμ_fin n
    have h0 := (hμ n).eq_laplaceTransform (t := 0) le_rfl
    have hreal : (μ n).real univ = f (a n) := by
      simpa [laplaceTransform_zero] using h0.symm
    have hle : (μ n).real univ ≤ f 0 := by
      rw [hreal]
      exact hf.le_apply_zero (ha_pos n).le
    calc
      (μ n) univ = ENNReal.ofReal ((μ n).real univ) := by
        rw [ofReal_measureReal]
      _ ≤ ENNReal.ofReal (f 0) := ENNReal.ofReal_le_ofReal hle
      _ = (C : ENNReal) := by
            have hC : f 0 = (C : ℝ) := rfl
            rw [hC]
            exact ENNReal.ofReal_coe_nnreal
  have htight : IsTightMeasureSet (Set.range μ) :=
    shiftedRepresentingMeasures_tight hf ha_pos ha_tendsto_nhds ha_tendsto_Ici hμ
  obtain ⟨μ₀, U, hUle, hμ₀_fin, _hmass₀, hweak⟩ :=
    finite_measure_cluster_limit (σ := μ) C hmass htight
  refine ⟨μ₀, representsLaplace_iff.mpr ⟨hμ₀_fin, fun t ht => ?_⟩⟩
  have ht_a_tendsto_nhds : Tendsto (fun n => t + a n) atTop (nhds t) := by
    simpa [add_zero] using tendsto_const_nhds.add ha_tendsto_nhds
  have ht_a_mem : ∀ᶠ n : ℕ in atTop, t + a n ∈ Ici (0 : ℝ) := by
    filter_upwards with n
    exact mem_Ici.mpr (add_nonneg ht (ha_pos n).le)
  have ht_a_tendsto_Ici : Tendsto (fun n => t + a n) atTop (𝓝[Ici (0 : ℝ)] t) := by
    rw [nhdsWithin]
    exact tendsto_inf.2 ⟨ht_a_tendsto_nhds, tendsto_principal.mpr ht_a_mem⟩
  have hf_arg_atTop : Tendsto (fun n => f (t + a n)) atTop (nhds (f t)) :=
    (hf.continuousOn.continuousWithinAt (mem_Ici.mpr ht)).tendsto.comp ht_a_tendsto_Ici
  have hf_arg_U : Tendsto (fun n => f (t + a n)) (U : Filter ℕ) (nhds (f t)) :=
    hf_arg_atTop.mono_left hUle
  have hlaplace_U :
      Tendsto (fun n => laplaceTransform (μ n) t) (U : Filter ℕ) (nhds (f t)) := by
    exact Tendsto.congr'
      (Filter.Eventually.of_forall fun n => (hμ n).eq_laplaceTransform (t := t) ht)
      hf_arg_U
  have hshift_laplace :
      Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(μ n)) (U : Filter ℕ)
        (nhds (f t)) := by
    simpa [laplaceTransform_apply] using hlaplace_U
  have hweak_laplace :
      Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(μ n)) (U : Filter ℕ)
        (nhds (laplaceTransform μ₀ t)) := by
    rw [laplaceTransform_apply]
    simpa using hweak (laplaceKernelBoundedContinuous ht)
  exact tendsto_nhds_unique hshift_laplace hweak_laplace

/-! ## Headline theorem -/

/-- **Hausdorff--Bernstein--Widder theorem**, finite-measure version on `ℝ≥0`.

A function is continuous on `[0, ∞)` and completely monotone on `(0, ∞)` if and only if it is
the Laplace transform of a finite positive measure on `ℝ≥0`. -/
theorem hausdorff_bernstein_widder (f : ℝ → ℝ) :
    IsCompletelyMonotoneOnIci f ↔ ∃ μ : Measure ℝ≥0, RepresentsLaplace f μ := by
  constructor
  · exact exists_representsLaplace_of_isCompletelyMonotoneOnIci
  · rintro ⟨μ, hμ⟩
    have := hμ.isFiniteMeasure
    exact (isCompletelyMonotoneOnIci_laplaceTransform μ).congr fun t ht =>
      hμ.eq_laplaceTransform ht

/-- Unique-existence form of the Hausdorff--Bernstein--Widder theorem. -/
theorem hausdorff_bernstein_widder_unique (f : ℝ → ℝ) :
    IsCompletelyMonotoneOnIci f ↔ ∃! μ : Measure ℝ≥0, RepresentsLaplace f μ := by
  rw [hausdorff_bernstein_widder]
  exact ⟨fun ⟨μ, hμ⟩ => ⟨μ, hμ, fun ν hν => laplaceTransform_unique hν hμ⟩,
    fun ⟨μ, hμ, _⟩ => ⟨μ, hμ⟩⟩

end TauCeti
