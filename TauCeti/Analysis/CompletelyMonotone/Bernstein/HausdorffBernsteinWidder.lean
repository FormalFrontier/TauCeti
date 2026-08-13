/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Laplace.Representation
-- Non-public: the metrizability class of the finite-set tightness lemmas.
import Mathlib.Topology.Metrizable.CompletelyMetrizable
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
uniqueness both live in `Laplace/Representation.lean`.

## Main declarations

* `TauCeti.exists_representsLaplace_of_isContinuousCompletelyMonotoneOnIoi`
* `TauCeti.hausdorff_bernstein_widder`, `TauCeti.hausdorff_bernstein_widder_existsUnique`

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

/-- A finite set of finite measures is tight: singletons are tight and tightness is closed
under unions. (The empty case routes through an arbitrary singleton, as Mathlib has no
dedicated empty-set tightness lemma.) -/
private lemma isTightMeasureSet_of_finite {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [TopologicalSpace.IsCompletelyPseudoMetrizableSpace α] [SecondCountableTopology α]
    [BorelSpace α] {S : Set (Measure α)} (hS : S.Finite)
    (hfin : ∀ ν ∈ S, IsFiniteMeasure ν) : IsTightMeasureSet S := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact (isTightMeasureSet_singleton (μ := (0 : Measure α))).subset (empty_subset _)
  | @insert ν S _ _ ih =>
      have : IsFiniteMeasure ν := hfin ν (mem_insert _ _)
      rw [insert_eq]
      exact isTightMeasureSet_singleton.union (ih fun ρ hρ => hfin ρ (mem_insert_of_mem _ hρ))

/-- A finite family of finite measures is tight. -/
private lemma isTightMeasureSet_range_finite
    {α ι : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [TopologicalSpace.IsCompletelyPseudoMetrizableSpace α] [SecondCountableTopology α]
    [BorelSpace α] [Finite ι] (μ : ι → Measure α)
    (hfin : ∀ i, IsFiniteMeasure (μ i)) :
    IsTightMeasureSet (Set.range μ) :=
  isTightMeasureSet_of_finite (finite_range μ) (by rintro ν ⟨i, rfl⟩; exact hfin i)

/-- Along a positive null sequence `aₙ ↓ 0`, the values `f (c + aₙ)` of a function continuous
within `[0, ∞)` converge to `f c`, for any `c ≥ 0`. -/
private lemma tendsto_apply_add_of_continuousOn
    {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0)) {c : ℝ} (hc : 0 ≤ c)
    {a : ℕ → ℝ} (ha_pos : ∀ n, 0 < a n) (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => f (c + a n)) atTop (𝓝 (f c)) := by
  have hmem : Tendsto (fun n => c + a n) atTop (𝓝[Ici (0 : ℝ)] c) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨by simpa using tendsto_const_nhds.add ha,
        .of_forall fun n => mem_Ici.mpr (add_nonneg hc (ha_pos n).le)⟩
  exact (hf.continuousWithinAt (mem_Ici.mpr hc)).tendsto.comp hmem

/-- The Markov denominator `1 - e^{-xR}` is positive for `x, R > 0`. -/
private lemma one_sub_exp_neg_mul_pos {x R : ℝ} (hx : 0 < x) (hR : 0 < R) :
    0 < 1 - Real.exp (-(x * R)) := by
  have : Real.exp (-(x * R)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  linarith

/-- The `∫⁻` of the bounded coordinate `p ↦ 1 - exp(-x·p)` against a measure that represents
`t ↦ f (t + δ)` by its Laplace transform equals `f δ - f (x + δ)` (for `x > 0`). This is the
Laplace-value identity behind the shifted-measure tail estimate. -/
private lemma lintegral_ofReal_one_sub_exp_eq_of_representsLaplace
    {f : ℝ → ℝ} {μ : Measure ℝ≥0}
    {δ x : ℝ} (hμ : RepresentsLaplace μ (fun t : ℝ => f (t + δ))) (hx : 0 < x) :
    ∫⁻ p : ℝ≥0, ENNReal.ofReal (1 - Real.exp (-(x * (p : ℝ)))) ∂μ
      = ENNReal.ofReal (f δ - f (x + δ)) := by
  have := hμ.isFiniteMeasure
  have h_one : Integrable (fun _ : ℝ≥0 => (1 : ℝ)) μ := integrable_const 1
  have h_exp : Integrable (fun p : ℝ≥0 => Real.exp (-(x * (p : ℝ)))) μ :=
    integrable_exp_neg_mul μ hx.le
  have h_nonneg : 0 ≤ᵐ[μ] fun p : ℝ≥0 => 1 - Real.exp (-(x * (p : ℝ))) := by
    refine Filter.Eventually.of_forall fun p => ?_
    exact sub_nonneg.mpr (exp_neg_mul_le_one hx.le p)
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
    {μ : Measure ℝ≥0} {x R : ℝ} (hx : 0 < x) (hR : 0 < R) :
    μ (Metric.closedBall (0 : ℝ≥0) R)ᶜ ≤
      (∫⁻ p : ℝ≥0, ENNReal.ofReal (1 - Real.exp (-(x * (p : ℝ)))) ∂μ)
        / ENNReal.ofReal (1 - Real.exp (-(x * R))) := by
  set c : ℝ := 1 - Real.exp (-(x * R)) with hc_def
  have hc_pos : 0 < c := one_sub_exp_neg_mul_pos hx hR
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
`lintegral_ofReal_one_sub_exp_eq_of_representsLaplace` (the Laplace-value identity). It is the
tightness input for shifting Bernstein's existence theorem back to the closed-half-line
theorem. -/
private lemma measure_closedBall_compl_le_of_representsLaplace_shift
    {f : ℝ → ℝ} {μ : Measure ℝ≥0}
    {δ x R : ℝ} (hμ : RepresentsLaplace μ (fun t : ℝ => f (t + δ)))
    (hx : 0 < x) (hR : 0 < R) :
    μ (Metric.closedBall (0 : ℝ≥0) R)ᶜ ≤
      ENNReal.ofReal ((f δ - f (x + δ)) / (1 - Real.exp (-(x * R)))) := by
  have hc_pos : 0 < 1 - Real.exp (-(x * R)) := one_sub_exp_neg_mul_pos hx hR
  calc
    μ (Metric.closedBall (0 : ℝ≥0) R)ᶜ
        ≤ (∫⁻ p : ℝ≥0, ENNReal.ofReal (1 - Real.exp (-(x * (p : ℝ)))) ∂μ)
            / ENNReal.ofReal (1 - Real.exp (-(x * R))) :=
          measure_closedBall_compl_le_lintegral_div hx hR
    _ = ENNReal.ofReal (f δ - f (x + δ)) / ENNReal.ofReal (1 - Real.exp (-(x * R))) := by
          rw [lintegral_ofReal_one_sub_exp_eq_of_representsLaplace hμ hx]
    _ = ENNReal.ofReal ((f δ - f (x + δ)) / (1 - Real.exp (-(x * R)))) := by
          rw [ENNReal.ofReal_div_of_pos hc_pos]

/-- The continuity-at-`0` step behind the tightness of the shifted representing measures: for any
`η > 0` there is a positive shift `x` and an index `N` beyond which the Laplace gap-quotient
`(f (aₙ) - f (x + aₙ)) / (1 - e⁻¹)` is at most `η`: the uniform-tail input to the tightness
of the shifted representing measures. The denominator `1 - e⁻¹` is the Markov constant
`1 - exp (-(x * R))` of `measure_closedBall_compl_le_of_representsLaplace_shift` at the radius
`R = x⁻¹` that the tightness proof chooses, so that `x * R = 1`. -/
private lemma exists_shift_uniform_gap_bound
    {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0))
    {a : ℕ → ℝ} (ha_pos : ∀ n, 0 < a n)
    (ha : Tendsto a atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    ∃ x, 0 < x ∧ ∃ N, ∀ n, N ≤ n →
      (f (a n) - f (x + a n)) / (1 - Real.exp (-1)) ≤ η := by
  have hf_tendsto0 : Tendsto (fun n => f (a n)) atTop (𝓝 (f 0)) := by
    simpa using tendsto_apply_add_of_continuousOn hf le_rfl ha_pos ha
  let c0 : ℝ := 1 - Real.exp (-1)
  have hc0_pos : 0 < c0 := by
    have hexp_lt : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    dsimp [c0]
    linarith
  have hetac : 0 < η * c0 := mul_pos hη hc0_pos
  obtain ⟨m, hm⟩ :=
    (hf_tendsto0.eventually (eventually_gt_nhds (by linarith : f 0 - η * c0 < f 0))).exists
  let x : ℝ := a m
  have hx_pos : 0 < x := ha_pos m
  have hlim_lt : f 0 - f x < η * c0 := by
    simpa [x, sub_lt_comm] using hm
  have hfx_tendsto : Tendsto (fun n => f (x + a n)) atTop (𝓝 (f x)) :=
    tendsto_apply_add_of_continuousOn hf hx_pos.le ha_pos ha
  have hgap_tendsto :
      Tendsto (fun n => f (a n) - f (x + a n)) atTop (𝓝 (f 0 - f x)) :=
    hf_tendsto0.sub hfx_tendsto
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
`measure_closedBall_compl_le_of_representsLaplace_shift`. -/
private lemma isTightMeasureSet_range_of_representsLaplace_shift
    {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0))
    {a : ℕ → ℝ} (ha_pos : ∀ n, 0 < a n)
    (ha : Tendsto a atTop (𝓝 0))
    {μ : ℕ → Measure ℝ≥0}
    (hμ : ∀ n, RepresentsLaplace (μ n) (fun t : ℝ => f (t + a n))) :
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
    exists_shift_uniform_gap_bound hf ha_pos ha hε_real_pos
  let μfin : {n // n < N} → Measure ℝ≥0 := fun n => μ n
  have hfin_tight : IsTightMeasureSet (Set.range μfin) :=
    isTightMeasureSet_range_finite μfin (fun n => hμ_fin n)
  obtain ⟨Kfin, hKfin_comp, hKfin_tail⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hfin_tight ε hε
  -- The radius is tied to the shift so that `x * R = 1`, matching the `1 - e⁻¹` denominator
  -- in the gap bound above.
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
      measure_closedBall_compl_le_of_representsLaplace_shift (hμ n) hx_pos hR_pos
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

/-- The representing measure of the positive shift `t ↦ f (t + δ)` has total mass
`f δ ≤ f 0`. -/
private lemma measure_univ_le_of_representsLaplace_shift
    {f : ℝ → ℝ} (hf : IsContinuousCompletelyMonotoneOnIoi f) {δ : ℝ} (hδ : 0 ≤ δ)
    {μ : Measure ℝ≥0} (hμ : RepresentsLaplace μ (fun t : ℝ => f (t + δ))) :
    μ univ ≤ ENNReal.ofReal (f 0) := by
  have := hμ.isFiniteMeasure
  have hreal : μ.real univ = f δ := by
    simpa [laplaceTransform_zero] using (hμ.eq_laplaceTransform (t := 0) le_rfl).symm
  calc
    μ univ = ENNReal.ofReal (μ.real univ) := by rw [ofReal_measureReal]
    _ ≤ ENNReal.ofReal (f 0) :=
        ENNReal.ofReal_le_ofReal (hreal ▸ hf.le_apply_zero hδ)

/-- **Existence half of the Hausdorff--Bernstein--Widder theorem**: a function continuous on
`[0, ∞)` and completely monotone on `(0, ∞)` is the Laplace transform of a finite positive
measure on `ℝ≥0`. -/
theorem exists_representsLaplace_of_isContinuousCompletelyMonotoneOnIoi
    {f : ℝ → ℝ} (hf : IsContinuousCompletelyMonotoneOnIoi f) :
    ∃ μ : Measure ℝ≥0, RepresentsLaplace μ f := by
  classical
  -- Stage 1: the positive null sequence of shifts `aₙ = 1/(n+1)`.
  let a : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ha_pos : ∀ n, 0 < a n := by
    intro n
    dsimp [a]
    positivity
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa [a] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  -- Stage 2: representing measures for the shifted functions, from Bernstein's theorem.
  have hshift_cm : ∀ n, IsCompletelyMonotone (fun t : ℝ => f (t + a n)) :=
    fun n => hf.isCompletelyMonotoneOnIoi.isCompletelyMonotone_comp_add_const (ha_pos n)
  choose μ hμ using fun n =>
    exists_representsLaplace_of_isCompletelyMonotone (hshift_cm n)
  -- Stage 3: a uniform mass bound and tightness give a weak cluster point.
  let C : ℝ≥0 := ⟨f 0, hf.nonneg_zero⟩
  have hmass : ∀ n, (μ n) univ ≤ (C : ENNReal) := fun n =>
    calc
      (μ n) univ ≤ ENNReal.ofReal (f 0) :=
        measure_univ_le_of_representsLaplace_shift hf (ha_pos n).le (hμ n)
      _ = (C : ENNReal) := ENNReal.ofReal_eq_coe_nnreal hf.nonneg_zero
  have htight : IsTightMeasureSet (Set.range μ) :=
    isTightMeasureSet_range_of_representsLaplace_shift hf.continuousOn ha_pos ha hμ
  obtain ⟨μ₀, U, hUle, hμ₀_fin, _hmass₀, hweak⟩ :=
    finite_measure_cluster_limit (σ := μ) C hmass htight
  -- Stage 4: identify the cluster point as a representing measure via continuity at `0⁺`.
  refine ⟨μ₀, representsLaplace_iff.mpr ⟨hμ₀_fin, fun t ht => ?_⟩⟩
  have hf_arg_U : Tendsto (fun n => f (t + a n)) (U : Filter ℕ) (𝓝 (f t)) :=
    (tendsto_apply_add_of_continuousOn hf.continuousOn ht ha_pos ha).mono_left hUle
  have hshift_laplace :
      Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(μ n)) (U : Filter ℕ)
        (𝓝 (f t)) := by
    refine Tendsto.congr (fun n => ?_) hf_arg_U
    rw [(hμ n).eq_laplaceTransform (t := t) ht, laplaceTransform_apply]
  have hweak_laplace :
      Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(μ n)) (U : Filter ℕ)
        (𝓝 (laplaceTransform μ₀ t)) := by
    rw [laplaceTransform_apply]
    simpa using hweak (laplaceKernelBoundedContinuous ht)
  exact tendsto_nhds_unique hshift_laplace hweak_laplace

/-! ## Headline theorem -/

/-- **Hausdorff--Bernstein--Widder theorem**, finite-measure version on `ℝ≥0`.

A function is continuous on `[0, ∞)` and completely monotone on `(0, ∞)` if and only if it is
the Laplace transform of a finite positive measure on `ℝ≥0`. -/
theorem hausdorff_bernstein_widder (f : ℝ → ℝ) :
    IsContinuousCompletelyMonotoneOnIoi f ↔ ∃ μ : Measure ℝ≥0, RepresentsLaplace μ f := by
  constructor
  · exact exists_representsLaplace_of_isContinuousCompletelyMonotoneOnIoi
  · rintro ⟨μ, hμ⟩
    exact hμ.isContinuousCompletelyMonotoneOnIoi

/-- Unique-existence form of the Hausdorff--Bernstein--Widder theorem. -/
theorem hausdorff_bernstein_widder_existsUnique (f : ℝ → ℝ) :
    IsContinuousCompletelyMonotoneOnIoi f ↔ ∃! μ : Measure ℝ≥0, RepresentsLaplace μ f := by
  rw [hausdorff_bernstein_widder]
  exact ⟨fun ⟨μ, hμ⟩ => ⟨μ, hμ, fun ν hν => hν.unique hμ⟩,
    fun ⟨μ, hμ, _⟩ => ⟨μ, hμ⟩⟩

end TauCeti
