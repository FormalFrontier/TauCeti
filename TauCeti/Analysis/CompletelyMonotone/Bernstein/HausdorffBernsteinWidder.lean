/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Laplace.Representation
-- Non-public: Bernstein's existence theorem supplies the representing measures of the shifts.
import TauCeti.Analysis.CompletelyMonotone.Bernstein.Theorem
-- Non-public: `finite_measure_cluster_limit` extracts the weak cluster point.
import TauCeti.MeasureTheory.Measure.Prokhorov
-- Non-public: tightness of the finitely many shifts that the uniform tail bound misses.
import TauCeti.MeasureTheory.Measure.Tight

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
* `TauCeti.bernsteinMeasure`: the canonical representing measure, with its uniqueness,
  total-mass, and algebraic API.

## References

The finite-measure representation is the Hausdorff--Bernstein--Widder theorem, after
S. Bernstein (1928) and D. V. Widder, *The Laplace Transform*, Chapter IV.

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem
  milestone).
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BoundedContinuousFunction ContDiff ENNReal NNReal Topology

namespace TauCeti

/-! ## Hard direction: tightness of the shifted representing measures -/

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

/-- Tail bound for a Laplace-representing measure of a positive shift: the mass outside the
ball of radius `R` is controlled by the Laplace gap `f δ - f (x + δ)`. This is the tightness
input, not a decay rate in `R`: the denominator tends to `1` as `R → ∞`.

It is `TauCeti.measure_compl_closedBall_le_of_laplaceTransform` read through the representation,
which turns the total mass into `f δ` and the Laplace transform at `x` into `f (x + δ)`. -/
private lemma measure_closedBall_compl_le_of_representsLaplace_shift
    {f : ℝ → ℝ} {μ : Measure ℝ≥0}
    {δ x R : ℝ} (hμ : RepresentsLaplace μ (fun t : ℝ => f (t + δ)))
    (hx : 0 < x) (hR : 0 < R) :
    μ (Metric.closedBall (0 : ℝ≥0) R)ᶜ ≤
      ENNReal.ofReal ((f δ - f (x + δ)) / (1 - Real.exp (-(x * R)))) := by
  have := hμ.isFiniteMeasure
  have hmass : μ.real univ = f δ := by
    simpa [laplaceTransform_zero] using (hμ.eq_laplaceTransform (t := 0) le_rfl).symm
  have hlap : laplaceTransform μ x = f (x + δ) := (hμ.eq_laplaceTransform hx.le).symm
  rw [← hmass, ← hlap]
  exact measure_compl_closedBall_le_of_laplaceTransform μ hx hR

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

/-! ## The canonical representing measure -/

variable {f : ℝ → ℝ}

open Classical in
/-- **The Bernstein representing measure** of `f`: the unique finite measure on `ℝ≥0` whose
Laplace transform is `f` on `[0, ∞)`, when `f` has one, and the zero measure otherwise.

By `TauCeti.hausdorff_bernstein_widder` a representing measure exists exactly when `f` is
continuous on `[0, ∞)` and completely monotone on `(0, ∞)`. -/
noncomputable def bernsteinMeasure (f : ℝ → ℝ) : Measure ℝ≥0 :=
  if h : ∃ μ : Measure ℝ≥0, RepresentsLaplace μ f then h.choose else 0

/-- Outside the hypotheses of the Hausdorff--Bernstein--Widder theorem the Bernstein measure is
`0`. -/
theorem bernsteinMeasure_eq_zero_of_not (h : ¬ ∃ μ : Measure ℝ≥0, RepresentsLaplace μ f) :
    bernsteinMeasure f = 0 := by
  classical
  rw [bernsteinMeasure, dite_eq_right h]

/-- **The Bernstein measure represents its function.** -/
theorem representsLaplace_bernsteinMeasure (hf : IsContinuousCompletelyMonotoneOnIoi f) :
    RepresentsLaplace (bernsteinMeasure f) f := by
  classical
  have h : ∃ μ : Measure ℝ≥0, RepresentsLaplace μ f := (hausdorff_bernstein_widder f).mp hf
  rw [bernsteinMeasure, dite_eq_left h]
  exact h.choose_spec

/-- The Bernstein measure of any function is finite: for a represented function this is the
finiteness of its representing measure, and otherwise the measure is `0`. -/
instance isFiniteMeasure_bernsteinMeasure (f : ℝ → ℝ) : IsFiniteMeasure (bernsteinMeasure f) := by
  classical
  rw [bernsteinMeasure]
  split
  · rename_i h
    exact h.choose_spec.isFiniteMeasure
  · infer_instance

/-- **Uniqueness of the Bernstein measure.** Any finite measure representing `f` by its Laplace
transform is the Bernstein measure of `f`. No hypothesis on `f` is needed: a represented function
is automatically continuous and completely monotone. -/
theorem eq_bernsteinMeasure (μ : Measure ℝ≥0) (hμ : RepresentsLaplace μ f) :
    μ = bernsteinMeasure f :=
  hμ.unique (representsLaplace_bernsteinMeasure hμ.isContinuousCompletelyMonotoneOnIoi)

/-- The Laplace transform of the Bernstein measure recovers the function on `[0, ∞)`. -/
@[grind =>]
theorem laplaceTransform_bernsteinMeasure (hf : IsContinuousCompletelyMonotoneOnIoi f) {t : ℝ}
    (ht : 0 ≤ t) : laplaceTransform (bernsteinMeasure f) t = f t :=
  ((representsLaplace_bernsteinMeasure hf).eq_laplaceTransform ht).symm

/-- The total mass of the Bernstein measure is the value of the function at `0`. -/
@[simp]
theorem bernsteinMeasure_real_univ (hf : IsContinuousCompletelyMonotoneOnIoi f) :
    (bernsteinMeasure f).real univ = f 0 :=
  ((representsLaplace_bernsteinMeasure hf).apply_zero).symm

/-- The total mass of the Bernstein measure, as an extended nonnegative real. -/
@[simp]
theorem bernsteinMeasure_univ (hf : IsContinuousCompletelyMonotoneOnIoi f) :
    bernsteinMeasure f univ = ENNReal.ofReal (f 0) := by
  rw [← bernsteinMeasure_real_univ hf, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- A function with total mass `1` has a probability measure for its Bernstein measure. -/
theorem isProbabilityMeasure_bernsteinMeasure (hf : IsContinuousCompletelyMonotoneOnIoi f)
    (hf0 : f 0 = 1) : IsProbabilityMeasure (bernsteinMeasure f) :=
  isProbabilityMeasure_iff_real.mpr <| by rw [bernsteinMeasure_real_univ hf, hf0]

/-- The Bernstein measure of the zero function is the zero measure. -/
@[simp]
theorem bernsteinMeasure_zero : bernsteinMeasure (fun _ : ℝ => (0 : ℝ)) = 0 :=
  (eq_bernsteinMeasure 0 representsLaplace_zero).symm

/-- The Bernstein measure turns sums of functions into sums of measures. -/
theorem bernsteinMeasure_add {g : ℝ → ℝ} (hf : IsContinuousCompletelyMonotoneOnIoi f)
    (hg : IsContinuousCompletelyMonotoneOnIoi g) :
    bernsteinMeasure (f + g) = bernsteinMeasure f + bernsteinMeasure g :=
  (eq_bernsteinMeasure _ ((representsLaplace_bernsteinMeasure hf).add
    (representsLaplace_bernsteinMeasure hg))).symm

/-- The Bernstein measure turns nonnegative scalar multiples of functions into scalar multiples of
measures. -/
theorem bernsteinMeasure_const_mul (hf : IsContinuousCompletelyMonotoneOnIoi f) (c : ℝ≥0) :
    bernsteinMeasure (fun t => (c : ℝ) * f t) = (c : ℝ≥0∞) • bernsteinMeasure f :=
  (eq_bernsteinMeasure _ ((representsLaplace_bernsteinMeasure hf).smul c)).symm

end TauCeti
