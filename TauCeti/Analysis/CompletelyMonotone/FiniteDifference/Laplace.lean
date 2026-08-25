/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Laplace.Representation
public import TauCeti.Analysis.CompletelyMonotone.FiniteDifference.Mollify
-- Non-public: Bernstein's theorem supplies the representing measures of the smoothings,
-- Prokhorov extracts their weak cluster point, and Tight handles the finitely many exceptional
-- shifts outside the uniform tail estimate.
import TauCeti.Analysis.CompletelyMonotone.Bernstein.Theorem
import TauCeti.MeasureTheory.Measure.Prokhorov
import TauCeti.MeasureTheory.Measure.Tight

/-!
# The Hausdorff--Bernstein--Widder theorem in finite-difference form

Bernstein's theorem in the form
`TauCeti.exists_representsLaplace_of_isCompletelyMonotone` takes a completely monotone function,
that is a *smooth* one with alternating iterated derivatives, and produces a finite measure on
`ℝ≥0` whose Laplace transform it is. The hypothesis available in applications is the
finite-difference one of `TauCeti.IsDifferenceCompletelyMonotone`, which carries no smoothness:
what one can check about the mass of a family of measures, or about a function built from
positive-definiteness data, is that its mixed forward differences alternate in sign.

This file closes the gap between the two, in both directions.

Feeding the smoothing of
`TauCeti.IsDifferenceCompletelyMonotone.exists_isCompletelyMonotone_between_shift` into Bernstein's
theorem bridges them up to an arbitrarily small shift of the argument: a function on `[0, ∞)`
all of whose mixed forward differences alternate is squeezed, for every `ε > 0`, between
the shift `f (· + ε)` and `f` by the Laplace transform of a finite measure
(`TauCeti.IsDifferenceCompletelyMonotone.exists_isFiniteMeasure_laplaceTransform_between_shift`).

Compactness alone does not remove the shift, because the finite-difference hypothesis says
nothing about the behaviour of `f` at the endpoint: the indicator `f 0 = 1`, `f t = 0` for
`t ≠ 0` has every mixed difference with nonnegative steps of the required sign on `[0, ∞)` —
with all steps positive, the only surviving term of `Δ_{h₁} ⋯ Δ_{hₙ} f` at a point of `[0, ∞)` is
`(-1)ⁿ f 0` at the origin — while no finite positive measure has it as its Laplace transform.
Right-continuity at `0` is enough: it makes the Laplace gaps uniformly small, so Prokhorov gives a
weak cluster point. The squeeze is closed at `0` by the assumed right-continuity and at positive
parameters by continuity of the cluster point's Laplace transform.

For the converse, positive shifts of a continuous completely monotone function satisfy the
finite-difference condition by the smooth equivalence in `FiniteDifference/Basic.lean`; closure
under pointwise limits removes the shift. Applying this to a finite measure's Laplace transform
gives the easy direction.

Together the two directions say that the finite-difference notion plus right-continuity at zero
is *equivalent* to the derivative notion of
`TauCeti.IsContinuousCompletelyMonotoneOnIoi` — no smoothness needs to be assumed, only
concluded. `TauCeti.IsDifferenceCompletelyMonotone.isContinuousCompletelyMonotoneOnIoi` is the
form in which applications use it: `TauCeti.bernsteinMeasureKernel` takes the derivative
predicate as a hypothesis, and the representation API for `TauCeti.bernsteinMeasure` uses it.

## Main declarations

* `TauCeti.IsDifferenceCompletelyMonotone.exists_isFiniteMeasure_laplaceTransform_between_shift`:
  the approximate Laplace representation of a finite-difference completely monotone function.
* `TauCeti.isDifferenceCompletelyMonotone_laplaceTransform` and
  `TauCeti.RepresentsLaplace.isDifferenceCompletelyMonotone`: the easy direction, that a Laplace
  transform of a finite measure has alternating mixed differences.
* `TauCeti.exists_representsLaplace_of_isDifferenceCompletelyMonotone_of_continuousWithinAt`:
  **the representation theorem**, that a function right-continuous at zero with alternating mixed
  differences is the Laplace transform of a finite measure.
* `TauCeti.hausdorff_bernstein_widder_difference`: the resulting characterization of the
  Laplace transforms of finite measures on `ℝ≥0`.
* `TauCeti.hausdorff_bernstein_widder_difference_existsUnique`: its unique-existence form.
* The endpoint-continuity equivalence between the two complete-monotonicity predicates and
  `TauCeti.IsDifferenceCompletelyMonotone.isContinuousCompletelyMonotoneOnIoi`: the two notions
  of complete monotonicity agree under right-continuity at zero.

## References

* D. V. Widder, *The Laplace Transform* (Princeton, 1941), Chapter IV.
* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984).

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem
  milestone) and Part C, Milestone 2 (BCR semigroup--Bochner).
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {f : ℝ → ℝ}

/-! ## Approximate representation from the finite-difference hypothesis -/

/-- **Approximate Bernstein representation.** A function that is completely monotone in the
finite-difference sense is squeezed, for every `ε > 0`, between
`f (· + ε)` and `f` by the Laplace transform of a finite positive measure on `ℝ≥0`.

A Bernstein representation of `f` itself does not follow from these measures by compactness
alone: the hypothesis leaves the value at the endpoint free, so it needs right-continuity of `f`
at `0`, which is what
`TauCeti.exists_representsLaplace_of_isDifferenceCompletelyMonotone_of_continuousWithinAt`
adds. -/
theorem IsDifferenceCompletelyMonotone.exists_isFiniteMeasure_laplaceTransform_between_shift
    (hf : IsDifferenceCompletelyMonotone f) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : Measure ℝ≥0, IsFiniteMeasure μ ∧ ∀ t : ℝ, 0 ≤ t →
      f (t + ε) ≤ laplaceTransform μ t ∧ laplaceTransform μ t ≤ f t := by
  obtain ⟨g, hg, hgle⟩ := hf.exists_isCompletelyMonotone_between_shift hε
  obtain ⟨μ, hμ⟩ := exists_representsLaplace_of_isCompletelyMonotone hg
  refine ⟨μ, hμ.isFiniteMeasure, fun t ht => ?_⟩
  rw [← hμ.eq_laplaceTransform ht]
  exact hgle t ht

/-! ## The easy direction: Laplace transforms have alternating mixed differences -/

/-- A function continuous on `[0, ∞)` and completely monotone on `(0, ∞)` is completely monotone
in the finite-difference sense. Positive shifts are smooth completely monotone functions, and the
finite-difference predicate passes to their pointwise limit. -/
theorem IsContinuousCompletelyMonotoneOnIoi.isDifferenceCompletelyMonotone
    (hf : IsContinuousCompletelyMonotoneOnIoi f) : IsDifferenceCompletelyMonotone f := by
  refine isDifferenceCompletelyMonotone_of_tendsto (L := atTop)
    (F := fun (n : ℕ) t => f (t + 1 / ((n : ℝ) + 1))) (fun n => ?_) ?_
  · have hshift : 0 < 1 / ((n : ℝ) + 1) := by positivity
    exact IsCompletelyMonotone.isDifferenceCompletelyMonotone
      (hf.isCompletelyMonotoneOnIoi.isCompletelyMonotone_comp_add_const hshift)
  · intro u hu
    have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have ha : Tendsto (fun n : ℕ => u + 1 / ((n : ℝ) + 1)) atTop (𝓝[Ici (0 : ℝ)] u) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨by simpa using tendsto_const_nhds.add hzero,
          .of_forall fun n => mem_Ici.mpr (add_nonneg hu (by positivity))⟩
    simpa only [Function.comp_def] using
      (hf.continuousOn.continuousWithinAt (mem_Ici.mpr hu)).tendsto.comp ha

/-- **The Laplace transform of a finite measure is completely monotone in the finite-difference
sense.** Every mixed forward difference with nonnegative steps has the sign `(-1)ⁿ`, because it
is `(-1)ⁿ` times the integral of a nonnegative function. -/
theorem isDifferenceCompletelyMonotone_laplaceTransform (μ : Measure ℝ≥0) [IsFiniteMeasure μ] :
    IsDifferenceCompletelyMonotone (laplaceTransform μ) :=
  (isContinuousCompletelyMonotoneOnIoi_laplaceTransform μ).isDifferenceCompletelyMonotone

/-- A function represented by a finite measure through its Laplace transform is completely
monotone in the finite-difference sense. -/
theorem RepresentsLaplace.isDifferenceCompletelyMonotone {μ : Measure ℝ≥0}
    (h : RepresentsLaplace μ f) : IsDifferenceCompletelyMonotone f :=
  h.isContinuousCompletelyMonotoneOnIoi.isDifferenceCompletelyMonotone

/-! ## Tightness of the approximating measures -/

/-- **The approximating measures of a finite-difference completely monotone function that is
right-continuous at zero are uniformly tight.** The mass a member of the family puts outside a
large ball is bounded, by
`TauCeti.measure_compl_closedBall_le_sub_laplaceTransform_div`, by its Laplace gap
`μ.real univ - laplaceTransform μ x`, and the squeeze bounds that gap by `f 0 - f (x + aₙ)`.
Choosing `x` so small that `f` has barely dropped by `2x` makes the estimate uniform over all
shifts `aₙ ≤ x`; the finitely many larger shifts are handled by
`TauCeti.isTightMeasureSet_range_of_finite`. -/
private lemma isTightMeasureSet_range_of_laplaceTransform_between_shift
    (hf : IsDifferenceCompletelyMonotone f) (hcont : ContinuousWithinAt f (Ici 0) 0)
    {a : ℕ → ℝ} (ha_pos : ∀ n, 0 < a n) (ha : Tendsto a atTop (𝓝 0))
    {μ : ℕ → Measure ℝ≥0} (hfin : ∀ n, IsFiniteMeasure (μ n))
    (hlow : ∀ n, ∀ t : ℝ, 0 ≤ t → f (t + a n) ≤ laplaceTransform (μ n) t)
    (hhigh : ∀ n, ∀ t : ℝ, 0 ≤ t → laplaceTransform (μ n) t ≤ f t) :
    IsTightMeasureSet (range μ) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases hε_top : ε = ∞
  · exact ⟨∅, isCompact_empty, fun ν _ => by simp [hε_top]⟩
  have hε_pos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hε_top
  have hc_pos : 0 < 1 - Real.exp (-1 : ℝ) := by
    have : Real.exp (-1 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  -- A point `y > 0` at which `f` has dropped from `f 0` by less than `ε.toReal * (1 - e⁻¹)`.
  have hcw : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) :=
    hcont.tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hdrop : f 0 - ε.toReal * (1 - Real.exp (-1 : ℝ)) < f 0 := by nlinarith
  obtain ⟨y, hy, hy_pos⟩ :=
    ((hcw.eventually (eventually_gt_nhds hdrop)).and self_mem_nhdsWithin).exists
  -- The Markov parameter is `y / 2` and the radius its inverse, so that their product is `1`.
  have hx_pos : 0 < y / 2 := by linarith
  have hR_pos : 0 < (y / 2)⁻¹ := inv_pos.mpr hx_pos
  have hden : 1 - Real.exp (-(y / 2 * (y / 2)⁻¹)) = 1 - Real.exp (-1 : ℝ) := by
    rw [mul_inv_cancel₀ hx_pos.ne']
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ha.eventually (eventually_lt_nhds hx_pos))
  -- The finitely many shifts larger than `x` are tight on their own.
  obtain ⟨K, hK_compact, hK_tail⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      (isTightMeasureSet_range_of_finite (fun n : {n : ℕ // n < N} => μ n) fun n => hfin n) ε hε
  refine ⟨K ∪ Metric.closedBall (0 : ℝ≥0) (y / 2)⁻¹,
    hK_compact.union (isCompact_closedBall _ _), ?_⟩
  rintro ν ⟨n, rfl⟩
  by_cases hn : n < N
  · exact (measure_mono (compl_subset_compl.mpr subset_union_left)).trans
      (hK_tail (μ n) ⟨⟨n, hn⟩, rfl⟩)
  -- Beyond the threshold the Markov bound applies with a uniform numerator.
  have hnN : N ≤ n := le_of_not_gt hn
  have hfin_n := hfin n
  have hmass : (μ n).real univ ≤ f 0 := by
    simpa [laplaceTransform_zero] using hhigh n 0 le_rfl
  have han : a n < y / 2 := hN n hnN
  have han_pos : 0 < a n := ha_pos n
  have hgap : f y ≤ laplaceTransform (μ n) (y / 2) :=
    le_trans (hf.antitoneOn (mem_Ici.2 (by linarith)) (mem_Ici.2 hy_pos.le) (by linarith))
      (hlow n (y / 2) hx_pos.le)
  have hnum : (μ n).real univ - laplaceTransform (μ n) (y / 2)
      ≤ ε.toReal * (1 - Real.exp (-1 : ℝ)) := by linarith
  calc
    μ n (K ∪ Metric.closedBall (0 : ℝ≥0) (y / 2)⁻¹)ᶜ
        ≤ μ n (Metric.closedBall (0 : ℝ≥0) (y / 2)⁻¹)ᶜ :=
      measure_mono (compl_subset_compl.mpr subset_union_right)
    _ ≤ ENNReal.ofReal (((μ n).real univ - laplaceTransform (μ n) (y / 2))
          / (1 - Real.exp (-(y / 2 * (y / 2)⁻¹)))) :=
      measure_compl_closedBall_le_sub_laplaceTransform_div (μ n) hx_pos hR_pos
    _ ≤ ENNReal.ofReal ε.toReal := by
      rw [hden]
      exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ hc_pos).2 hnum)
    _ ≤ ε := ENNReal.ofReal_le_of_le_toReal le_rfl

/-! ## The representation theorem -/

/-- For a finite measure `μ₀`: if `f u ≤ laplaceTransform μ₀ s` whenever `0 ≤ s < u`, and `f` is
right-continuous at `0`, then `f t ≤ laplaceTransform μ₀ t` for every `0 ≤ t`. -/
private theorem f_le_laplaceTransform_of_forall_lt {μ₀ : Measure ℝ≥0} [IsFiniteMeasure μ₀]
    (hcont : ContinuousWithinAt f (Ici 0) 0)
    (hlower : ∀ s : ℝ, 0 ≤ s → ∀ u : ℝ, s < u → f u ≤ laplaceTransform μ₀ s)
    {t : ℝ} (ht : 0 ≤ t) :
    f t ≤ laplaceTransform μ₀ t := by
  rcases ht.eq_or_lt with rfl | ht
  · -- At the endpoint, right-continuity of `f` passes to the limit from the right.
    have hf_right : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) :=
      hcont.tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    exact le_of_tendsto hf_right
      (eventually_mem_nhdsWithin.mono fun u hu => hlower 0 le_rfl u hu)
  · -- Beyond the endpoint, continuity of the Laplace transform does.
    let _ := right_nhdsWithin_Ico_neBot ht
    have hfilter : 𝓝[Ico 0 t] t ≤ 𝓝 t := inf_le_left
    have hlap : Tendsto (laplaceTransform μ₀) (𝓝[Ico 0 t] t)
        (𝓝 (laplaceTransform μ₀ t)) :=
      ((continuousOn_Ici_laplaceTransform μ₀).continuousAt (Ici_mem_nhds ht)).tendsto.mono_left
        hfilter
    exact ge_of_tendsto hlap
      (eventually_mem_nhdsWithin.mono fun s (hs : s ∈ Ico (0 : ℝ) t) =>
        hlower s hs.1 t hs.2)

/-- **The existence half of the Hausdorff--Bernstein--Widder theorem in finite-difference form.**
A function right-continuous at zero all of whose mixed forward differences with nonnegative steps
have the sign `(-1)ⁿ` is the Laplace transform of a finite positive measure on `ℝ≥0`. -/
theorem exists_representsLaplace_of_isDifferenceCompletelyMonotone_of_continuousWithinAt
    (hf : IsDifferenceCompletelyMonotone f) (hcont : ContinuousWithinAt f (Ici 0) 0) :
    ∃ μ : Measure ℝ≥0, RepresentsLaplace μ f := by
  classical
  -- Stage 1: the positive null sequence of shifts and the approximating measures.
  have ha_pos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have ha : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  choose μ hfin hbetween using fun n : ℕ =>
    hf.exists_isFiniteMeasure_laplaceTransform_between_shift (ha_pos n)
  have hlow : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → f (t + 1 / ((n : ℝ) + 1)) ≤ laplaceTransform (μ n) t :=
    fun n t ht => (hbetween n t ht).1
  have hhigh : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → laplaceTransform (μ n) t ≤ f t :=
    fun n t ht => (hbetween n t ht).2
  -- Stage 2: the uniform mass bound and tightness feed Prokhorov.
  have hmass : ∀ n : ℕ, (μ n) univ ≤ (((f 0).toNNReal : ℝ≥0) : ℝ≥0∞) := by
    intro n
    have := hfin n
    have hle : (μ n).real univ ≤ f 0 := by
      simpa [laplaceTransform_zero] using hhigh n 0 le_rfl
    calc (μ n) univ = ENNReal.ofReal ((μ n).real univ) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (f 0) := ENNReal.ofReal_le_ofReal hle
      _ = (((f 0).toNNReal : ℝ≥0) : ℝ≥0∞) :=
        (ENNReal.ofNNReal_toNNReal (f 0)).symm
  obtain ⟨μ₀, U, hUle, hμ₀_fin, -, hweak⟩ :=
    finite_measure_cluster_limit μ (f 0).toNNReal hmass
      (isTightMeasureSet_range_of_laplaceTransform_between_shift hf hcont ha_pos ha hfin
        hlow hhigh)
  -- Stage 3: the squeeze identifies the Laplace transform of the cluster point as `f`.
  refine ⟨μ₀, representsLaplace_iff.mpr ⟨hμ₀_fin, fun t ht => ?_⟩⟩
  have hL (s : ℝ) (hs : 0 ≤ s) : Tendsto (fun n => laplaceTransform (μ n) s) (U : Filter ℕ)
      (𝓝 (laplaceTransform μ₀ s)) := by
    have hw := hweak (laplaceKernelBoundedContinuous hs)
    simp only [laplaceKernelBoundedContinuous_apply] at hw
    simpa only [laplaceTransform_apply] using hw
  have hupper : laplaceTransform μ₀ t ≤ f t :=
    le_of_tendsto (hL t ht) (.of_forall fun n => hhigh n t ht)
  have hlower (s : ℝ) (hs : 0 ≤ s) (u : ℝ) (hsu : s < u) :
      f u ≤ laplaceTransform μ₀ s := by
    refine ge_of_tendsto (hL s hs) (Eventually.filter_mono hUle ?_)
    filter_upwards [ha.eventually (eventually_lt_nhds (sub_pos.mpr hsu))] with n hn
    refine le_trans (hf.antitoneOn (mem_Ici.2 (by positivity)) (mem_Ici.2 (hs.trans hsu.le))
      (by linarith)) (hlow n s hs)
  let _ := hμ₀_fin
  have hft : f t ≤ laplaceTransform μ₀ t :=
    f_le_laplaceTransform_of_forall_lt hcont hlower ht
  exact le_antisymm hft hupper

/-- **The Hausdorff--Bernstein--Widder theorem in finite-difference form.** A function has
alternating mixed forward differences and is right-continuous at zero if and only if it is the
Laplace transform of a finite positive measure on `ℝ≥0`.

Compare `TauCeti.hausdorff_bernstein_widder`, which states the same representation equivalence
using the derivative-based complete-monotonicity hypothesis. -/
theorem hausdorff_bernstein_widder_difference (f : ℝ → ℝ) :
    (IsDifferenceCompletelyMonotone f ∧ ContinuousWithinAt f (Ici 0) 0)
      ↔ ∃ μ : Measure ℝ≥0, RepresentsLaplace μ f := by
  refine ⟨fun ⟨hf, hcont⟩ =>
      exists_representsLaplace_of_isDifferenceCompletelyMonotone_of_continuousWithinAt hf hcont,
    fun ⟨μ, hμ⟩ =>
      ⟨hμ.isDifferenceCompletelyMonotone,
        hμ.isContinuousCompletelyMonotoneOnIoi.continuousOn.continuousWithinAt
          (mem_Ici.2 le_rfl)⟩⟩

/-- Unique-existence form of the Hausdorff--Bernstein--Widder theorem in finite-difference form. -/
theorem hausdorff_bernstein_widder_difference_existsUnique (f : ℝ → ℝ) :
    (IsDifferenceCompletelyMonotone f ∧ ContinuousWithinAt f (Ici 0) 0)
      ↔ ∃! μ : Measure ℝ≥0, RepresentsLaplace μ f := by
  rw [hausdorff_bernstein_widder_difference]
  exact ⟨fun ⟨μ, hμ⟩ => ⟨μ, hμ, fun ν hν => hν.unique hμ⟩,
    fun ⟨μ, hμ, _⟩ => ⟨μ, hμ⟩⟩

/-- **The two notions of complete monotonicity agree under endpoint continuity.** Complete
monotonicity in the derivative sense on `(0, ∞)`, together with continuity on `[0, ∞)`, is
equivalent to the sign condition on all mixed forward differences plus right-continuity at zero.
Compare `TauCeti.isCompletelyMonotone_iff_isDifferenceCompletelyMonotone`, which assumes
smoothness; here smoothness is a conclusion. -/
theorem
    isContinuousCompletelyMonotoneOnIoi_iff_isDifferenceCompletelyMonotone_and_continuousWithinAt
    (f : ℝ → ℝ) :
    IsContinuousCompletelyMonotoneOnIoi f
      ↔ IsDifferenceCompletelyMonotone f ∧ ContinuousWithinAt f (Ici 0) 0 := by
  refine ⟨fun hf => ⟨hf.isDifferenceCompletelyMonotone,
      hf.continuousOn.continuousWithinAt (mem_Ici.2 le_rfl)⟩, ?_⟩
  rintro ⟨hf, hcont⟩
  obtain ⟨μ, hμ⟩ :=
    exists_representsLaplace_of_isDifferenceCompletelyMonotone_of_continuousWithinAt hf hcont
  exact hμ.isContinuousCompletelyMonotoneOnIoi

/-- **From finite differences to derivatives.** This is the form in which applications use the
equivalence: `TauCeti.bernsteinMeasureKernel` takes
`TauCeti.IsContinuousCompletelyMonotoneOnIoi` as a hypothesis, and the representation lemmas
`TauCeti.representsLaplace_bernsteinMeasure` and `TauCeti.laplaceTransform_bernsteinMeasure` use
it for `TauCeti.bernsteinMeasure`, while what is checkable in practice is the finite-difference
condition. -/
theorem IsDifferenceCompletelyMonotone.isContinuousCompletelyMonotoneOnIoi
    (hf : IsDifferenceCompletelyMonotone f) (hcont : ContinuousWithinAt f (Ici 0) 0) :
    IsContinuousCompletelyMonotoneOnIoi f := by
  obtain ⟨μ, hμ⟩ :=
    exists_representsLaplace_of_isDifferenceCompletelyMonotone_of_continuousWithinAt hf hcont
  exact hμ.isContinuousCompletelyMonotoneOnIoi

end TauCeti

end
