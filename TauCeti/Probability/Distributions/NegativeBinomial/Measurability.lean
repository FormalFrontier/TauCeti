/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.NegativeBinomial.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# Parameter measurability of the negative-binomial distribution

This file proves that the negative-binomial law is a measurable function of its real shape and
success-probability parameters. Consequently, a measurable pair of parameters can be used to form
a probability kernel with negative-binomial fibres whenever the parameters lie in the classical
range.

## Main result

* `TauCeti.Probability.measurable_negativeBinomialMeasure` — joint parameter measurability of the
  totalized negative-binomial family.
-/

public section

noncomputable section

open MeasureTheory Real

open scoped ENNReal

namespace TauCeti

namespace Probability

/-- The negative-binomial family is jointly measurable in its shape and success probability.

This includes the shape-zero Dirac law and every invalid parameter value, where the totalized
family is the zero measure. -/
@[fun_prop]
theorem measurable_negativeBinomialMeasure :
    Measurable fun q : ℝ × ℝ => negativeBinomialMeasure q.1 q.2 := by
  let weight : ℝ × ℝ → ℕ → ℝ≥0∞ := fun q k =>
    ENNReal.ofReal (Real.Gamma (k + q.1) / (k.factorial * Real.Gamma q.1) *
      Real.rpow q.2 q.1 * (1 - q.2) ^ k)
  have hweight (k : ℕ) : Measurable fun q => weight q k := by
    apply Measurable.ennreal_ofReal
    have hcoeff : Measurable fun q : ℝ × ℝ =>
        Real.Gamma (k + q.1) / (k.factorial * Real.Gamma q.1) :=
      (Real.measurable_Gamma.comp (by fun_prop)).div
        (measurable_const.mul (Real.measurable_Gamma.comp measurable_fst))
    exact (hcoeff.mul (measurable_snd.pow measurable_fst)).mul
        ((measurable_const.sub measurable_snd).pow_const k)
  let sumMeasure : ℝ × ℝ → Measure ℕ := fun q =>
    Measure.sum fun k => weight q k • Measure.dirac k
  have hsum : Measurable sumMeasure :=
    TauCeti.MeasureTheory.measurable_sum_smul_dirac hweight
  have hvalid : MeasurableSet {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.2 ≤ 1} := by
    exact (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const))
  have hzero : MeasurableSet {q : ℝ × ℝ | q.1 = 0 ∧ 0 < q.2 ∧ q.2 ≤ 1} := by
    have hrzero : MeasurableSet {q : ℝ × ℝ | q.1 = 0} :=
      measurableSet_eq_fun measurable_fst measurable_const
    exact hrzero.inter ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const))
  have hmodel : (fun q : ℝ × ℝ => negativeBinomialMeasure q.1 q.2) = fun q =>
      if 0 < q.1 ∧ 0 < q.2 ∧ q.2 ≤ 1 then sumMeasure q
      else if q.1 = 0 ∧ 0 < q.2 ∧ q.2 ≤ 1 then Measure.dirac 0 else 0 := by
    funext q
    split_ifs with hpos hshape
    · rw [negativeBinomialMeasure_eq_sum_dirac hpos.1.le hpos.2.1 hpos.2.2]
      simp only [sumMeasure]
      apply congrArg Measure.sum
      funext k
      apply congrArg (fun c => c • Measure.dirac k)
      have htop : negativeBinomialWeight q.1 q.2 k ≠ ∞ := by
        let _ := isProbabilityMeasure_negativeBinomialMeasure
          hpos.1.le hpos.2.1 hpos.2.2
        rw [← negativeBinomialMeasure_singleton hpos.1.le hpos.2.1 hpos.2.2 k]
        exact measure_ne_top _ _
      rw [← ENNReal.ofReal_toReal htop,
        negativeBinomialWeight_toReal hpos.1.le hpos.2.1.le hpos.2.2,
        negativeBinomialWeightReal_eq_gamma hpos.1.ne' k]
    · rw [hshape.1]
      exact negativeBinomialMeasure_zero hshape.2.1 hshape.2.2
    · apply negativeBinomialMeasure_eq_zero_of_invalid
      rintro ⟨hr, hp, hp1⟩
      rcases hr.eq_or_lt with hr | hr
      · exact hshape ⟨hr.symm, hp, hp1⟩
      · exact hpos ⟨hr, hp, hp1⟩
  rw [hmodel]
  exact Measurable.ite hvalid hsum
    (Measurable.ite hzero measurable_const measurable_const)

end Probability

end TauCeti
