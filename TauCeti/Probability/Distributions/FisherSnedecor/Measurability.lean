/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.FisherSnedecor.Basic
import all TauCeti.Probability.Distributions.FisherSnedecor.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma

/-!
# Parameter measurability of Fisher's F distribution

This file proves that the Fisher--Snedecor law is a measurable function of its two degrees of
freedom. Consequently, measurable numerator and denominator parameters can be used to form a
probability kernel whenever they lie in the positive range.

Joint measurability of the density is exposed alongside the measure-level result, so both the law
and its density can be composed with measurable parameter maps.

## Main results

* `measurable_uncurry_fisherSnedecorPDF` — joint measurability of the density.
* `measurable_fisherSnedecorMeasure` — joint parameter measurability of the family of measures.
-/

public section

noncomputable section

open MeasureTheory Real

namespace TauCeti

namespace Probability

/-- The Fisher--Snedecor density is jointly measurable in the numerator and denominator degrees
of freedom and the sample point. -/
@[fun_prop]
theorem measurable_uncurry_fisherSnedecorPDF :
    Measurable fun q : (ℝ × ℝ) × ℝ => fisherSnedecorPDF q.1.1 q.1.2 q.2 := by
  unfold fisherSnedecorPDF fisherSnedecorPDFReal
  refine (Measurable.ite ?_ (by fun_prop) measurable_const).ennreal_ofReal
  have hzero : Measurable fun _ : (ℝ × ℝ) × ℝ => (0 : ℝ) := measurable_const
  exact (measurableSet_lt hzero measurable_fst.fst).inter
    ((measurableSet_lt hzero measurable_fst.snd).inter
      (measurableSet_lt hzero measurable_snd))

/-- The Fisher--Snedecor family is jointly measurable in its two degrees of freedom.

This theorem includes every invalid parameter pair, where `fisherSnedecorMeasure` is the zero
measure. -/
@[fun_prop]
theorem measurable_fisherSnedecorMeasure :
    Measurable fun p : ℝ × ℝ => fisherSnedecorMeasure p.1 p.2 := by
  simpa only [fisherSnedecorMeasure_eq_withDensity] using
    measurable_withDensity (μ := volume) measurable_uncurry_fisherSnedecorPDF

end Probability

end TauCeti
