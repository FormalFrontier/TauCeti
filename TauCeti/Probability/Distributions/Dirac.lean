/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# Distributional formulas for Dirac measures

This file records the cumulative distribution function of a real Dirac measure, and the
exponential-integrability domain and cumulant-generating function of a real-valued statistic under
a Dirac measure. The moment-generating function is already available in Mathlib as
`ProbabilityTheory.mgf_dirac'`.

## Main results

* `TauCeti.cdf_dirac` — the cdf of a real Dirac measure;
* `TauCeti.integrableExpSet_dirac` — every exponential moment exists under a Dirac measure;
* `TauCeti.cgf_dirac'` — the cumulant-generating function under a Dirac measure.
-/

public section

namespace TauCeti

open MeasureTheory ProbabilityTheory Set

/-- The cumulative distribution function of a Dirac measure is a step function. -/
@[simp]
theorem cdf_dirac (a x : ℝ) : cdf (Measure.dirac a) x = if a ≤ x then 1 else 0 := by
  rw [cdf_eq_real, measureReal_def]
  by_cases h : a ≤ x <;> simp [Measure.dirac_apply' _ measurableSet_Iic, h]

/-- Every exponential moment of a Dirac measure exists. -/
@[simp]
theorem integrableExpSet_dirac {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (X : Ω → ℝ) (ω : Ω) :
    integrableExpSet X (Measure.dirac ω) = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact integrable_dirac (by simp)

/-- The cumulant-generating function of a Dirac measure is linear. -/
@[simp]
theorem cgf_dirac' {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (X : Ω → ℝ) (ω : Ω) (t : ℝ) :
    cgf X (Measure.dirac ω) t = t * X ω := by
  rw [cgf, mgf_dirac', Real.log_exp]

end TauCeti
