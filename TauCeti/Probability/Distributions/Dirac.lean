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

This file records formulas for cumulative and exponential generating functions of Dirac measures.
They provide the common boundary-case API for distribution families that degenerate to a point mass.
-/

public section

namespace TauCeti

open MeasureTheory ProbabilityTheory Set

/-- The cumulative distribution function of a Dirac measure is a step function. -/
@[simp]
theorem cdf_dirac (a x : ℝ) : cdf (Measure.dirac a) x = if a ≤ x then 1 else 0 := by
  rw [cdf_eq_real, Measure.real]
  by_cases h : a ≤ x <;> simp [Measure.dirac_apply' _ measurableSet_Iic, h]

/-- Every exponential moment of a Dirac measure exists. -/
@[simp]
theorem integrableExpSet_dirac {Omega : Type*} [MeasurableSpace Omega]
    [MeasurableSingletonClass Omega] (X : Omega → ℝ) (omega : Omega) :
    integrableExpSet X (Measure.dirac omega) = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact integrable_dirac (by simp)

/-- The cumulant-generating function of a Dirac measure is linear. -/
@[simp]
theorem cgf_dirac {Omega : Type*} [MeasurableSpace Omega] [MeasurableSingletonClass Omega]
    (X : Omega → ℝ) (omega : Omega) (t : ℝ) :
    cgf X (Measure.dirac omega) t = t * X omega := by
  rw [cgf, mgf_dirac', Real.log_exp]

end TauCeti
