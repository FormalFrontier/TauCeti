/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Probability mass functions on finite types

This file records elementary real-valued finite-sum identities for probability mass functions.
-/

public section

noncomputable section

open scoped BigOperators ENNReal

universe u

namespace PMF

variable {ι : Type u}

/-- The real values of a probability mass function on a finite type sum to one. -/
@[simp]
theorem sum_toReal_eq_one [Fintype ι] (μ : PMF ι) : ∑ i, (μ i).toReal = 1 := by
  have h : ∑ i, μ i = 1 := (tsum_fintype fun i ↦ μ i).symm.trans μ.tsum_coe
  rw [← ENNReal.toReal_sum fun i _ ↦ μ.apply_ne_top i, h, ENNReal.toReal_one]

end PMF
