/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.ProbabilityMassFunction.Marginal

/-!
# Finite sums for probability mass functions

This file records the summation identities for probability mass functions that need a finiteness
hypothesis: the total mass on a finite type, and the finite-sum specializations of the marginal
formulas of `TauCeti.Probability.ProbabilityMassFunction.Marginal`.

## Main results

* `PMF.sum_toReal_eq_one`: the real values of a PMF on a finite type sum to one.
* `PMF.map_fst_apply_fintype`, `PMF.map_snd_apply_fintype`: the two marginals of a product PMF are
  its row and column sums whenever the factor being summed over is finite.
* `PMF.map_fst_eq_iff_fintype`, `PMF.map_snd_eq_iff_fintype`: characterizations of prescribed
  marginals by those finite sums.
-/

public section

noncomputable section

open scoped BigOperators ENNReal

universe u v

namespace PMF

variable {ι : Type u} {κ : Type v}

/-- The real values of a probability mass function on a finite type sum to one. -/
@[simp]
theorem sum_toReal_eq_one [Fintype ι] (μ : PMF ι) : ∑ i, (μ i).toReal = 1 := by
  have h : ∑ i, μ i = 1 := (tsum_fintype fun i ↦ μ i).symm.trans μ.tsum_coe
  rw [← ENNReal.toReal_sum fun i _ ↦ μ.apply_ne_top i, h, ENNReal.toReal_one]

variable (π : PMF (ι × κ))

/-- The first marginal of a product PMF with finite second factor is obtained by summing each row
of its matrix of point masses. -/
theorem map_fst_apply_fintype [Fintype κ] (i : ι) : π.map Prod.fst i = ∑ j, π (i, j) := by
  rw [map_fst_apply, tsum_fintype]

/-- A product PMF with finite second factor has first marginal `μ` exactly when its row sums are
`μ`. -/
theorem map_fst_eq_iff_fintype [Fintype κ] (μ : PMF ι) :
    π.map Prod.fst = μ ↔ ∀ i, ∑ j, π (i, j) = μ i := by
  rw [map_fst_eq_iff]
  simp only [tsum_fintype]

/-- The second marginal of a product PMF with finite first factor is obtained by summing each
column of its matrix of point masses. -/
theorem map_snd_apply_fintype [Fintype ι] (j : κ) : π.map Prod.snd j = ∑ i, π (i, j) := by
  rw [map_snd_apply, tsum_fintype]

/-- A product PMF with finite first factor has second marginal `ν` exactly when its column sums are
`ν`. -/
theorem map_snd_eq_iff_fintype [Fintype ι] (ν : PMF κ) :
    π.map Prod.snd = ν ↔ ∀ j, ∑ i, π (i, j) = ν j := by
  rw [map_snd_eq_iff]
  simp only [tsum_fintype]

end PMF
