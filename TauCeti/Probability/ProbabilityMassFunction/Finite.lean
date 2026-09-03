/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Finite sums for probability mass functions

This file records elementary finite-sum identities for probability mass functions, including the
row- and column-sum formulas for the marginals of a product PMF on finite types.

## Main results

* `PMF.sum_toReal_eq_one`: the real values of a PMF on a finite type sum to one.
* `PMF.map_fst_apply_fintype`, `PMF.map_snd_apply_fintype`: the two marginals of a finite
  product PMF are its row and column sums.
* `PMF.map_fst_eq_iff_fintype`, `PMF.map_snd_eq_iff_fintype`: characterizations of prescribed
  marginals by those sums.
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

section Fst

variable [Fintype κ] (π : PMF (ι × κ))

/-- The first marginal of a finite product PMF is obtained by summing each row of its matrix of
point masses. -/
theorem map_fst_apply_fintype (i : ι) : π.map Prod.fst i = ∑ j, π (i, j) := by
  classical
  rw [PMF.map_apply, ENNReal.tsum_prod']
  rw [tsum_eq_single i]
  · simp
  · intro i' hi
    simp [hi.symm]

/-- A finite product PMF has first marginal `μ` exactly when its row sums are `μ`. -/
theorem map_fst_eq_iff_fintype (μ : PMF ι) :
    π.map Prod.fst = μ ↔ ∀ i, ∑ j, π (i, j) = μ i := by
  rw [PMF.ext_iff]
  simp only [map_fst_apply_fintype]

end Fst

section Snd

variable [Fintype ι] (π : PMF (ι × κ))

/-- The second marginal of a finite product PMF is obtained by summing each column of its matrix
of point masses. -/
theorem map_snd_apply_fintype (j : κ) : π.map Prod.snd j = ∑ i, π (i, j) := by
  classical
  rw [PMF.map_apply, ENNReal.tsum_prod']
  simp

/-- A finite product PMF has second marginal `ν` exactly when its column sums are `ν`. -/
theorem map_snd_eq_iff_fintype (ν : PMF κ) :
    π.map Prod.snd = ν ↔ ∀ j, ∑ i, π (i, j) = ν j := by
  rw [PMF.ext_iff]
  simp only [map_snd_apply_fintype]

end Snd

end PMF
