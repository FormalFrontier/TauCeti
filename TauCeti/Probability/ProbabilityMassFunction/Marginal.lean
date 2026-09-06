/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Marginals of a probability mass function on a product

This file records the two marginals of a probability mass function on an arbitrary product as the
infinite row and column sums of its matrix of point masses, together with the resulting
characterizations of a prescribed marginal.

## Main results

* `PMF.map_fst_apply`, `PMF.map_snd_apply`: the two marginals of a product PMF are its infinite row
  and column sums.
* `PMF.map_fst_eq_iff`, `PMF.map_snd_eq_iff`: characterizations of prescribed marginals by those
  sums.
-/

public section

noncomputable section

open scoped ENNReal

universe u v

namespace PMF

variable {ι : Type u} {κ : Type v} (π : PMF (ι × κ))

/-- The first marginal of a product PMF is obtained by summing each row of its matrix of point
masses. -/
theorem map_fst_apply (i : ι) : π.map Prod.fst i = ∑' j, π (i, j) := by
  classical
  rw [PMF.map_apply, ENNReal.tsum_prod']
  rw [tsum_eq_single i]
  · simp
  · intro i' hi
    simp [hi.symm]

/-- A product PMF has first marginal `μ` exactly when its infinite row sums are `μ`. -/
theorem map_fst_eq_iff (μ : PMF ι) :
    π.map Prod.fst = μ ↔ ∀ i, ∑' j, π (i, j) = μ i := by
  rw [PMF.ext_iff]
  simp only [map_fst_apply]

/-- The second marginal of a product PMF is obtained by summing each column of its matrix of point
masses. -/
theorem map_snd_apply (j : κ) : π.map Prod.snd j = ∑' i, π (i, j) := by
  classical
  rw [PMF.map_apply, ENNReal.tsum_prod']
  simp

/-- A product PMF has second marginal `ν` exactly when its infinite column sums are `ν`. -/
theorem map_snd_eq_iff (ν : PMF κ) :
    π.map Prod.snd = ν ↔ ∀ j, ∑' i, π (i, j) = ν j := by
  rw [PMF.ext_iff]
  simp only [map_snd_apply]

end PMF
