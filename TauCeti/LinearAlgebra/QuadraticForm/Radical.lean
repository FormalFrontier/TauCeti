/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Radical API for quadratic forms

This file records general consequences of nondegeneracy for quadratic forms.
-/

public section

namespace QuadraticMap.Nondegenerate

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A nondegenerate quadratic form on a nontrivial module is nonzero. -/
theorem ne_zero [Nontrivial M] {Q : QuadraticForm R M} (hQ : Q.Nondegenerate) : Q ≠ 0 := by
  intro hzero
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  apply hv
  have hm : v ∈ Q.radical := by
    rw [hzero, QuadraticMap.mem_radical_iff']
    simp
  rwa [hQ.radical_eq_bot, Submodule.mem_bot] at hm

end QuadraticMap.Nondegenerate
