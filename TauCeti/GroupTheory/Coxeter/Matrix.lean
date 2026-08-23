/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coxeter.Matrix

/-!
# Elementary facts about Coxeter matrices

This file gives convenient equations for entries of Mathlib's type-`A` Coxeter matrix.
-/

public section

namespace TauCeti

variable {m : ℕ} {i j : Fin m}

/-- The entries of Mathlib's type-`A` Coxeter matrix, unfolded. -/
theorem coxeterMatrixA_apply (i j : Fin m) :
    CoxeterMatrix.A m i j =
      if i = j then 1 else if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2 :=
  rfl

/-- Neighbouring indices of the type-`A` Coxeter matrix carry the entry `3`. -/
theorem coxeterMatrixA_eq_three (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    CoxeterMatrix.A m i j = 3 := by
  rw [coxeterMatrixA_apply]
  split_ifs with h₁ h₂
  · exact absurd (congrArg Fin.val h₁) (by omega)
  · rfl
  · exact absurd h.symm h₂

/-- Indices of the type-`A` Coxeter matrix at distance at least two carry the entry `2`. -/
theorem coxeterMatrixA_eq_two (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    CoxeterMatrix.A m i j = 2 := by
  rw [coxeterMatrixA_apply]
  split_ifs with h₁ h₂
  · exact absurd (congrArg Fin.val h₁) (by omega)
  · exact absurd h₂ (by omega)
  · rfl

end TauCeti
