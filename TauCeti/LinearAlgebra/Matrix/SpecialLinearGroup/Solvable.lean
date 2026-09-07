/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.IsPerfect

/-!
# Nonsolvability of `SL₂`

If a field contains an element `a` with `a ≠ 0` and `a² ≠ 1`, then `SL₂` is nonsolvable.
In particular, this holds over every infinite field.

## Main declarations

* `TauCeti.Matrix.SpecialLinearGroup.not_isSolvable_fin_two`: `SL₂` is not solvable when the
  field contains an element outside the roots of `X * (X² - 1)`.
* `TauCeti.Matrix.SpecialLinearGroup.not_isSolvable_fin_two_of_infinite`: the infinite-field
  specialization.
-/

public section

open scoped MatrixGroups

namespace TauCeti.Matrix.SpecialLinearGroup

universe u

/-- The special linear group `SL₂(F)` is not solvable if `F` contains a nonzero element whose
square is not one. -/
theorem not_isSolvable_fin_two (F : Type u) [Field F]
    (hF : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1) : ¬ Group.IsSolvable SL(2, F) := by
  obtain ⟨a, ha0, ha1⟩ := hF
  let _ : Group.IsPerfect SL(2, F) := ⟨Matrix.SL2.commutator_eq_top ha0 ha1⟩
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  let t : SL(2, F) := Matrix.SpecialLinearGroup.transvection h01 1
  have ht : t ≠ 1 := by
    intro ht
    have hentry := congrArg
      (fun s : SL(2, F) ↦ (s : Matrix (Fin 2) (Fin 2) F) 0 1) ht
    simp [t, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single] at hentry
  let _ : Nontrivial SL(2, F) := ⟨t, 1, ht⟩
  exact Group.IsPerfect.not_isSolvable SL(2, F)

/-- The special linear group `SL₂` over an infinite field is not solvable. -/
theorem not_isSolvable_fin_two_of_infinite (F : Type u) [Field F] [Infinite F] :
    ¬ Group.IsSolvable SL(2, F) := by
  apply not_isSolvable_fin_two F
  classical
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset F)
  have ha' : a ≠ 0 ∧ a ≠ 1 ∧ a ≠ -1 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using ha
  exact ⟨a, ha'.1, sq_ne_one_iff.mpr ha'.2⟩

end TauCeti.Matrix.SpecialLinearGroup
