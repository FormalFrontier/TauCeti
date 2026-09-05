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

Over an infinite field, `SL₂` is nonsolvable. The proof uses Mathlib's computation that its
commutator subgroup is the whole group.

## Main declaration

* `Matrix.SpecialLinearGroup.not_isSolvable_fin_two`: `SL₂` over an infinite field is not
  solvable.
-/

public section

open scoped MatrixGroups

namespace TauCeti.Matrix.SpecialLinearGroup

universe u

/-- The special linear group `SL₂` over an infinite field is not solvable. -/
theorem not_isSolvable_fin_two (F : Type u) [Field F] [Infinite F] :
    ¬ Group.IsSolvable SL(2, F) := by
  let S : Set F := {0} ∪ {1} ∪ {-1}
  let U := {x : F // x ∈ Sᶜ}
  let _ : Infinite U := (Set.toFinite S).infinite_compl.to_subtype
  obtain ⟨a, _, _⟩ := exists_pair_ne U
  have ha0 : (a : F) ≠ 0 := by
    intro h
    apply a.property
    simp [S, h]
  have ha1 : (a : F) ^ 2 ≠ 1 := by
    rw [sq_ne_one_iff]
    constructor
    · intro h
      apply a.property
      simp [S, h]
    · intro h
      apply a.property
      simp [S, h]
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

end TauCeti.Matrix.SpecialLinearGroup
