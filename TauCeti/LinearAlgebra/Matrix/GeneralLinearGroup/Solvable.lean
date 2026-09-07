/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Solvable

/-!
# Nonsolvability of `GL₂`

If a field contains an element `a` with `a ≠ 0` and `a² ≠ 1`, then `GL₂` is nonsolvable.
In particular, this holds over every infinite field.

## Main declarations

* `TauCeti.Matrix.GeneralLinearGroup.not_isSolvable_fin_two`: `GL₂` is not solvable when the
  field contains an element outside the roots of `X * (X² - 1)`.
* `TauCeti.Matrix.GeneralLinearGroup.not_isSolvable_fin_two_of_infinite`: the infinite-field
  specialization.
-/

public section

open scoped MatrixGroups

namespace TauCeti.Matrix.GeneralLinearGroup

universe u

/-- The general linear group `GL₂(F)` is not solvable if `F` contains a nonzero element whose
square is not one. -/
theorem not_isSolvable_fin_two (F : Type u) [Field F]
    (hF : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1) : ¬ Group.IsSolvable (GL (Fin 2) F) := by
  intro hGL
  let _ : Group.IsSolvable (GL (Fin 2) F) := hGL
  exact Matrix.SpecialLinearGroup.not_isSolvable_fin_two F hF <|
    Group.isSolvable_of_isSolvable_injective
      (f := Matrix.SpecialLinearGroup.toGL) Matrix.SpecialLinearGroup.toGL_injective

/-- The general linear group `GL₂` over an infinite field is not solvable. -/
theorem not_isSolvable_fin_two_of_infinite (F : Type u) [Field F] [Infinite F] :
    ¬ Group.IsSolvable (GL (Fin 2) F) := by
  intro hGL
  let _ : Group.IsSolvable (GL (Fin 2) F) := hGL
  exact Matrix.SpecialLinearGroup.not_isSolvable_fin_two_of_infinite F <|
    Group.isSolvable_of_isSolvable_injective
      (f := Matrix.SpecialLinearGroup.toGL) Matrix.SpecialLinearGroup.toGL_injective

end TauCeti.Matrix.GeneralLinearGroup
