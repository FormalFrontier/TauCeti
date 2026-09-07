/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The modular-group generator in special linear groups

This module records the matrix of the standard modular-group generator after scalar extension
from `SL₂(ℤ)` to `SL₂(R)`.

## Main declaration

* `TauCeti.Matrix.SpecialLinearGroup.coe_modularGroup_S`: the scalar extension of
  `ModularGroup.S` has matrix `!![0, -1; 1, 0]`.
-/

public section

open Matrix
open scoped MatrixGroups

namespace TauCeti.Matrix.SpecialLinearGroup

universe u

/-- The scalar extension of `ModularGroup.S` to a commutative ring has its standard matrix. -/
theorem coe_modularGroup_S {R : Type u} [CommRing R] :
    (((ModularGroup.S : SL(2, ℤ)) : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) =
      !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_matrix_coe, ModularGroup.coe_S]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end TauCeti.Matrix.SpecialLinearGroup
