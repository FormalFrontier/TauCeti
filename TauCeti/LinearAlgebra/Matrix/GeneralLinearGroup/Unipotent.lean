/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.GeneralLinearGroup.Unipotent
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Unipotent matrix automorphisms

This file relates unipotence of the natural linear action of an invertible matrix to nilpotence
of the matrix obtained by subtracting the identity.

## Main declarations

* `TauCeti.GeneralLinearGroup.isUnipotent_toLin_iff` — a matrix acts unipotently exactly when
  subtracting the identity from the matrix gives a nilpotent matrix.
-/

public section

namespace TauCeti.GeneralLinearGroup

universe u

/-- An element of the general linear group is unipotent in its natural representation exactly
when subtracting the identity from its underlying matrix gives a nilpotent matrix. -/
theorem isUnipotent_toLin_iff
    (m : Type*) [Fintype m] [DecidableEq m] (R : Type u) [CommRing R] (g : GL m R) :
    IsUnipotent (Matrix.GeneralLinearGroup.toLin g) ↔
      _root_.IsNilpotent ((g : Matrix m m R) - 1) := by
  rw [isUnipotent_def, ← Matrix.isNilpotent_toLin'_iff, map_sub, Matrix.toLin'_one]
  simp only [Matrix.GeneralLinearGroup.coe_toLin, Matrix.toLin'_apply',
    Module.End.one_eq_id]

end TauCeti.GeneralLinearGroup
