/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Determinant

public section

/-!
# Determinant transformation laws

This file records transformation laws for determinant forms under matrix actions.

## Main results

* `TauCeti.Matrix.detRowAlternating_mulVec` states that multiplication by a square matrix scales
  the standard-basis determinant form by the matrix determinant.
-/

namespace TauCeti

open Matrix

universe u

variable (k : Type u)

namespace Matrix

/-- Multiplication by a square matrix scales the standard-basis determinant form by its
determinant. -/
@[simp]
theorem detRowAlternating_mulVec [CommRing k] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι k) (v : ι → ι → k) :
    Matrix.detRowAlternating (fun i => M *ᵥ v i) =
      M.det * Matrix.detRowAlternating v := by
  simpa only [Pi.basisFun_det, Function.comp_def, Matrix.toLin'_apply, Matrix.mulVecBilin_apply,
    LinearMap.det_toLin'] using
    (Module.Basis.det_comp (Pi.basisFun k ι) (Matrix.toLin' M) v)

end Matrix

end TauCeti
