/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Two-sided invertible equivalence of matrices

Matrices related by `L * A * R` with `L` and `R` invertible. Rows and columns are transformed
independently, so the two index types are separate, and nothing here needs more than a
semiring.

## Main results

* `Matrix.GeneralLinearGroup.inv_mul_mul_inv_of_mul_mul_eq`: inverting a two-sided
  invertible transformation.
-/

namespace Matrix.GeneralLinearGroup

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

public section

/-- **Inverting a two-sided invertible transformation.** The rows and columns are transformed
independently, so they need not share an index type. -/
theorem inv_mul_mul_inv_of_mul_mul_eq {S : Type*} [Semiring S]
    {A B : Matrix ι κ S} (L : GeneralLinearGroup ι S) (R : GeneralLinearGroup κ S)
    (h : (L : Matrix ι ι S) * A * (R : Matrix κ κ S) = B) :
    (↑L⁻¹ : Matrix ι ι S) * B * (↑R⁻¹ : Matrix κ κ S) = A := by
  -- with the rows and columns indexed separately, the two cancellations are named rather
  -- than left to `simp`, which no longer matches them across the differing index types
  have hL : (↑L⁻¹ : Matrix ι ι S) * (L : Matrix ι ι S) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hR : (R : Matrix κ κ S) * (↑R⁻¹ : Matrix κ κ S) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [← h]
  simp only [Matrix.mul_assoc, hR, Matrix.mul_one]
  rw [← Matrix.mul_assoc, hL, Matrix.one_mul]

end

end Matrix.GeneralLinearGroup
