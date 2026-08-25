/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Diagonal

/-!
# A Laurent-polynomial path in the special linear group

Specializing the generic Laurent unit in the two-coordinate unit diagonal family recovers
Mathlib's `Matrix.SpecialLinearGroup.diag2n` matrix. This supplies the diagonal one-parameter
family used to prove connectedness of `SLₙ`.

## Main declarations

* `TauCeti.SpecialLinear.map_diag2nUnit_genericUnit`: specialization of the generic Laurent
  matrix.
-/

public section

open scoped LaurentPolynomial

namespace TauCeti.SpecialLinear

universe u v

noncomputable section

/-- Evaluating the generic Laurent diagonal matrix at a unit `b` gives the ordinary
two-coordinate diagonal matrix with entries `b` and `b⁻¹`. -/
theorem map_diag2nUnit_genericUnit
    {K : Type u} [Field K] {m : Type v} [Fintype m] [DecidableEq m]
    {i j : m} (hij : i ≠ j) (b : Kˣ) :
    Matrix.SpecialLinearGroup.map
        (MultiplicativeGroup.point (R := K) b).toRingHom
        (Matrix.SpecialLinearGroup.diag2nUnit hij (MultiplicativeGroup.genericUnit K)) =
      Matrix.SpecialLinearGroup.diag2n hij (b : K) (Units.ne_zero b) := by
  rw [Matrix.SpecialLinearGroup.map_diag2nUnit]
  have hunit : Units.map (MultiplicativeGroup.point (R := K) b).toRingHom
      (MultiplicativeGroup.genericUnit K) = b := by
    exact ((MultiplicativeGroup.map_genericUnit K
      (MultiplicativeGroup.point (R := K) b)).trans
        (MultiplicativeGroup.unitOfPoint_point b))
  calc
    Matrix.SpecialLinearGroup.diag2nUnit hij
        (Units.map (MultiplicativeGroup.point (R := K) b).toRingHom
          (MultiplicativeGroup.genericUnit K)) =
        Matrix.SpecialLinearGroup.diag2nUnit hij b := congrArg _ hunit
    _ = Matrix.SpecialLinearGroup.diag2n hij (b : K) (Units.ne_zero b) := by
      simpa using
        Matrix.SpecialLinearGroup.diag2nUnit_mk0 hij (b : K) (Units.ne_zero b)

end

end TauCeti.SpecialLinear
