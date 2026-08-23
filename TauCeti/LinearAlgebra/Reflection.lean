/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Reflection
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Determinant of a module reflection

This file computes the determinant of Mathlib's `Module.reflection` on a finite free module.
-/

public section

universe u v

namespace Module

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {x : M} {f : Module.Dual R M} (h : f x = 2)

/-- The determinant of a module reflection is `-1` on a finite free module. -/
@[simp]
theorem det_reflection [Module.Free R M] [Module.Finite R M] :
    LinearEquiv.det (reflection h) = (-1 : Rˣ) := by
  apply Units.ext
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix (Module.Free.chooseBasis R M)]
  let b := Module.Free.chooseBasis R M
  rw [reflection]
  -- Unfold the reflection into its rank-one perturbation before applying the determinant lemma.
  change Matrix.det (LinearMap.toMatrix b b (LinearMap.id - f.smulRight x)) = -1
  rw [map_sub, LinearMap.toMatrix_id, LinearMap.toMatrix_smulRight]
  -- The rank-one determinant lemma is stated for a column matrix times a row matrix.
  rw [show Matrix.vecMulVec (b.repr x) (f ∘ b) =
      Matrix.replicateCol Unit (b.repr x) * Matrix.replicateRow Unit (f ∘ b) by
      ext i j
      simp [Matrix.mul_apply, Matrix.vecMulVec_apply]]
  rw [sub_eq_add_neg, ← Matrix.neg_mul]
  -- Put the matrix in the exact Schur-complement rank-one form.
  change Matrix.det
    (1 + Matrix.replicateCol Unit (-b.repr x) * Matrix.replicateRow Unit (f ∘ b)) = -1
  rw [Matrix.det_one_add_replicateCol_mul_replicateRow]
  -- The remaining scalar is `1 - f x = -1`.
  change 1 + ∑ i, f (b i) * -(b.repr x i) = -1
  simp_rw [mul_neg, mul_comm (f (b _))]
  rw [Finset.sum_neg_distrib]
  have hsum : ∑ i, b.repr x i * f (b i) = f x := by
    calc
      _ = ∑ i, f ((b.repr x i) • b i) := by
        simp only [map_smul, smul_eq_mul]
      _ = f (∑ i, (b.repr x i) • b i) := by rw [map_sum]
      _ = f x := congrArg f (b.sum_repr x)
  rw [hsum, h]
  ring

end Module
