/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Matrix.Normed

/-!
# The Frobenius inner product on real matrices

Mathlib's `Matrix.frobeniusNormedAddCommGroup` equips `Matrix m n ℝ` with the Frobenius norm
while keeping the topology and uniformity definitionally equal to the product ones. This file
adds the compatible real inner product `⟪A, B⟫_ℝ = ∑ i, ∑ j, A i j * B i j`, together with its
description through the trace.

Like the Frobenius norm itself, the inner product is not a global instance, because there are
several natural norms on matrices. It is registered as a scoped instance in the existing
`Matrix.Norms.Frobenius` namespace, so `open scoped Matrix.Norms.Frobenius` activates the norm
and the inner product together.

## Main declarations

* `Matrix.frobeniusInnerProductSpace` — the Frobenius inner product, compatible with
  `Matrix.frobeniusNormedAddCommGroup`.
* `Matrix.frobenius_inner_def` — the inner product is the sum of entrywise products.
* `Matrix.frobenius_inner_eq_trace_transpose_mul` — the inner product is `(Aᵀ * B).trace`.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 6, item 1,
  **Symmetric matrices and their Lebesgue measure**.
-/

public section

noncomputable section

open scoped RealInnerProductSpace

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The Frobenius inner product `⟪A, B⟫_ℝ = ∑ i, ∑ j, A i j * B i j` on real matrices,
compatible with the Frobenius norm of `Matrix.frobeniusNormedAddCommGroup`. Not declared as a
global instance because there are several natural choices of norm on matrices; it is available
through `open scoped Matrix.Norms.Frobenius`. -/
@[expose, instance_reducible]
def frobeniusInnerProductSpace :
    letI : NormedAddCommGroup (Matrix m n ℝ) := Matrix.frobeniusNormedAddCommGroup
    InnerProductSpace ℝ (Matrix m n ℝ) :=
  letI : NormedAddCommGroup (Matrix m n ℝ) := Matrix.frobeniusNormedAddCommGroup
  { __ := (Matrix.frobeniusNormedSpace : NormedSpace ℝ (Matrix m n ℝ))
    inner A B := ∑ i, ∑ j, A i j * B i j
    norm_sq_eq_re_inner A := by
      have h : (0 : ℝ) ≤ ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) :=
        Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _
      rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast _ 2, ← Real.rpow_mul h]
      norm_num [Real.rpow_two, pow_two]
    conj_inner_symm A B := by
      simp [mul_comm]
    add_left A B C := by
      simp [add_mul, Finset.sum_add_distrib]
    smul_left A B r := by
      simp [mul_assoc, Finset.mul_sum] }

namespace Norms.Frobenius

attribute [scoped instance] Matrix.frobeniusInnerProductSpace

end Norms.Frobenius

section lemmas

open scoped Matrix.Norms.Frobenius

theorem frobenius_inner_def (A B : Matrix m n ℝ) : ⟪A, B⟫ = ∑ i, ∑ j, A i j * B i j :=
  rfl

theorem frobenius_inner_eq_trace_transpose_mul (A B : Matrix m n ℝ) :
    ⟪A, B⟫ = (Aᵀ * B).trace := by
  rw [frobenius_inner_def, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

end lemmas

end Matrix
