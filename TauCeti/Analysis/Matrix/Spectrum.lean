/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.PosDef

/-!
# Eigen-coordinates of a real symmetric matrix

Let `B` be a real symmetric matrix with orthonormal eigenvector basis `hB.eigenvectorBasis` and
eigenvalues `hB.eigenvalues`. This file reads three quantities off the eigen-coordinates: the
quadratic form `x ↦ ⟪x, B x⟫`, which becomes a weighted sum of squares, and the positivity and
the determinant of the pencil `1 - c • B`, which become conditions on the numbers
`1 - c * hB.eigenvalues j`.

These are the spectral facts behind the moment-generating function of a Gaussian quadratic form,
whose exponential-integrability domain is a positive-definiteness condition on such a pencil and
whose value is a power of its determinant.

## Main results

* `Matrix.IsHermitian.inner_toEuclideanLin_sum_smul_eigenvectorBasis` — the quadratic form of
  `B` at `∑ j, c j • b j` is `∑ j, hB.eigenvalues j * c j ^ 2`;
* `Matrix.IsHermitian.posDef_one_sub_smul_iff` — `1 - c • B` is positive definite exactly when
  `c * hB.eigenvalues j < 1` for every `j`;
* `Matrix.IsHermitian.det_one_sub_smul` — the determinant of `1 - c • B` is
  `∏ j, (1 - c * hB.eigenvalues j)`.
-/

public section

noncomputable section

open Unitary
open scoped RealInnerProductSpace

namespace Matrix.IsHermitian

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℝ} (hB : B.IsHermitian)
include hB

/-- In the eigen-coordinates of a real symmetric matrix, its quadratic form is the sum of the
squares of the coordinates weighted by the eigenvalues. -/
theorem inner_toEuclideanLin_sum_smul_eigenvectorBasis (c : ι → ℝ) :
    ⟪∑ j, c j • hB.eigenvectorBasis j,
      B.toEuclideanLin (∑ j, c j • hB.eigenvectorBasis j)⟫ =
      ∑ j, hB.eigenvalues j * c j ^ 2 := by
  have hb (j : ι) : B.toEuclideanLin (hB.eigenvectorBasis j) =
      hB.eigenvalues j • hB.eigenvectorBasis j := by
    simp [toLpLin_apply, hB.mulVec_eigenvectorBasis]
  rw [map_sum]
  simp_rw [map_smul, hb, smul_smul]
  rw [hB.eigenvectorBasis.orthonormal.inner_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [conj_trivial]; ring

/-- The pencil `1 - c • B` is conjugate, by the eigenvector unitary of `B`, to the diagonal matrix
with entries `1 - c * hB.eigenvalues j`. -/
theorem one_sub_smul_eq_conjStarAlgAut (c : ℝ) :
    1 - c • B =
      conjStarAlgAut ℝ _ hB.eigenvectorUnitary (diagonal fun j => 1 - c * hB.eigenvalues j) := by
  have h : (diagonal fun j => 1 - c * hB.eigenvalues j) =
      1 - c • diagonal (RCLike.ofReal ∘ hB.eigenvalues) := by
    simp [← diagonal_one, ← diagonal_sub, ← diagonal_smul, Pi.smul_def]
  rw [h, map_sub, map_one, map_smul, ← hB.spectral_theorem]

open scoped ComplexOrder in
/-- The pencil `1 - c • B` is positive definite exactly when `c * hB.eigenvalues j < 1` for every
eigenvalue. -/
theorem posDef_one_sub_smul_iff (c : ℝ) :
    (1 - c • B).PosDef ↔ ∀ j, c * hB.eigenvalues j < 1 := by
  rw [hB.one_sub_smul_eq_conjStarAlgAut c, conjStarAlgAut_apply,
    IsUnit.posDef_star_right_conjugate_iff isUnit_coe, posDef_diagonal_iff]
  simp [sub_pos]

/-- The determinant of the pencil `1 - c • B` is the product of `1 - c * hB.eigenvalues j` over
the eigenvalues. -/
theorem det_one_sub_smul (c : ℝ) :
    (1 - c • B).det = ∏ j, (1 - c * hB.eigenvalues j) := by
  rw [hB.one_sub_smul_eq_conjStarAlgAut c, conjStarAlgAut_apply, det_mul, det_mul,
    mul_right_comm, ← det_mul, mul_star_self_of_mem hB.eigenvectorUnitary.2, det_one,
    one_mul, det_diagonal]

end Matrix.IsHermitian
