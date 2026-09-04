/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection

/-!
# Packaging nonsingular matrices in the general linear group

Over a field, `Matrix.GeneralLinearGroup.mkOfDetNeZero` packages a matrix with nonzero
determinant as an element of `GL`. This file records how that packaging interacts with matrix
multiplication, existing general-linear elements, and transvections.

## Main results

* `Matrix.GeneralLinearGroup.mkOfDetNeZero_mul`: packaging a matrix product agrees with
  multiplication in `GL`.
* `Matrix.GeneralLinearGroup.mkOfDetNeZero_coe`: repackaging the matrix of an element
  of `GL` recovers that element.
* `Matrix.GeneralLinearGroup.mkOfDetNeZero_transvection`: packaging a transvection
  recovers its canonical element of `GL`.
-/

public section

open Matrix

namespace Matrix.GeneralLinearGroup

universe u v

variable {n : Type u} [Fintype n] [DecidableEq n]
variable {K : Type v} [Field K]

/-- Packaging a product by `mkOfDetNeZero` agrees with multiplication in `GL`. -/
@[simp]
theorem mkOfDetNeZero_mul (M N : Matrix n n K) (hM : M.det ≠ 0) (hN : N.det ≠ 0) :
    mkOfDetNeZero (M * N) (by
        rw [Matrix.det_mul]
        exact mul_ne_zero hM hN) =
      mkOfDetNeZero M hM * mkOfDetNeZero N hN := by
  apply ext
  intro i j
  simp

/-- Repackaging the matrix underlying an element of `GL` by `mkOfDetNeZero` recovers that
element. -/
@[simp]
theorem mkOfDetNeZero_coe (A : GL n K) :
    mkOfDetNeZero (A : Matrix n n K) A.det_ne_zero = A := by
  apply ext
  intro i j
  simp

/-- Packaging a transvection matrix by `mkOfDetNeZero` recovers its canonical element of
`GL`. -/
@[simp]
theorem mkOfDetNeZero_transvection {i j : n} (hij : i ≠ j) (c : K) :
    mkOfDetNeZero
        (Matrix.transvection i j c) (by
          rw [Matrix.det_transvection_of_ne i j hij c]
          exact one_ne_zero) =
      (Matrix.SpecialLinearGroup.transvection hij c).toGL := by
  rw [TauCeti.toGL_transvection_eq_transvectionUnit]
  apply ext
  intro a b
  simp only [TauCeti.coe_transvectionUnit]
  simp

end Matrix.GeneralLinearGroup
