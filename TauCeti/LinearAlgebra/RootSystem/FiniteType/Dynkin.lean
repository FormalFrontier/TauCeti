/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic
import TauCeti.LinearAlgebra.RootSystem.E8Coordinates
import Mathlib.Data.Rat.Star

public section

/-!
# Exceptional Cartan matrices are of finite type

This file proves that the five exceptional Cartan matrices in `TauCeti.DynkinType` are of finite
type.  The proof exhibits each symmetrized Cartan matrix as `Bᴴ * B` for an explicit rational
matrix `B` and reads off positive definiteness from
`TauCeti.isFiniteType_of_conjTranspose_mul_self_of_det_ne_zero`.

The columns of `B` are the simple **coroots** `αᵢ^∨ = 2 αᵢ / (αᵢ, αᵢ)`, in orthonormal rational
coordinates and up to one common positive scale, rather than the simple roots themselves.  That is
forced by the symmetrizer: the symmetrization `dᵢ Aᵢⱼ` is symmetric exactly when `dᵢ` is
proportional to `1 / (αᵢ, αᵢ)`, and then `dᵢ Aᵢⱼ` is proportional to `(αᵢ^∨, αⱼ^∨)`.  The two
readings agree for the simply-laced `E₈`, where all roots have the same length, and differ for
`F₄` and `G₂`, where a column of `B` is longest exactly where the corresponding root is shortest.
Node numbering is Bourbaki's throughout: column `i` belongs to node `i` of `TauCeti.DynkinType`.

Only `E₈` needs a coordinate model among the simply-laced types: the `E₆` and `E₇` Cartan matrices
are the principal submatrices of the `E₈` one on the first six and seven indices, so
`TauCeti.IsFiniteType.submatrix` delivers them.  That one model is not tabulated here but taken
from `TauCeti.LinearAlgebra.RootSystem.E8Coordinates`, whose integral table has twice the simple
roots as its rows; halving and transposing it gives the `B` above.  The nonsimply-laced types use
the integral symmetrizers `(1, 1, 2, 2)` for `F₄` and `(3, 1)` for `G₂`, the inverse root lengths
recorded in `TauCeti.DynkinType.rootLength_F4` and `TauCeti.DynkinType.rootLength_G2`.

## Main results

* `TauCeti.DynkinType.isFiniteType_cartanMatrix_E8`
* `TauCeti.DynkinType.isFiniteType_cartanMatrix_E6`
* `TauCeti.DynkinType.isFiniteType_cartanMatrix_E7`
* `TauCeti.DynkinType.isFiniteType_cartanMatrix_F4`
* `TauCeti.DynkinType.isFiniteType_cartanMatrix_G2`
* `TauCeti.DynkinType.cartanMatrix_E6_eq_submatrix_E8` and
  `TauCeti.DynkinType.cartanMatrix_E7_eq_submatrix_E8`: the nesting `E₆ ⊂ E₇ ⊂ E₈` at the level of
  Cartan matrices, which is what makes the two derivations above possible.

## References

This file advances the "classification of finite-type Cartan matrices" target in Layer 5 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`.  The `E₈` model is the list of simple
roots of Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, plate VII; the `F₄` and `G₂`
models are the coroots dual to the simple roots of plates VIII and IX.  See also Humphreys,
*Introduction to Lie Algebras and Representation Theory*, Chapter 11.
-/

open scoped Matrix

namespace TauCeti.DynkinType

/-- The coordinate model of type `E₈`: column `i` is the simple root `αᵢ₊₁` of Bourbaki's plate
VII, in the orthonormal coordinates `ε₁, ..., ε₈` used there.  `E₈` being simply laced, these are
also the simple coroots, and the Gram matrix of the columns is the `E₈` Cartan matrix itself.
The coordinates are read off the shared integral table `TauCeti.DynkinType.e8DoubledSimpleRoot`,
whose rows are twice them. -/
private def rootsE8 : _root_.Matrix (Fin 8) (Fin 8) ℚ :=
  (2 : ℚ)⁻¹ • (e8DoubledSimpleRoot.map ((↑) : ℤ → ℚ))ᵀ

/-- The standard Cartan matrix of type `E₈` is of finite type. -/
theorem isFiniteType_cartanMatrix_E8 : IsFiniteType E8.cartanMatrix := by
  have hgram : _root_.Matrix.of (fun i j ↦ (1 : ℚ) * (CartanMatrix.E 8 i j : ℚ))
      = rootsE8ᴴ * rootsE8 := by
    ext i j
    -- The `(i, j)` entry of the Gram matrix of the doubled rows is four times the Cartan entry.
    have hrow : ∑ k, e8DoubledSimpleRoot i k * e8DoubledSimpleRoot j k
        = 4 * CartanMatrix.E 8 i j := by
      have h := congrFun (congrFun e8DoubledSimpleRoot_mul_transpose i) j
      simpa [_root_.Matrix.mul_apply, _root_.Matrix.transpose_apply] using h
    have hrowQ : ∑ k, (e8DoubledSimpleRoot i k : ℚ) * (e8DoubledSimpleRoot j k : ℚ)
        = 4 * (CartanMatrix.E 8 i j : ℚ) := by exact_mod_cast hrow
    -- Halving both factors divides each term of that sum by four.
    have hpoint : ∀ k : Fin 8, (2 : ℚ)⁻¹ * (e8DoubledSimpleRoot i k : ℚ) *
        ((2 : ℚ)⁻¹ * (e8DoubledSimpleRoot j k : ℚ))
        = 4⁻¹ * ((e8DoubledSimpleRoot i k : ℚ) * (e8DoubledSimpleRoot j k : ℚ)) :=
      fun k ↦ by ring
    simp only [rootsE8, _root_.Matrix.of_apply, _root_.Matrix.mul_apply,
      _root_.Matrix.conjTranspose_apply, _root_.Matrix.smul_apply, _root_.Matrix.transpose_apply,
      _root_.Matrix.map_apply, star_trivial, smul_eq_mul]
    rw [Finset.sum_congr rfl fun k _ ↦ hpoint k, ← Finset.mul_sum, hrowQ]
    ring
  have hdet : (CartanMatrix.E 8).det ≠ 0 := by rw [CartanMatrix.E₈_det]; norm_num
  rw [cartanMatrix_E8]
  exact isFiniteType_of_conjTranspose_mul_self_of_det_ne_zero (CartanMatrix.E_diag 8)
    (CartanMatrix.E_off_diag_nonpos 8) (d := fun _ ↦ 1) (fun _ ↦ by positivity) hgram hdet

/-- The `E₆` Cartan matrix is the principal submatrix of the `E₈` one on the first six nodes: in
Bourbaki's numbering the exceptional `E` diagrams are nested, `E₆ ⊂ E₇ ⊂ E₈`. -/
theorem cartanMatrix_E6_eq_submatrix_E8 :
    CartanMatrix.E 6
      = (CartanMatrix.E 8).submatrix (Fin.castAdd 2 : Fin 6 → Fin 8) (Fin.castAdd 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The `E₇` Cartan matrix is the principal submatrix of the `E₈` one on the first seven nodes: in
Bourbaki's numbering the exceptional `E` diagrams are nested, `E₆ ⊂ E₇ ⊂ E₈`. -/
theorem cartanMatrix_E7_eq_submatrix_E8 :
    CartanMatrix.E 7
      = (CartanMatrix.E 8).submatrix (Fin.castAdd 1 : Fin 7 → Fin 8) (Fin.castAdd 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The standard Cartan matrix of type `E₆` is of finite type: it is the principal submatrix of the
`E₈` Cartan matrix on the first six indices. -/
theorem isFiniteType_cartanMatrix_E6 : IsFiniteType E6.cartanMatrix := by
  simp only [cartanMatrix_E6, cartanMatrix_E6_eq_submatrix_E8]
  exact (cartanMatrix_E8 ▸ isFiniteType_cartanMatrix_E8).submatrix (Fin.castAdd_injective 6 2)

/-- The standard Cartan matrix of type `E₇` is of finite type: it is the principal submatrix of the
`E₈` Cartan matrix on the first seven indices. -/
theorem isFiniteType_cartanMatrix_E7 : IsFiniteType E7.cartanMatrix := by
  simp only [cartanMatrix_E7, cartanMatrix_E7_eq_submatrix_E8]
  exact (cartanMatrix_E8 ▸ isFiniteType_cartanMatrix_E8).submatrix (Fin.castAdd_injective 7 1)

/-- The coordinate model of type `F₄`: column `i` is the simple coroot `αᵢ₊₁^∨` of Bourbaki's plate
VIII, in the orthonormal coordinates `ε₁, ..., ε₄` used there, cyclically relabelled so that `ε₁`
comes last.  Columns `2` and `3` are the long ones, being dual to the two short simple roots
recorded in `TauCeti.DynkinType.rootLength_F4`. -/
private def corootsF4 : _root_.Matrix (Fin 4) (Fin 4) ℚ :=
  !![ 1,  0,  0, -1;
     -1,  1,  0, -1;
      0, -1,  2, -1;
      0,  0,  0,  1]

/-- The standard Cartan matrix of type `F₄` is of finite type. -/
theorem isFiniteType_cartanMatrix_F4 : IsFiniteType F4.cartanMatrix := by
  have hd : ∀ i, (0 : ℚ) < ![1, 1, 2, 2] i := by intro i; fin_cases i <;> norm_num
  have hgram : _root_.Matrix.of (fun i j ↦ ![1, 1, 2, 2] i * (CartanMatrix.F₄ i j : ℚ))
      = corootsF4ᴴ * corootsF4 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [corootsF4, CartanMatrix.F₄, _root_.Matrix.mul_apply, Fin.sum_univ_succ,
        _root_.Matrix.cons_val_succ]
  have hdet : CartanMatrix.F₄.det ≠ 0 := by rw [CartanMatrix.F₄_det]; norm_num
  rw [cartanMatrix_F4]
  exact isFiniteType_of_conjTranspose_mul_self_of_det_ne_zero CartanMatrix.F₄_diag
    CartanMatrix.F₄_off_diag_nonpos (d := ![1, 1, 2, 2]) hd hgram hdet

/-- The coordinate model of type `G₂`: column `i` is the simple coroot `αᵢ₊₁^∨` of Bourbaki's plate
IX, scaled by the common factor `√3` and written in an orthonormal basis of `ℚ³` for which the
scaled vectors have rational coordinates.  Plate IX's own coordinates are unusable as they stand,
since `α₂^∨` has denominator `3` there; only the Gram matrix of the columns matters, and the
scaling is what makes it integral.  Column `0` is the long one, being dual to the short simple root
recorded in `TauCeti.DynkinType.rootLength_G2`. -/
private def corootsG2 : _root_.Matrix (Fin 3) (Fin 2) ℚ :=
  !![ 1, -1;
     -2,  1;
      1,  0]

/-- The standard Bourbaki-numbered Cartan matrix of type `G₂` is of finite type. -/
theorem isFiniteType_cartanMatrix_G2 : IsFiniteType G2.cartanMatrix := by
  have hd : ∀ i, (0 : ℚ) < ![3, 1] i := by intro i; fin_cases i <;> norm_num
  have hgram : _root_.Matrix.of (fun i j ↦ ![3, 1] i * (CartanMatrix.G₂ᵀ i j : ℚ))
      = corootsG2ᴴ * corootsG2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [corootsG2, CartanMatrix.G₂, _root_.Matrix.mul_apply, Fin.sum_univ_succ,
        _root_.Matrix.cons_val_succ]
  have hdet : CartanMatrix.G₂ᵀ.det ≠ 0 := by
    rw [_root_.Matrix.det_transpose, CartanMatrix.G₂_det]; norm_num
  rw [cartanMatrix_G2]
  -- The generalized Cartan matrix axioms transpose: `G₂ᵀ i j` is `G₂ j i` by definition.
  exact isFiniteType_of_conjTranspose_mul_self_of_det_ne_zero
    (fun i ↦ CartanMatrix.G₂_diag i)
    (fun i j hij ↦ CartanMatrix.G₂_off_diag_nonpos j i hij.symm)
    (d := ![3, 1]) hd hgram hdet

end TauCeti.DynkinType
