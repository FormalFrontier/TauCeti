/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic
import Mathlib.Data.Rat.Star

public section

/-!
# Exceptional Cartan matrices are of finite type

This file proves that the five exceptional Cartan matrices in `TauCeti.DynkinType` are of finite
type.  The proof exhibits each symmetrized Cartan matrix as `Bᴴ * B`, where the columns of `B`
are the standard simple roots in rational Euclidean coordinates.  Linear independence of those
columns then makes the Gram matrix positive definite.

For the simply-laced types `E₆`, `E₇`, and `E₈`, the first columns of a single eight-dimensional
coordinate model are used.  The nonsimply-laced types use the integral symmetrizers `(1, 1, 2, 2)`
for `F₄` and `(3, 1)` for `G₂`.

## Main results

* `TauCeti.DynkinType.isFiniteType_cartanMatrix_E6`
* `TauCeti.DynkinType.isFiniteType_cartanMatrix_E7`
* `TauCeti.DynkinType.isFiniteType_cartanMatrix_E8`
* `TauCeti.DynkinType.isFiniteType_cartanMatrix_F4`
* `TauCeti.DynkinType.isFiniteType_cartanMatrix_G2`

## References

This file advances the "classification of finite-type Cartan matrices" target in Layer 5 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`.  The coordinate models follow
Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, plates V--IX; see also Humphreys,
*Introduction to Lie Algebras and Representation Theory*, Chapter 11.
-/

open scoped Matrix

namespace TauCeti.DynkinType

private lemma posDef_of_gram {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : _root_.Matrix n n ℚ) (B : _root_.Matrix m n ℚ) (hgram : M = Bᴴ * B)
    (hunit : IsUnit M) : M.PosDef := by
  have hunit' : IsUnit (Bᴴ * B) := hgram ▸ hunit
  have hinjective : Function.Injective B.mulVec := by
    intro x y hxy
    apply (_root_.Matrix.mulVec_injective_iff_isUnit.mpr hunit')
    rw [← _root_.Matrix.mulVec_mulVec x Bᴴ B, ← _root_.Matrix.mulVec_mulVec y Bᴴ B, hxy]
  exact hgram.symm ▸ _root_.Matrix.PosDef.conjTranspose_mul_self B hinjective

/-- The determinant of the symmetrization `fun i j ↦ dᵢ Mᵢⱼ` of an integer matrix by a rational
vector. This is the ℤ-to-ℚ cast bridge of `Matrix.det_mul_column`, which does the row scaling, with
`Int.cast_det`, which returns the rational determinant of the cast matrix to the integral
determinant of `M`; the result is the shape in which Mathlib's determinants of the exceptional
Cartan matrices are used below. -/
private lemma det_mul_intCast {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℚ) (M : _root_.Matrix n n ℤ) :
    (_root_.Matrix.of fun i j ↦ d i * (M i j : ℚ)).det = (∏ i, d i) * (M.det : ℚ) := by
  have hmap : (_root_.Matrix.of fun i j ↦ d i * (M i j : ℚ))
      = _root_.Matrix.of fun i j ↦ d i * M.map (fun x : ℤ ↦ (x : ℚ)) i j := by
    ext i j
    simp
  rw [hmap, _root_.Matrix.det_mul_column, ← Int.cast_det]

private def rootsE : _root_.Matrix (Fin 8) (Fin 8) ℚ :=
  !![ 1 / 2,  1, -1,  0,  0,  0,  0,  0;
     -1 / 2,  1,  1, -1,  0,  0,  0,  0;
     -1 / 2,  0,  0,  1, -1,  0,  0,  0;
     -1 / 2,  0,  0,  0,  1, -1,  0,  0;
     -1 / 2,  0,  0,  0,  0,  1, -1,  0;
     -1 / 2,  0,  0,  0,  0,  0,  1, -1;
     -1 / 2,  0,  0,  0,  0,  0,  0,  1;
      1 / 2,  0,  0,  0,  0,  0,  0,  0]

private def rootsE6 : _root_.Matrix (Fin 8) (Fin 6) ℚ :=
  rootsE.submatrix id (Fin.castAdd 2)

/-- The standard Cartan matrix of type `E₆` is of finite type. -/
theorem isFiniteType_cartanMatrix_E6 : IsFiniteType E6.cartanMatrix := by
  refine isFiniteType_of (fun i ↦ cartanMatrix_apply_same E6 i)
    (fun i j hij ↦ cartanMatrix_apply_le_zero_of_ne E6 hij)
    (d := fun _ ↦ 1) (fun _ ↦ by positivity) ?_
  have hgram :
      _root_.Matrix.of (fun i j ↦ (1 : ℚ) * (CartanMatrix.E₆ i j : ℚ)) = rootsE6ᴴ * rootsE6 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rootsE6, rootsE, Fin.castAdd, Fin.castLE, CartanMatrix.E₆,
        _root_.Matrix.mul_apply, Fin.sum_univ_succ, _root_.Matrix.cons_val_succ]
  have hunit : IsUnit (_root_.Matrix.of fun i j ↦ (1 : ℚ) * (CartanMatrix.E₆ i j : ℚ)) := by
    rw [_root_.Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, det_mul_intCast,
      CartanMatrix.E₆_det]
    norm_num
  simp only [cartanMatrix_E6]
  exact posDef_of_gram _ _ hgram hunit

private def rootsE7 : _root_.Matrix (Fin 8) (Fin 7) ℚ :=
  rootsE.submatrix id (Fin.castAdd 1)

/-- The standard Cartan matrix of type `E₇` is of finite type. -/
theorem isFiniteType_cartanMatrix_E7 : IsFiniteType E7.cartanMatrix := by
  refine isFiniteType_of (fun i ↦ cartanMatrix_apply_same E7 i)
    (fun i j hij ↦ cartanMatrix_apply_le_zero_of_ne E7 hij)
    (d := fun _ ↦ 1) (fun _ ↦ by positivity) ?_
  have hgram :
      _root_.Matrix.of (fun i j ↦ (1 : ℚ) * (CartanMatrix.E₇ i j : ℚ)) = rootsE7ᴴ * rootsE7 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rootsE7, rootsE, Fin.castAdd, Fin.castLE, CartanMatrix.E₇,
        _root_.Matrix.mul_apply, Fin.sum_univ_succ, _root_.Matrix.cons_val_succ]
  have hunit : IsUnit (_root_.Matrix.of fun i j ↦ (1 : ℚ) * (CartanMatrix.E₇ i j : ℚ)) := by
    rw [_root_.Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, det_mul_intCast,
      CartanMatrix.E₇_det]
    norm_num
  simp only [cartanMatrix_E7]
  exact posDef_of_gram _ _ hgram hunit

/-- The standard Cartan matrix of type `E₈` is of finite type. -/
theorem isFiniteType_cartanMatrix_E8 : IsFiniteType E8.cartanMatrix := by
  refine isFiniteType_of (fun i ↦ cartanMatrix_apply_same E8 i)
    (fun i j hij ↦ cartanMatrix_apply_le_zero_of_ne E8 hij)
    (d := fun _ ↦ 1) (fun _ ↦ by positivity) ?_
  have hgram :
      _root_.Matrix.of (fun i j ↦ (1 : ℚ) * (CartanMatrix.E₈ i j : ℚ)) = rootsEᴴ * rootsE := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rootsE, CartanMatrix.E₈, _root_.Matrix.mul_apply, Fin.sum_univ_succ,
        _root_.Matrix.cons_val_succ]
  have hunit : IsUnit (_root_.Matrix.of fun i j ↦ (1 : ℚ) * (CartanMatrix.E₈ i j : ℚ)) := by
    rw [_root_.Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, det_mul_intCast,
      CartanMatrix.E₈_det]
    norm_num
  simp only [cartanMatrix_E8]
  exact posDef_of_gram _ _ hgram hunit

private def rootsF4 : _root_.Matrix (Fin 4) (Fin 4) ℚ :=
  !![ 1,  0,  0, -1;
     -1,  1,  0, -1;
      0, -1,  2, -1;
      0,  0,  0,  1]

/-- The standard Cartan matrix of type `F₄` is of finite type. -/
theorem isFiniteType_cartanMatrix_F4 : IsFiniteType F4.cartanMatrix := by
  let d : Fin 4 → ℚ := fun i ↦ if i.val < 2 then 1 else 2
  refine isFiniteType_of (fun i ↦ cartanMatrix_apply_same F4 i)
    (fun i j hij ↦ cartanMatrix_apply_le_zero_of_ne F4 hij)
    (d := d) (by intro i; dsimp only [d]; split <;> norm_num) ?_
  have hgram :
      _root_.Matrix.of (fun i j ↦ d i * (CartanMatrix.F₄ i j : ℚ)) = rootsF4ᴴ * rootsF4 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d, rootsF4, CartanMatrix.F₄, _root_.Matrix.mul_apply, Fin.sum_univ_succ,
        _root_.Matrix.cons_val_succ]
  have hunit : IsUnit (_root_.Matrix.of fun i j ↦ d i * (CartanMatrix.F₄ i j : ℚ)) := by
    rw [_root_.Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    rw [det_mul_intCast, CartanMatrix.F₄_det]
    norm_num [d, Fin.prod_univ_succ]
  simp only [cartanMatrix_F4]
  exact posDef_of_gram _ _ hgram hunit

private def rootsG2 : _root_.Matrix (Fin 3) (Fin 2) ℚ :=
  !![ 1, -1;
     -2,  1;
      1,  0]

/-- The standard Bourbaki-numbered Cartan matrix of type `G₂` is of finite type. -/
theorem isFiniteType_cartanMatrix_G2 : IsFiniteType G2.cartanMatrix := by
  let d : Fin 2 → ℚ := fun i ↦ if i = 0 then 3 else 1
  refine isFiniteType_of (fun i ↦ cartanMatrix_apply_same G2 i)
    (fun i j hij ↦ cartanMatrix_apply_le_zero_of_ne G2 hij)
    (d := d) (by intro i; dsimp only [d]; split <;> norm_num) ?_
  have hgram :
      _root_.Matrix.of (fun i j ↦ d i * (CartanMatrix.G₂ᵀ i j : ℚ)) = rootsG2ᴴ * rootsG2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [d, rootsG2, CartanMatrix.G₂, _root_.Matrix.mul_apply, Fin.sum_univ_succ,
        _root_.Matrix.cons_val_succ]
  have hunit : IsUnit (_root_.Matrix.of fun i j ↦ d i * (CartanMatrix.G₂ᵀ i j : ℚ)) := by
    rw [_root_.Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    rw [det_mul_intCast, _root_.Matrix.det_transpose, CartanMatrix.G₂_det]
    norm_num [d, Fin.prod_univ_succ]
  simp only [cartanMatrix_G2]
  exact posDef_of_gram _ _ hgram hunit

end TauCeti.DynkinType
