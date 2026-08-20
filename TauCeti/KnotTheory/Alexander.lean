/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# The Alexander polynomial of a Seifert matrix

A Seifert surface of a knot carries a bilinear linking form, and a basis of its first homology
turns that form into a square integer matrix `V`, the *Seifert matrix* of the surface. The
Alexander polynomial of the knot is read off `V` as the determinant of `t^(1/2) V - t^(-1/2) Vᵀ`.
This file builds that invariant and proves the identities that make it one: the symmetry
`Δ(t) = Δ(t⁻¹)`, the value `Δ(1) = det (V - Vᵀ)`, and invariance under the two moves generating
S-equivalence of Seifert matrices (congruence by a matrix of square determinant `1`, and the
enlargements that change the Seifert surface without changing the knot).

Half-integer powers are avoided by pulling `t^(-1/2)` out of every row: for a matrix of size
`2 * g` — the size of every Seifert matrix, `g` the genus of the surface — the determinant of
`t^(1/2) V - t^(-1/2) Vᵀ` is `T ^ (-g)` times the determinant of `alexanderMatrix V = T • V - Vᵀ`,
which lives in the Laurent polynomial ring `R[T;T⁻¹]` on the nose. That is the definition of
`alexander` below, with the genus read off the index type as `Fintype.card ι / 2`.

This is the *algebraic* half of the Alexander polynomial: the input is a matrix, not a knot.
Producing a Seifert matrix from a knot (a Seifert surface, a basis of its homology, and the
linking form) is separate work, as is the agreement of this route with the Conway skein relation
on a diagram and with the Burau representation of a braid word. What is fixed here is the
normalisation those routes must match, pinned by the trefoil and figure-eight computations at the
end of the file.

Everything is stated over an arbitrary commutative ring and an arbitrary index type; the
knot-theoretic case is `R = ℤ` and `ι = Fin (2 * g)`.

This is the Seifert-matrix route to the Alexander polynomial called for by Layer 4 (knot theory)
of the GeometricTopology roadmap.

## Main definitions

* `TauCeti.KnotTheory.alexanderMatrix`: the matrix `T • V - Vᵀ` over `R[T;T⁻¹]`.
* `TauCeti.KnotTheory.alexander`: the Conway-normalised Alexander polynomial
  `T ^ (-g) * det (T • V - Vᵀ)`, where `2 * g` is the size of `V`.
* `TauCeti.KnotTheory.enlargeColumn`, `TauCeti.KnotTheory.enlargeRow`: the two enlargements of a
  Seifert matrix, which together with congruence generate S-equivalence.

## Main results

* `TauCeti.KnotTheory.invert_alexander`: `Δ(t⁻¹) = Δ(t)` for a matrix of even size.
* `TauCeti.KnotTheory.alexander_conj_of_det_sq_eq_one`: `Δ` is unchanged by `V ↦ P * V * Pᵀ` when
  `det P ^ 2 = 1`, that is, by a change of basis of the homology of the Seifert surface.
* `TauCeti.KnotTheory.alexander_enlargeColumn`, `TauCeti.KnotTheory.alexander_enlargeRow`: `Δ` is
  unchanged by the enlargements. This is where the normalisation earns its keep: the unnormalised
  determinant is multiplied by `T`.
* `TauCeti.KnotTheory.eval₂_one_alexander`: `Δ(1) = det (V - Vᵀ)`, the determinant of the
  intersection form of the Seifert surface; for a knot it is `1`, so `Δ` is normalised so that
  the unknot has `Δ = 1` (`TauCeti.KnotTheory.alexander_of_isEmpty`).
* `TauCeti.KnotTheory.alexander_trefoilSeifertMatrix` and
  `TauCeti.KnotTheory.alexander_figureEightSeifertMatrix`: the classical values `t - 1 + t⁻¹` and
  `-t + 3 - t⁻¹`.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapters 6 and 8
  (Seifert matrices, S-equivalence, and the Conway-normalised Alexander polynomial).
* G. Burde, H. Zieschang, *Knots*, 2nd ed., de Gruyter (2003), Chapter 8.
-/

public section

open Matrix LaurentPolynomial

namespace TauCeti.KnotTheory

variable {R : Type*} [CommRing R] {ι : Type*}

/-- The Alexander matrix `T • V - Vᵀ` of a square matrix `V` over `R`, with entries in the ring
`R[T;T⁻¹]` of Laurent polynomials.

This is `t^(1/2)` times the classical matrix `t^(1/2) V - t^(-1/2) Vᵀ`, so for `V` of size `2 * g`
its determinant is `T ^ g` times the classical one; the normalisation is restored in
`TauCeti.KnotTheory.alexander`. -/
noncomputable def alexanderMatrix (V : Matrix ι ι R) : Matrix ι ι R[T;T⁻¹] :=
  (T 1 : R[T;T⁻¹]) • V.map C - (V.map C)ᵀ

/-- The entries of the Alexander matrix. -/
theorem alexanderMatrix_apply (V : Matrix ι ι R) (i j : ι) :
    alexanderMatrix V i j = T 1 * C (V i j) - C (V j i) := by
  simp [alexanderMatrix]

/-- Transposing the Alexander matrix transposes the underlying matrix. -/
theorem transpose_alexanderMatrix (V : Matrix ι ι R) :
    (alexanderMatrix V)ᵀ = alexanderMatrix Vᵀ := by
  ext i j
  simp [alexanderMatrix_apply, Matrix.transpose_apply]

/-- Substituting `T⁻¹` for `T` in the Alexander matrix transposes it and rescales it by `-T⁻¹`.
This is the matrix-level source of the symmetry of the Alexander polynomial. -/
theorem map_invert_alexanderMatrix (V : Matrix ι ι R) :
    (alexanderMatrix V).map invert = (-T (-1) : R[T;T⁻¹]) • (alexanderMatrix V)ᵀ := by
  have hT : (T (-1) : R[T;T⁻¹]) * T 1 = 1 := by rw [← T_add]; norm_num
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, alexanderMatrix_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul, map_sub, map_mul, invert_C, invert_T, mul_sub, neg_mul]
  rw [← mul_assoc, hT, one_mul]
  ring

/-- Evaluating the Alexander matrix at `T = 1` gives the intersection form `V - Vᵀ`. -/
theorem map_eval₂_one_alexanderMatrix (V : Matrix ι ι R) :
    (alexanderMatrix V).map (eval₂ (RingHom.id R) 1) = V - Vᵀ := by
  refine Matrix.ext fun i j => ?_
  simp [alexanderMatrix_apply, eval₂_C]

/-- The two extra columns of an enlargement: a chosen vector `ξ` in the first, zero in the
second. -/
def enlargeBlock (ξ : ι → R) : Matrix ι (Fin 2) R :=
  Matrix.of fun i => ![ξ i, 0]

/-- The first column of the enlargement block is `ξ`. -/
@[simp]
theorem enlargeBlock_apply_zero (ξ : ι → R) (i : ι) : enlargeBlock ξ i 0 = ξ i := by
  simp [enlargeBlock]

/-- The second column of the enlargement block vanishes. -/
@[simp]
theorem enlargeBlock_apply_one (ξ : ι → R) (i : ι) : enlargeBlock ξ i 1 = 0 := by
  simp [enlargeBlock]

/-- The column enlargement of a Seifert matrix by a vector `ξ`, the block matrix

```
⎛ V  ξ  0 ⎞
⎜ 0  0  1 ⎟
⎝ 0  0  0 ⎠
```

Adding a tube to a Seifert surface changes its Seifert matrix by this move (or by the transposed
move `TauCeti.KnotTheory.enlargeRow`) up to a change of basis, and the two enlargements together
with congruence are what generate S-equivalence of Seifert matrices. -/
def enlargeColumn (V : Matrix ι ι R) (ξ : ι → R) : Matrix (ι ⊕ Fin 2) (ι ⊕ Fin 2) R :=
  fromBlocks V (enlargeBlock ξ) 0 !![0, 1; 0, 0]

/-- The row enlargement of a Seifert matrix by a vector `η`, the transpose of the column
enlargement, that is the block matrix

```
⎛ V  0  0 ⎞
⎜ η  0  0 ⎟
⎝ 0  1  0 ⎠
```
-/
def enlargeRow (V : Matrix ι ι R) (η : ι → R) : Matrix (ι ⊕ Fin 2) (ι ⊕ Fin 2) R :=
  (enlargeColumn Vᵀ η)ᵀ

/-- The Alexander matrix of a column enlargement, in blocks. The bottom-right block is the only
new content: it is invertible with determinant `T`, which is where the extra factor of `T` in
`TauCeti.KnotTheory.det_alexanderMatrix_enlargeColumn` comes from. -/
theorem alexanderMatrix_enlargeColumn (V : Matrix ι ι R) (ξ : ι → R) :
    alexanderMatrix (enlargeColumn V ξ) =
      fromBlocks (alexanderMatrix V) ((T 1 : R[T;T⁻¹]) • (enlargeBlock ξ).map C)
        (-((enlargeBlock ξ).map C)ᵀ) !![0, T 1; -1, 0] := by
  refine Matrix.ext fun i j => ?_
  rcases i with i | i <;> rcases j with j | j
  · simp [enlargeColumn, alexanderMatrix_apply]
  · simp [enlargeColumn, alexanderMatrix_apply]
  · simp [enlargeColumn, alexanderMatrix_apply, Matrix.transpose_apply]
  · fin_cases i <;> fin_cases j <;> simp [enlargeColumn, alexanderMatrix_apply]

/-- Congruence of matrices is congruence of Alexander matrices. -/
theorem alexanderMatrix_conj [Fintype ι] (P V : Matrix ι ι R) :
    alexanderMatrix (P * V * Pᵀ) = P.map C * alexanderMatrix V * (P.map C)ᵀ := by
  simp [alexanderMatrix, Matrix.map_mul, Matrix.transpose_mul, mul_sub, sub_mul,
    Matrix.transpose_map, mul_assoc]

variable [Fintype ι] [DecidableEq ι]

/-- Transposing a matrix does not change its Alexander determinant. -/
theorem det_alexanderMatrix_transpose (V : Matrix ι ι R) :
    (alexanderMatrix Vᵀ).det = (alexanderMatrix V).det := by
  rw [← transpose_alexanderMatrix, Matrix.det_transpose]

/-- Substituting `T⁻¹` for `T` multiplies the unnormalised Alexander determinant by
`(-1) ^ n * T ^ (-n)`, where `n` is the size of the matrix. -/
theorem invert_det_alexanderMatrix (V : Matrix ι ι R) :
    invert ((alexanderMatrix V).det) =
      (-1 : R[T;T⁻¹]) ^ Fintype.card ι * T (-(Fintype.card ι : ℤ)) * (alexanderMatrix V).det := by
  rw [AlgEquiv.map_det, AlgEquiv.mapMatrix_apply, map_invert_alexanderMatrix, Matrix.det_smul,
    Matrix.det_transpose, neg_pow, T_pow, mul_neg_one, mul_assoc]

/-- Congruence multiplies the Alexander determinant by the square of the determinant of the
conjugating matrix. -/
theorem det_alexanderMatrix_conj (P V : Matrix ι ι R) :
    (alexanderMatrix (P * V * Pᵀ)).det = C P.det ^ 2 * (alexanderMatrix V).det := by
  rw [alexanderMatrix_conj, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  ring

/-- The Conway-normalised Alexander polynomial of a Seifert matrix `V`: the determinant of
`t^(1/2) V - t^(-1/2) Vᵀ`, written without half-integer powers as `T ^ (-g) * det (T • V - Vᵀ)`
for `V` of size `2 * g`.

A Seifert matrix always has even size, so `Fintype.card ι / 2` is the genus `g` of the underlying
Seifert surface; the results below that depend on the size being even take `Fintype.card ι = 2 * g`
as an explicit hypothesis. -/
noncomputable def alexander (V : Matrix ι ι R) : R[T;T⁻¹] :=
  T (-((Fintype.card ι / 2 : ℕ) : ℤ)) * (alexanderMatrix V).det

/-- The Alexander polynomial of a matrix of size `2 * g`, with the genus `g` named. -/
theorem alexander_eq_of_card {g : ℕ} (V : Matrix ι ι R) (h : Fintype.card ι = 2 * g) :
    alexander V = T (-(g : ℤ)) * (alexanderMatrix V).det := by
  rw [alexander, h]
  norm_num

/-- **The Alexander polynomial is symmetric**: `Δ(t⁻¹) = Δ(t)`. This is exactly what the
normalisation `T ^ (-g)` buys, and it needs the size of the Seifert matrix to be even. -/
theorem invert_alexander {g : ℕ} (V : Matrix ι ι R) (h : Fintype.card ι = 2 * g) :
    invert (alexander V) = alexander V := by
  have h1 : (-1 : R[T;T⁻¹]) ^ Fintype.card ι = 1 := by
    rw [h, pow_mul]
    norm_num
  rw [alexander_eq_of_card V h, map_mul, invert_T, invert_det_alexanderMatrix, h1, one_mul,
    ← mul_assoc, ← T_add, h, show - -(g : ℤ) + -((2 * g : ℕ) : ℤ) = -(g : ℤ) by push_cast; ring]

/-- Congruence multiplies the Alexander polynomial by the square of the determinant of the
conjugating matrix. -/
theorem alexander_conj (P V : Matrix ι ι R) :
    alexander (P * V * Pᵀ) = C P.det ^ 2 * alexander V := by
  rw [alexander, alexander, det_alexanderMatrix_conj]
  ring

/-- **The Alexander polynomial is a congruence invariant**: changing the basis of the first
homology of the Seifert surface leaves it unchanged. -/
theorem alexander_conj_of_det_sq_eq_one {P : Matrix ι ι R} (V : Matrix ι ι R)
    (hP : P.det ^ 2 = 1) : alexander (P * V * Pᵀ) = alexander V := by
  rw [alexander_conj, ← map_pow, hP, map_one, one_mul]

/-- Reversing the orientation of the Seifert surface transposes its Seifert matrix and leaves the
Alexander polynomial unchanged. -/
theorem alexander_transpose (V : Matrix ι ι R) : alexander Vᵀ = alexander V := by
  rw [alexander, alexander, det_alexanderMatrix_transpose]

/-- `Δ(1)` is the determinant of the intersection form `V - Vᵀ` of the Seifert surface. For a
knot that form is unimodular, so `Δ(1) = ±1`. -/
theorem eval₂_one_alexander (V : Matrix ι ι R) :
    eval₂ (RingHom.id R) 1 (alexander V) = (V - Vᵀ).det := by
  rw [alexander, map_mul, eval₂_T, RingHom.map_det, RingHom.mapMatrix_apply,
    map_eval₂_one_alexanderMatrix]
  simp

/-- The empty Seifert matrix, that of a disc, has Alexander polynomial `1`: the unknot is
normalised to `Δ = 1`. -/
@[simp]
theorem alexander_of_isEmpty [IsEmpty ι] (V : Matrix ι ι R) : alexander V = 1 := by
  simp [alexander]

/-- **The unnormalised Alexander determinant picks up exactly one factor of `T` under a column
enlargement.** -/
theorem det_alexanderMatrix_enlargeColumn (V : Matrix ι ι R) (ξ : ι → R) :
    (alexanderMatrix (enlargeColumn V ξ)).det = T 1 * (alexanderMatrix V).det := by
  set E : Matrix ι (Fin 2) R[T;T⁻¹] := (enlargeBlock ξ).map C with hE
  set D : Matrix (Fin 2) (Fin 2) R[T;T⁻¹] := !![0, T 1; -1, 0] with hD
  set X : Matrix ι (Fin 2) R[T;T⁻¹] := Matrix.of fun i => ![0, T 1 * C (ξ i)] with hX
  have hXE : X * (-Eᵀ) = 0 := by
    refine Matrix.ext fun i j => ?_
    simp only [hX, hE, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply,
      Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, enlargeBlock_apply_one, map_zero, Matrix.zero_apply,
      neg_zero, mul_zero, zero_mul, add_zero]
  have hXD : (T 1 : R[T;T⁻¹]) • E + X * D = 0 := by
    refine Matrix.ext fun i j => ?_
    fin_cases j <;>
      simp only [hX, hE, hD, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val',
        Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one,
        enlargeBlock_apply_zero, enlargeBlock_apply_one, map_zero, Matrix.zero_apply, mul_zero,
        zero_mul, add_zero, zero_add, mul_neg]
    all_goals ring
  have hone : (fromBlocks (1 : Matrix ι ι R[T;T⁻¹]) X 0 1).det = 1 := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, one_mul]
  have key : fromBlocks (1 : Matrix ι ι R[T;T⁻¹]) X 0 1 * alexanderMatrix (enlargeColumn V ξ)
      = fromBlocks (alexanderMatrix V) 0 (-Eᵀ) D := by
    rw [alexanderMatrix_enlargeColumn, fromBlocks_multiply, ← hE, ← hD]
    simp only [Matrix.one_mul, Matrix.zero_mul, zero_add, hXE, add_zero, hXD]
  calc (alexanderMatrix (enlargeColumn V ξ)).det
      = (fromBlocks (1 : Matrix ι ι R[T;T⁻¹]) X 0 1).det
        * (alexanderMatrix (enlargeColumn V ξ)).det := by rw [hone, one_mul]
    _ = (fromBlocks (1 : Matrix ι ι R[T;T⁻¹]) X 0 1
        * alexanderMatrix (enlargeColumn V ξ)).det := (Matrix.det_mul _ _).symm
    _ = (fromBlocks (alexanderMatrix V) 0 (-Eᵀ) D).det := by rw [key]
    _ = (alexanderMatrix V).det * D.det := Matrix.det_fromBlocks_zero₁₂ _ _ _
    _ = T 1 * (alexanderMatrix V).det := by rw [hD, Matrix.det_fin_two_of]; ring

/-- The unnormalised Alexander determinant picks up exactly one factor of `T` under a row
enlargement. -/
theorem det_alexanderMatrix_enlargeRow (V : Matrix ι ι R) (η : ι → R) :
    (alexanderMatrix (enlargeRow V η)).det = T 1 * (alexanderMatrix V).det := by
  rw [enlargeRow, det_alexanderMatrix_transpose, det_alexanderMatrix_enlargeColumn,
    det_alexanderMatrix_transpose]

/-- **The Alexander polynomial is unchanged by a column enlargement of the Seifert matrix.** The
extra factor of `T` in the determinant is exactly cancelled by the genus going up by one. -/
theorem alexander_enlargeColumn (V : Matrix ι ι R) (ξ : ι → R) :
    alexander (enlargeColumn V ξ) = alexander V := by
  have hcard : Fintype.card (ι ⊕ Fin 2) / 2 = Fintype.card ι / 2 + 1 := by
    simp [Fintype.card_sum]
  rw [alexander, alexander, det_alexanderMatrix_enlargeColumn, hcard, ← mul_assoc, ← T_add,
    show -((Fintype.card ι / 2 + 1 : ℕ) : ℤ) + 1 = -((Fintype.card ι / 2 : ℕ) : ℤ) by
      push_cast; ring]

/-- **The Alexander polynomial is unchanged by a row enlargement of the Seifert matrix.** -/
theorem alexander_enlargeRow (V : Matrix ι ι R) (η : ι → R) :
    alexander (enlargeRow V η) = alexander V := by
  rw [enlargeRow, alexander_transpose, alexander_enlargeColumn, alexander_transpose]

/-- The Seifert matrix of the right-handed trefoil, read off the standard genus-one Seifert
surface (Lickorish, *An Introduction to Knot Theory*, Chapter 6). -/
def trefoilSeifertMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 1; 0, -1]

/-- The Seifert matrix of the figure-eight knot, read off the standard genus-one Seifert
surface. -/
def figureEightSeifertMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, -1]

/-- The Alexander polynomial of the right-handed trefoil is `t - 1 + t⁻¹`. -/
theorem alexander_trefoilSeifertMatrix :
    alexander trefoilSeifertMatrix = T 1 - 1 + T (-1) := by
  have hT : (T (-1) : ℤ[T;T⁻¹]) * T 1 = 1 := by rw [← T_add]; norm_num
  rw [alexander_eq_of_card (g := 1) _ (by norm_num), Matrix.det_fin_two]
  simp only [Nat.cast_one, Int.reduceNeg, trefoilSeifertMatrix, Fin.isValue,
    alexanderMatrix_apply, of_apply, cons_val', cons_val_zero, cons_val_fin_one, eq_intCast,
    Int.cast_neg, Int.cast_one, mul_neg, mul_one, sub_neg_eq_add, cons_val_one, Int.cast_zero,
    sub_zero, mul_zero, zero_sub, T_mul]
  linear_combination (T 1 - 1 : ℤ[T;T⁻¹]) * hT

/-- The Alexander polynomial of the figure-eight knot is `-t + 3 - t⁻¹`. -/
theorem alexander_figureEightSeifertMatrix :
    alexander figureEightSeifertMatrix = -T 1 + 3 - T (-1) := by
  have hT : (T (-1) : ℤ[T;T⁻¹]) * T 1 = 1 := by rw [← T_add]; norm_num
  rw [alexander_eq_of_card (g := 1) _ (by norm_num), Matrix.det_fin_two]
  simp only [Nat.cast_one, Int.reduceNeg, figureEightSeifertMatrix, Fin.isValue,
    alexanderMatrix_apply, of_apply, cons_val', cons_val_zero, cons_val_fin_one, eq_intCast,
    Int.cast_one, mul_one, cons_val_one, Int.cast_neg, mul_neg, sub_neg_eq_add, Int.cast_zero,
    sub_zero, mul_zero, zero_sub, T_mul]
  linear_combination (3 - T 1 : ℤ[T;T⁻¹]) * hT

end TauCeti.KnotTheory
