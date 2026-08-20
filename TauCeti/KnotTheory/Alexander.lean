/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The Alexander polynomial of a Seifert matrix

A Seifert surface of a knot carries a bilinear linking form, and a basis of its first homology
turns that form into a square integer matrix `V`, the *Seifert matrix* of the surface. The
Alexander polynomial of the knot is read off `V` as the determinant of `t^(1/2) V - t^(-1/2) Vᵀ`.
This file builds that invariant and proves the identities that make it one: the symmetry
`Δ(t) = Δ(t⁻¹)`, the value `Δ(1) = det (V - Vᵀ)`, and invariance under the two moves generating
S-equivalence of Seifert matrices (congruence `V ↦ P * V * Pᵀ` by a matrix `P` whose determinant
squares to `1` — over `ℤ` this is precisely a change of basis of the homology — and the
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
* `TauCeti.KnotTheory.alexander_congruence_of_det_sq_eq_one`: `Δ` is unchanged by
  `V ↦ P * V * Pᵀ` whenever `det P ^ 2 = 1`. Over `ℤ` that is exactly the congruence by a change
  of basis of the first homology of the Seifert surface, since a change of basis of a free
  `ℤ`-module has determinant `±1`; over a general commutative ring an invertible `P` need only
  have unit determinant, and the hypothesis is a genuine restriction.
* `TauCeti.KnotTheory.alexander_enlargeColumn`, `TauCeti.KnotTheory.alexander_enlargeRow`: `Δ` is
  unchanged by the enlargements. This is where the normalisation earns its keep: the unnormalised
  determinant is multiplied by `T`.
* `TauCeti.KnotTheory.eval₂_one_alexander`: `Δ(1) = det (V - Vᵀ)`, the determinant of the
  intersection form of the Seifert surface; for a knot it is `1`, so `Δ` is normalised so that
  the unknot has `Δ = 1` (`TauCeti.KnotTheory.alexander_of_isEmpty`).
* `TauCeti.KnotTheory.alexander_fin_two`: the closed form of `Δ` for a genus-one (`2 × 2`)
  Seifert matrix, from which the two examples below are read off.
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
@[simp]
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

/-- The old block of a column enlargement is the original matrix. -/
@[simp]
theorem enlargeColumn_apply_inl_inl (V : Matrix ι ι R) (ξ : ι → R) (i j : ι) :
    enlargeColumn V ξ (Sum.inl i) (Sum.inl j) = V i j := by
  simp [enlargeColumn]

/-- The first new column of a column enlargement is `ξ`. -/
@[simp]
theorem enlargeColumn_apply_inl_inr_zero (V : Matrix ι ι R) (ξ : ι → R) (i : ι) :
    enlargeColumn V ξ (Sum.inl i) (Sum.inr 0) = ξ i := by
  simp [enlargeColumn]

/-- The second new column of a column enlargement vanishes on the old rows. -/
@[simp]
theorem enlargeColumn_apply_inl_inr_one (V : Matrix ι ι R) (ξ : ι → R) (i : ι) :
    enlargeColumn V ξ (Sum.inl i) (Sum.inr 1) = 0 := by
  simp [enlargeColumn]

/-- The new rows of a column enlargement vanish on the old columns. -/
@[simp]
theorem enlargeColumn_apply_inr_inl (V : Matrix ι ι R) (ξ : ι → R) (i : Fin 2) (j : ι) :
    enlargeColumn V ξ (Sum.inr i) (Sum.inl j) = 0 := by
  simp [enlargeColumn]

/-- The new `2 × 2` block of a column enlargement, at `(0, 0)`. -/
@[simp]
theorem enlargeColumn_apply_inr_zero_inr_zero (V : Matrix ι ι R) (ξ : ι → R) :
    enlargeColumn V ξ (Sum.inr 0) (Sum.inr 0) = 0 := by
  simp [enlargeColumn]

/-- The new `2 × 2` block of a column enlargement, at `(0, 1)`: the single new `1`. -/
@[simp]
theorem enlargeColumn_apply_inr_zero_inr_one (V : Matrix ι ι R) (ξ : ι → R) :
    enlargeColumn V ξ (Sum.inr 0) (Sum.inr 1) = 1 := by
  simp [enlargeColumn]

/-- The new `2 × 2` block of a column enlargement, at `(1, 0)`. -/
@[simp]
theorem enlargeColumn_apply_inr_one_inr_zero (V : Matrix ι ι R) (ξ : ι → R) :
    enlargeColumn V ξ (Sum.inr 1) (Sum.inr 0) = 0 := by
  simp [enlargeColumn]

/-- The new `2 × 2` block of a column enlargement, at `(1, 1)`. -/
@[simp]
theorem enlargeColumn_apply_inr_one_inr_one (V : Matrix ι ι R) (ξ : ι → R) :
    enlargeColumn V ξ (Sum.inr 1) (Sum.inr 1) = 0 := by
  simp [enlargeColumn]

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

/-- The old block of a row enlargement is the original matrix. -/
@[simp]
theorem enlargeRow_apply_inl_inl (V : Matrix ι ι R) (η : ι → R) (i j : ι) :
    enlargeRow V η (Sum.inl i) (Sum.inl j) = V i j := by
  simp [enlargeRow]

/-- The new columns of a row enlargement vanish on the old rows. -/
@[simp]
theorem enlargeRow_apply_inl_inr (V : Matrix ι ι R) (η : ι → R) (i : ι) (j : Fin 2) :
    enlargeRow V η (Sum.inl i) (Sum.inr j) = 0 := by
  simp [enlargeRow]

/-- The first new row of a row enlargement is `η`. -/
@[simp]
theorem enlargeRow_apply_inr_zero_inl (V : Matrix ι ι R) (η : ι → R) (j : ι) :
    enlargeRow V η (Sum.inr 0) (Sum.inl j) = η j := by
  simp [enlargeRow]

/-- The second new row of a row enlargement vanishes on the old columns. -/
@[simp]
theorem enlargeRow_apply_inr_one_inl (V : Matrix ι ι R) (η : ι → R) (j : ι) :
    enlargeRow V η (Sum.inr 1) (Sum.inl j) = 0 := by
  simp [enlargeRow]

/-- The new `2 × 2` block of a row enlargement, at `(0, 0)`. -/
@[simp]
theorem enlargeRow_apply_inr_zero_inr_zero (V : Matrix ι ι R) (η : ι → R) :
    enlargeRow V η (Sum.inr 0) (Sum.inr 0) = 0 := by
  simp [enlargeRow]

/-- The new `2 × 2` block of a row enlargement, at `(0, 1)`. -/
@[simp]
theorem enlargeRow_apply_inr_zero_inr_one (V : Matrix ι ι R) (η : ι → R) :
    enlargeRow V η (Sum.inr 0) (Sum.inr 1) = 0 := by
  simp [enlargeRow]

/-- The new `2 × 2` block of a row enlargement, at `(1, 0)`: the single new `1`. -/
@[simp]
theorem enlargeRow_apply_inr_one_inr_zero (V : Matrix ι ι R) (η : ι → R) :
    enlargeRow V η (Sum.inr 1) (Sum.inr 0) = 1 := by
  simp [enlargeRow]

/-- The new `2 × 2` block of a row enlargement, at `(1, 1)`. -/
@[simp]
theorem enlargeRow_apply_inr_one_inr_one (V : Matrix ι ι R) (η : ι → R) :
    enlargeRow V η (Sum.inr 1) (Sum.inr 1) = 0 := by
  simp [enlargeRow]

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
theorem alexanderMatrix_congruence [Fintype ι] (P V : Matrix ι ι R) :
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
congruence matrix. -/
theorem det_alexanderMatrix_congruence (P V : Matrix ι ι R) :
    (alexanderMatrix (P * V * Pᵀ)).det = C P.det ^ 2 * (alexanderMatrix V).det := by
  rw [alexanderMatrix_congruence, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
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
  have hexp : - -(g : ℤ) + -((2 * g : ℕ) : ℤ) = -(g : ℤ) := by push_cast; ring
  rw [alexander_eq_of_card V h, map_mul, invert_T, invert_det_alexanderMatrix, h1, one_mul,
    ← mul_assoc, ← T_add, h, hexp]

/-- Congruence multiplies the Alexander polynomial by the square of the determinant of the
congruence matrix. -/
theorem alexander_congruence (P V : Matrix ι ι R) :
    alexander (P * V * Pᵀ) = C P.det ^ 2 * alexander V := by
  rw [alexander, alexander, det_alexanderMatrix_congruence]
  ring

/-- **The Alexander polynomial is a congruence invariant** as soon as the determinant of the
congruence matrix squares to `1`: `alexander (P * V * Pᵀ) = alexander V`.

The hypothesis `P.det ^ 2 = 1` is not automatic for an invertible `P` over an arbitrary
commutative ring, where `P.det` need only be a unit; it is automatic in the knot-theoretic case
`R = ℤ`, where a change of basis of the first homology of the Seifert surface is a matrix in
`GL (2 * g) ℤ` and so has determinant `±1`. -/
theorem alexander_congruence_of_det_sq_eq_one {P : Matrix ι ι R} (V : Matrix ι ι R)
    (hP : P.det ^ 2 = 1) : alexander (P * V * Pᵀ) = alexander V := by
  rw [alexander_congruence, ← map_pow, hP, map_one, one_mul]

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
  have hexp : -((Fintype.card ι / 2 + 1 : ℕ) : ℤ) + 1 = -((Fintype.card ι / 2 : ℕ) : ℤ) := by
    push_cast; ring
  rw [alexander, alexander, det_alexanderMatrix_enlargeColumn, hcard, ← mul_assoc, ← T_add, hexp]

/-- **The Alexander polynomial is unchanged by a row enlargement of the Seifert matrix.** -/
theorem alexander_enlargeRow (V : Matrix ι ι R) (η : ι → R) :
    alexander (enlargeRow V η) = alexander V := by
  rw [enlargeRow, alexander_transpose, alexander_enlargeColumn, alexander_transpose]

/-- **The Alexander polynomial of a genus-one Seifert matrix**: for `V = !![a, b; c, d]`,

`Δ = (t - 2 + t⁻¹) * a * d - (t + t⁻¹) * b * c + b ^ 2 + c ^ 2`.

This is the closed form behind the trefoil and figure-eight computations below. -/
theorem alexander_fin_two (V : Matrix (Fin 2) (Fin 2) R) :
    alexander V = (T 1 - 2 + T (-1)) * C (V 0 0) * C (V 1 1)
      - (T 1 + T (-1)) * C (V 0 1) * C (V 1 0) + (C (V 0 1) ^ 2 + C (V 1 0) ^ 2) := by
  have hT : (T (-1) : R[T;T⁻¹]) * T 1 = 1 := by rw [← T_add]; norm_num
  rw [alexander_eq_of_card (g := 1) _ (by simp), Matrix.det_fin_two, alexanderMatrix_apply,
    alexanderMatrix_apply, alexanderMatrix_apply, alexanderMatrix_apply, Nat.cast_one]
  linear_combination (C (V 0 0) * C (V 1 1) * (T 1 - 2) - C (V 0 1) * C (V 1 0) * T 1
    + C (V 0 1) ^ 2 + C (V 1 0) ^ 2) * hT

/-- The Seifert matrix of the right-handed trefoil, read off the standard genus-one Seifert
surface (Lickorish, *An Introduction to Knot Theory*, Chapter 6). -/
def trefoilSeifertMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 1; 0, -1]

/-- The Seifert matrix of the figure-eight knot, read off the standard genus-one Seifert
surface. -/
def figureEightSeifertMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, -1]

/-- The Alexander polynomial of the right-handed trefoil is `t - 1 + t⁻¹`. -/
theorem alexander_trefoilSeifertMatrix :
    alexander trefoilSeifertMatrix = T 1 - 1 + T (-1) := by
  rw [alexander_fin_two]
  simp [trefoilSeifertMatrix]
  ring

/-- The Alexander polynomial of the figure-eight knot is `-t + 3 - t⁻¹`. -/
theorem alexander_figureEightSeifertMatrix :
    alexander figureEightSeifertMatrix = -T 1 + 3 - T (-1) := by
  rw [alexander_fin_two]
  simp [figureEightSeifertMatrix]
  ring

end TauCeti.KnotTheory
