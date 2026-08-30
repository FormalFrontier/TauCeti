/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import TauCeti.GroupTheory.SpecificGroups.Braid

/-!
# The Burau representation of the braid group

The braid group `TauCeti.BraidGroup n` acts on the first homology of the infinite cyclic cover of
the `n`-punctured disc relative to the fibre over a basepoint. This relative homology is free of
rank `n` over the ring of Laurent polynomials, and a choice of basis gives the *unreduced Burau
representation*. This file constructs it over an arbitrary commutative ring `R` and an arbitrary
unit `t : Rˣ`, so the Laurent-polynomial case is the instance `R = ℤ[T;T⁻¹]`, `t = T`. The absolute
first homology of the cover instead has rank `n - 1` and carries the reduced representation.

Concretely the elementary braid `σ i` is sent to the matrix that is the identity outside the two
strands it crosses and is
`!![1 - t, t; 1, 0]`
on them. The whole file is organised around the observation that this matrix differs from the
identity by a **rank-one** matrix,
`burauMatrix t i = 1 - vecMulVec (burauCol t i) (burauRow R i)`,
where `burauCol t i = t • e i - e (i + 1)` and `burauRow R i = e i - e (i + 1)`. Products of
rank-one matrices are governed by a single scalar, `vecMulVec u v * vecMulVec u' v' =
(v ⬝ᵥ u') • vecMulVec u v'`, so all four dot products between the rows and columns attached to two
elementary braids are computed once, and both defining braid relations, the inverse matrix, and the
determinant follow from them by pure module algebra. This is what keeps the verification of the
relations short: the braid relation reduces to `U * U = (t + 1) • U`,
`U * V * U = t • U` and their mirror images.

Two theorems keep the representation honest. `TauCeti.KnotTheory.det_burauMatrix` computes the
determinant of an elementary Burau matrix as `-t`, so the representation is by genuinely invertible
matrices and its determinant character is `(-t)` to the exponent sum;
`TauCeti.KnotTheory.coe_burau_one_eq_permMatrix` identifies the specialisation at `t = 1` with the
permutation representation `TauCeti.BraidGroup.permHom` of the strands, so the Burau representation
is a one-parameter deformation of the permutation representation. Over a nontrivial ring no
elementary Burau matrix is the identity (`TauCeti.KnotTheory.burauMatrix_ne_one`), so as soon as
`2 ≤ n` — that is, as soon as there is an elementary braid at all — the representation is not
trivial.

Finally there are two dual invariant vectors, unconditionally in `n` and `R`: the all-ones column
vector is fixed (`TauCeti.KnotTheory.burau_mulVec_one`), and the row vector
`(1, t, …, t ^ (n - 1))` is fixed (`TauCeti.KnotTheory.vecMul_burau_geom`). The kernel of the
latter covector is therefore an invariant submodule, and for `2 ≤ n` over a nontrivial ring it is
a proper nonzero one, which is the reducibility that the *reduced* Burau representation — the
restriction to that kernel — is carved out of. The restriction and an explicit basis of its kernel
are constructed in `TauCeti.KnotTheory.Burau.Reduced`; its comparison with the Seifert-matrix
Alexander polynomial of `TauCeti/KnotTheory/Alexander.lean` still needs the closure of a braid to
a link.

This is the Burau route of the "knot polynomials, each a project in itself, with several algorithms
apiece" bullet of Layer 4 ("knot theory, done properly") of the GeometricTopology roadmap.

## Main definitions

* `TauCeti.KnotTheory.burauCol` and `TauCeti.KnotTheory.burauRow`: the column and row vector whose
  outer product is the rank-one part of an elementary Burau matrix.
* `TauCeti.KnotTheory.burauMatrix`: the unreduced Burau matrix of an elementary braid.
* `TauCeti.KnotTheory.burauGL`: the same matrix as an element of the general linear group, with its
  inverse `1 - t⁻¹ • vecMulVec (burauCol t i) (burauRow R i)` named.
* `TauCeti.KnotTheory.burau`: the unreduced Burau representation `BraidGroup n →* GL (Fin n) R`.

## Main results

* `TauCeti.KnotTheory.burauMatrix_mul_comm` and `TauCeti.KnotTheory.burauMatrix_braid`: the two
  braid relations, verified for the elementary Burau matrices.
* `TauCeti.KnotTheory.det_burauMatrix` and `TauCeti.KnotTheory.det_burau`: the determinant of an
  elementary Burau matrix is `-t`, hence the determinant of the Burau matrix of a braid is `-t` to
  its exponent sum.
* `TauCeti.KnotTheory.burauMatrix_ne_one`: an elementary Burau matrix is never the identity.
* `TauCeti.KnotTheory.coe_burau_one_eq_permMatrix`: at `t = 1` the Burau representation is the
  permutation representation of the strands.
* `TauCeti.KnotTheory.burau_mulVec_one` and `TauCeti.KnotTheory.vecMul_burau_geom`: the invariant
  column vector `(1, …, 1)` and the invariant row vector `(1, t, …, t ^ (n - 1))`.

## References

* W. Burau, *Über Zopfgruppen und gleichsinnig verdrillte Verkettungen*, Abh. Math. Sem. Univ.
  Hamburg 11 (1935), 179-186.
* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82, Princeton
  University Press (1974), Chapter 3 (the Burau matrices and the reduced Burau representation).
-/

public section

open Matrix

namespace TauCeti.KnotTheory

variable {R : Type*} {n : ℕ}

section Ring

variable [Ring R]

/-! ### The rank-one part of an elementary Burau matrix -/

/-- The column vector `t • e i - e (i + 1)` indexed by the strands, where `i` and `i + 1` are the
two strands crossed by the elementary braid `TauCeti.BraidGroup.sigma i`. -/
def burauCol (t : R) (i : Fin (n - 1)) : Fin n → R :=
  Pi.single (BraidGroup.strand i) t - Pi.single (BraidGroup.strandSucc i) 1

/-- The row vector `e i - e (i + 1)` indexed by the strands, where `i` and `i + 1` are the two
strands crossed by the elementary braid `TauCeti.BraidGroup.sigma i`. -/
def burauRow (R : Type*) [Ring R] {n : ℕ} (i : Fin (n - 1)) : Fin n → R :=
  Pi.single (BraidGroup.strand i) 1 - Pi.single (BraidGroup.strandSucc i) 1

/-- The entries of the Burau column vector. -/
theorem burauCol_apply (t : R) (i : Fin (n - 1)) (k : Fin n) :
    burauCol t i k = (if k = BraidGroup.strand i then t else 0) -
      (if k = BraidGroup.strandSucc i then 1 else 0) := by
  simp [burauCol, Pi.single_apply]

/-- The entries of the Burau row vector. -/
theorem burauRow_apply (i : Fin (n - 1)) (k : Fin n) :
    burauRow R i k = (if k = BraidGroup.strand i then 1 else 0) -
      (if k = BraidGroup.strandSucc i then 1 else 0) := by
  simp [burauRow, Pi.single_apply]

@[simp]
private theorem burauCol_strand (t : R) (i : Fin (n - 1)) :
    burauCol t i (BraidGroup.strand i) = t := by
  simp [burauCol_apply, BraidGroup.strand_ne_strandSucc i]

@[simp]
private theorem burauCol_strandSucc (t : R) (i : Fin (n - 1)) :
    burauCol t i (BraidGroup.strandSucc i) = -1 := by
  simp [burauCol_apply, (BraidGroup.strand_ne_strandSucc i).symm]

@[simp]
private theorem burauRow_strand (i : Fin (n - 1)) :
    burauRow R i (BraidGroup.strand i) = 1 := by
  simp [burauRow_apply, BraidGroup.strand_ne_strandSucc i]

@[simp]
private theorem burauRow_strandSucc (i : Fin (n - 1)) :
    burauRow R i (BraidGroup.strandSucc i) = -1 := by
  simp [burauRow_apply, (BraidGroup.strand_ne_strandSucc i).symm]

private theorem burauCol_apply_of_ne (t : R) (i : Fin (n - 1)) {k : Fin n}
    (h : k ≠ BraidGroup.strand i) (h' : k ≠ BraidGroup.strandSucc i) : burauCol t i k = 0 := by
  simp [burauCol_apply, h, h']

private theorem burauRow_apply_of_ne (i : Fin (n - 1)) {k : Fin n}
    (h : k ≠ BraidGroup.strand i) (h' : k ≠ BraidGroup.strandSucc i) : burauRow R i k = 0 := by
  simp [burauRow_apply, h, h']

/-- Dotting the Burau row vector against any vector reads off the difference of its values at the
two crossed strands. -/
theorem burauRow_dotProduct (i : Fin (n - 1)) (w : Fin n → R) :
    burauRow R i ⬝ᵥ w = w (BraidGroup.strand i) - w (BraidGroup.strandSucc i) := by
  simp [burauRow, sub_dotProduct, single_dotProduct]

/-- Dotting any vector against the Burau column vector. -/
theorem dotProduct_burauCol (t : R) (i : Fin (n - 1)) (w : Fin n → R) :
    w ⬝ᵥ burauCol t i = w (BraidGroup.strand i) * t - w (BraidGroup.strandSucc i) := by
  simp [burauCol, dotProduct_sub, dotProduct_single]

/-- The row and column vectors of one and the same elementary braid pair to `t + 1`. -/
theorem burauRow_dotProduct_burauCol_self (t : R) (i : Fin (n - 1)) :
    burauRow R i ⬝ᵥ burauCol t i = t + 1 := by
  rw [burauRow_dotProduct, burauCol_strand, burauCol_strandSucc, sub_neg_eq_add]

/-- For two consecutive elementary braids the row of the first pairs with the column of the second
to `-t`. -/
theorem burauRow_dotProduct_burauCol_of_succ (t : R) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 1 = j) :
    burauRow R i ⬝ᵥ burauCol t j = -t := by
  have h₁ : BraidGroup.strand i ≠ BraidGroup.strand j := by
    rw [BraidGroup.strand_eq_strandSucc_of_succ h]
    exact BraidGroup.strand_ne_strandSucc i
  have h₂ := BraidGroup.strand_ne_strandSucc_of_succ h
  rw [burauRow_dotProduct, burauCol_apply_of_ne t j h₁ h₂,
    ← BraidGroup.strand_eq_strandSucc_of_succ h, burauCol_strand, zero_sub]

/-- For two consecutive elementary braids the row of the second pairs with the column of the first
to `-1`. -/
theorem burauRow_dotProduct_burauCol_of_succ_rev (t : R) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 1 = j) :
    burauRow R j ⬝ᵥ burauCol t i = -1 := by
  have hij : i ≠ j := by
    intro hij
    have := congrArg Fin.val hij
    omega
  have h₁ := (BraidGroup.strand_ne_strandSucc_of_succ h).symm
  have h₂ := (BraidGroup.strandSucc_ne_strandSucc hij).symm
  rw [burauRow_dotProduct, BraidGroup.strand_eq_strandSucc_of_succ h, burauCol_strandSucc,
    burauCol_apply_of_ne t i h₁ h₂, sub_zero]

/-- Two elementary braids that share no strand have orthogonal rows and columns. -/
theorem burauRow_dotProduct_burauCol_of_not_adjacent (t : R) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) : burauRow R i ⬝ᵥ burauCol t j = 0 := by
  have h₁ : BraidGroup.strand i ≠ BraidGroup.strand j := by
    simp only [ne_eq, Fin.ext_iff, BraidGroup.val_strand]
    omega
  have h₂ : BraidGroup.strand i ≠ BraidGroup.strandSucc j := by
    simp only [ne_eq, Fin.ext_iff, BraidGroup.val_strand, BraidGroup.val_strandSucc]
    omega
  have h₃ : BraidGroup.strandSucc i ≠ BraidGroup.strand j := by
    simp only [ne_eq, Fin.ext_iff, BraidGroup.val_strand, BraidGroup.val_strandSucc]
    omega
  have h₄ : BraidGroup.strandSucc i ≠ BraidGroup.strandSucc j := by
    simp only [ne_eq, Fin.ext_iff, BraidGroup.val_strandSucc]
    omega
  rw [burauRow_dotProduct, burauCol_apply_of_ne t j h₁ h₂,
    burauCol_apply_of_ne t j h₃ h₄, sub_self]

/-! ### The elementary Burau matrices -/

/-- The unreduced Burau matrix of the elementary braid `TauCeti.BraidGroup.sigma i` at the
parameter `t`: the identity outside the two strands crossed by `sigma i`, and `!![1 - t, t; 1, 0]`
on them. -/
def burauMatrix (t : R) (i : Fin (n - 1)) : Matrix (Fin n) (Fin n) R :=
  1 - vecMulVec (burauCol t i) (burauRow R i)

/-- The defining formula for an elementary Burau matrix: it differs from the identity by the
rank-one matrix `vecMulVec (burauCol t i) (burauRow R i)`. -/
theorem burauMatrix_def (t : R) (i : Fin (n - 1)) :
    burauMatrix t i = 1 - vecMulVec (burauCol t i) (burauRow R i) := by
  rw [burauMatrix]

/-- The entries of an elementary Burau matrix. -/
theorem burauMatrix_apply (t : R) (i : Fin (n - 1)) (a b : Fin n) :
    burauMatrix t i a b = (if a = b then 1 else 0) - burauCol t i a * burauRow R i b := by
  rw [burauMatrix_def, Matrix.sub_apply, vecMulVec_apply, Matrix.one_apply]

/-- The upper left entry of the nontrivial two-by-two block of an elementary Burau matrix. -/
@[simp]
theorem burauMatrix_apply_strand_strand (t : R) (i : Fin (n - 1)) :
    burauMatrix t i (BraidGroup.strand i) (BraidGroup.strand i) = 1 - t := by
  rw [burauMatrix_apply, burauCol_strand, burauRow_strand]
  simp

/-- The upper right entry of the nontrivial two-by-two block of an elementary Burau matrix. -/
@[simp]
theorem burauMatrix_apply_strand_strandSucc (t : R) (i : Fin (n - 1)) :
    burauMatrix t i (BraidGroup.strand i) (BraidGroup.strandSucc i) = t := by
  rw [burauMatrix_apply, burauCol_strand, burauRow_strandSucc]
  simp [BraidGroup.strand_ne_strandSucc]

/-- The lower left entry of the nontrivial two-by-two block of an elementary Burau matrix. -/
@[simp]
theorem burauMatrix_apply_strandSucc_strand (t : R) (i : Fin (n - 1)) :
    burauMatrix t i (BraidGroup.strandSucc i) (BraidGroup.strand i) = 1 := by
  rw [burauMatrix_apply, burauCol_strandSucc, burauRow_strand]
  simp [(BraidGroup.strand_ne_strandSucc i).symm]

/-- The lower right entry of the nontrivial two-by-two block of an elementary Burau matrix. -/
@[simp]
theorem burauMatrix_apply_strandSucc_strandSucc (t : R) (i : Fin (n - 1)) :
    burauMatrix t i (BraidGroup.strandSucc i) (BraidGroup.strandSucc i) = 0 := by
  rw [burauMatrix_apply, burauCol_strandSucc, burauRow_strandSucc]
  simp

/-- Away from the two crossed strands the Burau matrix has the rows of the identity. -/
theorem burauMatrix_apply_of_ne (t : R) (i : Fin (n - 1)) {a : Fin n}
    (h : a ≠ BraidGroup.strand i) (h' : a ≠ BraidGroup.strandSucc i) (b : Fin n) :
    burauMatrix t i a b = if a = b then 1 else 0 := by
  rw [burauMatrix_apply, burauCol_apply]
  simp [h, h']

/-- An elementary Burau matrix is never the identity: the entry at which the two crossed strands
meet is `1` rather than `0`. Since an `i : Fin (n - 1)` exists exactly when `2 ≤ n`, this says that
the Burau representation is nontrivial for `2 ≤ n` over a nontrivial ring. -/
theorem burauMatrix_ne_one [Nontrivial R] (t : R) (i : Fin (n - 1)) : burauMatrix t i ≠ 1 := by
  intro h
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) R =>
    M (BraidGroup.strandSucc i) (BraidGroup.strand i)) h
  rw [burauMatrix_apply_strandSucc_strand,
    Matrix.one_apply_ne (BraidGroup.strand_ne_strandSucc i).symm] at hentry
  exact one_ne_zero hentry

/-- At `t = 1` an elementary Burau matrix is the permutation matrix of the transposition of the two
crossed strands. -/
theorem burauMatrix_one_eq_permMatrix (i : Fin (n - 1)) :
    burauMatrix (1 : R) i = (BraidGroup.transposition i).permMatrix R := by
  refine Matrix.ext fun a b => ?_
  have hrhs : (BraidGroup.transposition i).permMatrix R a b =
      if BraidGroup.transposition i a = b then 1 else 0 := by
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  rw [hrhs, BraidGroup.transposition_eq_swap]
  rcases eq_or_ne a (BraidGroup.strand i) with rfl | ha
  · rw [Equiv.swap_apply_left]
    rcases eq_or_ne b (BraidGroup.strand i) with rfl | hb
    · rw [burauMatrix_apply_strand_strand]
      simp [(BraidGroup.strand_ne_strandSucc i).symm]
    · rcases eq_or_ne b (BraidGroup.strandSucc i) with rfl | hb'
      · rw [burauMatrix_apply_strand_strandSucc]
        simp
      · rw [burauMatrix_apply, burauCol_strand, burauRow_apply_of_ne i hb hb']
        simp [hb.symm, hb'.symm]
  · rcases eq_or_ne a (BraidGroup.strandSucc i) with rfl | ha'
    · rw [Equiv.swap_apply_right]
      rcases eq_or_ne b (BraidGroup.strand i) with rfl | hb
      · rw [burauMatrix_apply_strandSucc_strand]
        simp
      · rcases eq_or_ne b (BraidGroup.strandSucc i) with rfl | hb'
        · rw [burauMatrix_apply_strandSucc_strandSucc]
          simp [BraidGroup.strand_ne_strandSucc]
        · rw [burauMatrix_apply, burauCol_strandSucc, burauRow_apply_of_ne i hb hb']
          simp [hb.symm, hb'.symm]
    · rw [Equiv.swap_apply_of_ne_of_ne ha ha']
      rw [burauMatrix_apply_of_ne (1 : R) i ha ha']

/-- The action of an elementary Burau matrix on a row vector, in rank-one form. -/
theorem vecMul_burauMatrix (t : R) (i : Fin (n - 1)) (w : Fin n → R) :
    w ᵥ* burauMatrix t i = w - (w ⬝ᵥ burauCol t i) • burauRow R i := by
  rw [burauMatrix_def, Matrix.vecMul_sub, Matrix.vecMul_one, vecMul_vecMulVec]

/-- The all-ones column vector is fixed by every elementary Burau matrix. -/
@[simp]
theorem burauMatrix_mulVec_one (t : R) (i : Fin (n - 1)) :
    burauMatrix t i *ᵥ (1 : Fin n → R) = 1 := by
  rw [burauMatrix_def, Matrix.sub_mulVec, Matrix.one_mulVec, vecMulVec_mulVec,
    burauRow_dotProduct]
  simp only [Pi.one_apply, sub_self]
  simp

/-- The geometric row vector `(1, t, …, t ^ (n - 1))` annihilates every Burau column. -/
theorem geom_dotProduct_burauCol_eq_zero (t : R) (i : Fin (n - 1)) :
    (fun k : Fin n => t ^ (k : ℕ)) ⬝ᵥ burauCol t i = 0 := by
  rw [dotProduct_burauCol, BraidGroup.val_strand, BraidGroup.val_strandSucc, pow_succ, sub_self]

/-- The geometric row vector `(1, t, …, t ^ (n - 1))` is fixed by every elementary Burau matrix. -/
@[simp]
theorem vecMul_burauMatrix_geom (t : R) (i : Fin (n - 1)) :
    (fun k : Fin n => t ^ (k : ℕ)) ᵥ* burauMatrix t i = fun k : Fin n => t ^ (k : ℕ) := by
  rw [vecMul_burauMatrix, geom_dotProduct_burauCol_eq_zero, zero_smul, sub_zero]

end Ring

section CommRing

variable [CommRing R]

/-- Multiplying two elementary Burau matrices: the two rank-one parts survive, and their product
contributes a single further rank-one matrix. -/
private theorem burauMatrix_mul_burauMatrix (t : R) (i j : Fin (n - 1)) :
    burauMatrix t i * burauMatrix t j =
      1 - vecMulVec (burauCol t i) (burauRow R i) - vecMulVec (burauCol t j) (burauRow R j) +
        (burauRow R i ⬝ᵥ burauCol t j) • vecMulVec (burauCol t i) (burauRow R j) := by
  simp only [burauMatrix_def, sub_mul, mul_sub, one_mul, mul_one, vecMulVec_mul_vecMulVec,
    vecMulVec_smul]
  abel

/-- **The distant commutation relation** for the elementary Burau matrices. -/
theorem burauMatrix_mul_comm (t : R) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    burauMatrix t i * burauMatrix t j = burauMatrix t j * burauMatrix t i := by
  rw [burauMatrix_mul_burauMatrix, burauMatrix_mul_burauMatrix,
    burauRow_dotProduct_burauCol_of_not_adjacent t h,
    burauRow_dotProduct_burauCol_of_not_adjacent t h.symm]
  simp only [zero_smul, add_zero]
  abel

/-- The braid relation for two consecutive elementary Burau matrices, in the asymmetric form from
which the symmetric statement `TauCeti.KnotTheory.burauMatrix_braid` follows. -/
private theorem burauMatrix_braid_of_succ (t : R) {i j : Fin (n - 1)} (h : (i : ℕ) + 1 = j) :
    burauMatrix t i * burauMatrix t j * burauMatrix t i =
      burauMatrix t j * burauMatrix t i * burauMatrix t j := by
  have hii := burauRow_dotProduct_burauCol_self (R := R) t i
  have hjj := burauRow_dotProduct_burauCol_self (R := R) t j
  have hij := burauRow_dotProduct_burauCol_of_succ (R := R) t h
  have hji := burauRow_dotProduct_burauCol_of_succ_rev (R := R) t h
  simp only [burauMatrix_def, sub_mul, mul_sub, one_mul, mul_one, vecMulVec_mul_vecMulVec,
    vecMulVec_smul, smul_mul_assoc, smul_smul, hii, hjj, hij, hji]
  module

/-- **The braid relation** for the elementary Burau matrices. -/
theorem burauMatrix_braid (t : R) {i j : Fin (n - 1)} (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    burauMatrix t i * burauMatrix t j * burauMatrix t i =
      burauMatrix t j * burauMatrix t i * burauMatrix t j := by
  rcases h with h | h
  · exact burauMatrix_braid_of_succ t h
  · exact (burauMatrix_braid_of_succ t h).symm

/-- The inverse of an elementary Burau matrix is
`1 - t⁻¹ • vecMulVec (burauCol t i) (burauRow R i)`. This is the witness that builds
`TauCeti.KnotTheory.burauGL`; the public statement of the inverse is
`TauCeti.KnotTheory.inv_burauMatrix`. -/
private theorem burauMatrix_mul_inv (t : Rˣ) (i : Fin (n - 1)) :
    burauMatrix (t : R) i *
      (1 - ((t⁻¹ : Rˣ) : R) • vecMulVec (burauCol (t : R) i) (burauRow R i)) = 1 := by
  have hb : vecMulVec (burauCol (t : R) i) (burauRow R i) *
      vecMulVec (burauCol (t : R) i) (burauRow R i) =
      ((t : R) + 1) • vecMulVec (burauCol (t : R) i) (burauRow R i) := by
    rw [vecMulVec_mul_vecMulVec, burauRow_dotProduct_burauCol_self, vecMulVec_smul]
  have hc : ((t⁻¹ : Rˣ) : R) * ((t : R) + 1) = 1 + ((t⁻¹ : Rˣ) : R) := by
    rw [mul_add, mul_one, Units.inv_mul]
  simp only [burauMatrix_def, sub_mul, mul_sub, one_mul, mul_one, mul_smul_comm, hb, smul_sub]
  rw [smul_smul, hc, add_smul, one_smul]
  abel

/-- The other side of `burauMatrix_mul_inv`. -/
private theorem burauMatrix_inv_mul (t : Rˣ) (i : Fin (n - 1)) :
    (1 - ((t⁻¹ : Rˣ) : R) • vecMulVec (burauCol (t : R) i) (burauRow R i)) *
      burauMatrix (t : R) i = 1 :=
  mul_eq_one_comm.mp (burauMatrix_mul_inv t i)

/-- The determinant of an elementary Burau matrix is `-t`. -/
@[simp]
theorem det_burauMatrix (t : R) (i : Fin (n - 1)) : (burauMatrix t i).det = -t := by
  rw [burauMatrix_def, sub_eq_add_neg, ← neg_vecMulVec, vecMulVec_eq Unit,
    det_one_add_replicateCol_mul_replicateRow, dotProduct_neg,
    burauRow_dotProduct_burauCol_self]
  ring

/-! ### The Burau representation -/

/-- An elementary Burau matrix as an element of the general linear group: its underlying matrix is
`TauCeti.KnotTheory.burauMatrix t i`, with inverse
`1 - t⁻¹ • vecMulVec (burauCol t i) (burauRow R i)`. -/
def burauGL (t : Rˣ) (i : Fin (n - 1)) : GL (Fin n) R where
  val := burauMatrix (t : R) i
  inv := 1 - ((t⁻¹ : Rˣ) : R) • vecMulVec (burauCol (t : R) i) (burauRow R i)
  val_inv := burauMatrix_mul_inv t i
  inv_val := burauMatrix_inv_mul t i

/-- The matrix underlying `TauCeti.KnotTheory.burauGL`. -/
@[simp]
theorem coe_burauGL (t : Rˣ) (i : Fin (n - 1)) :
    (burauGL t i : Matrix (Fin n) (Fin n) R) = burauMatrix (t : R) i :=
  (rfl)

/-- The nonsingular inverse of an elementary Burau matrix. -/
@[simp]
theorem inv_burauMatrix (t : Rˣ) (i : Fin (n - 1)) :
    (burauMatrix (t : R) i)⁻¹ =
      1 - ((t⁻¹ : Rˣ) : R) • vecMulVec (burauCol (t : R) i) (burauRow R i) :=
  Matrix.inv_eq_right_inv (burauMatrix_mul_inv t i)

/-- **The unreduced Burau representation** of the braid group on `n` strands at a unit `t`, sending
the elementary braid `sigma i` to `TauCeti.KnotTheory.burauGL t i`. -/
def burau (n : ℕ) (t : Rˣ) : BraidGroup n →* GL (Fin n) R :=
  BraidGroup.lift (burauGL t) (fun h => Units.ext (burauMatrix_mul_comm _ h))
    (fun h => Units.ext (burauMatrix_braid _ h))

/-- The Burau representation takes an elementary braid to the elementary Burau matrix. -/
@[simp]
theorem burau_sigma (t : Rˣ) (i : Fin (n - 1)) :
    burau n t (BraidGroup.sigma i) = (burauGL t i : GL (Fin n) R) :=
  BraidGroup.lift_sigma _ _ _ i

/-- The determinant of the Burau matrix of a braid is `-t` raised to its exponent sum. -/
theorem det_burau (t : Rˣ) (b : BraidGroup n) :
    Matrix.GeneralLinearGroup.det (burau n t b : GL (Fin n) R) =
      (-t) ^ Multiplicative.toAdd (ArtinGroup.exponentSum (CoxeterMatrix.A (n - 1)) b) := by
  have key : (Matrix.GeneralLinearGroup.det (n := Fin n) (R := R)).comp (burau n t) =
      (zpowersHom Rˣ (-t)).comp (ArtinGroup.exponentSum (CoxeterMatrix.A (n - 1))) := by
    refine BraidGroup.hom_ext fun i => ?_
    apply Units.ext
    simp [det_burauMatrix]
  exact congrArg (fun f : BraidGroup n →* Rˣ => f b) key

/-! ### The permutation representation as the specialisation at `t = 1` -/

/-- **The Burau representation at `t = 1` is the permutation representation of the strands.** Note
that `TauCeti.BraidGroup.permHom` is a homomorphism while `Equiv.Perm.permMatrix` is an
antihomomorphism, so the comparison is with `Matrix.permMatrixHom`, which inverts before taking the
permutation matrix. -/
theorem burau_one_eq_permMatrixHom_comp (n : ℕ) :
    (burau n (1 : Rˣ) : BraidGroup n →* GL (Fin n) R) =
      (Matrix.permMatrixHom (R := R)).toHomUnits.comp (BraidGroup.permHom n) := by
  refine BraidGroup.hom_ext fun i => ?_
  have hinv : (BraidGroup.transposition i)⁻¹ = BraidGroup.transposition i := by
    rw [BraidGroup.transposition_eq_swap, Equiv.swap_inv]
  refine Units.ext ?_
  simp only [burau_sigma, coe_burauGL, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.coe_toHomUnits, BraidGroup.permHom_sigma, Matrix.permMatrixHom_apply, hinv,
    Units.val_one]
  simpa using burauMatrix_one_eq_permMatrix (R := R) i

/-- At `t = 1` the Burau matrix of a braid is the permutation matrix of the underlying permutation
of the strands. -/
theorem coe_burau_one_eq_permMatrix (b : BraidGroup n) :
    (burau n (1 : Rˣ) b : Matrix (Fin n) (Fin n) R) =
      Matrix.permMatrixHom (BraidGroup.permHom n b) := by
  rw [burau_one_eq_permMatrixHom_comp]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_toHomUnits]

/-! ### Reducibility: the invariant vector and covector -/

/-- The action of an elementary Burau matrix on a column vector, in rank-one form. -/
theorem burauMatrix_mulVec (t : R) (i : Fin (n - 1)) (v : Fin n → R) :
    burauMatrix t i *ᵥ v = v - (burauRow R i ⬝ᵥ v) • burauCol t i := by
  rw [burauMatrix_def, Matrix.sub_mulVec, Matrix.one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

/-- A column vector fixed by every elementary Burau matrix is fixed by the whole representation. -/
theorem burau_mulVec_of_forall {t : Rˣ} {v : Fin n → R}
    (h : ∀ i : Fin (n - 1), burauMatrix (t : R) i *ᵥ v = v) (b : BraidGroup n) :
    (burau n t b : Matrix (Fin n) (Fin n) R) *ᵥ v = v := by
  refine BraidGroup.sigma_induction_on
    (p := fun b => (burau n t b : Matrix (Fin n) (Fin n) R) *ᵥ v = v) b
    (fun i => by simp only [burau_sigma, coe_burauGL]; exact h i) ?_ ?_ ?_
  · rw [map_one, Units.val_one, Matrix.one_mulVec]
  · intro b b' hb hb'
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hb', hb]
  · intro b hb
    have hmul : ((burau n t b⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ
        ((burau n t b : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ v = v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
        Units.val_one, Matrix.one_mulVec]
    rwa [hb] at hmul

/-- A row vector fixed by every elementary Burau matrix is fixed by the whole representation. -/
theorem vecMul_burau_of_forall {t : Rˣ} {w : Fin n → R}
    (h : ∀ i : Fin (n - 1), w ᵥ* burauMatrix (t : R) i = w) (b : BraidGroup n) :
    w ᵥ* (burau n t b : Matrix (Fin n) (Fin n) R) = w := by
  refine BraidGroup.sigma_induction_on
    (p := fun b => w ᵥ* (burau n t b : Matrix (Fin n) (Fin n) R) = w) b
    (fun i => by simp only [burau_sigma, coe_burauGL]; exact h i) ?_ ?_ ?_
  · rw [map_one, Units.val_one, Matrix.vecMul_one]
  · intro b b' hb hb'
    rw [map_mul, Units.val_mul, ← Matrix.vecMul_vecMul, hb, hb']
  · intro b hb
    have hmul : w ᵥ* ((burau n t b : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) ᵥ*
        ((burau n t b⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = w := by
      rw [Matrix.vecMul_vecMul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
        Units.val_one, Matrix.vecMul_one]
    rwa [hb] at hmul

/-- A matrix intertwining every elementary Burau matrix with the corresponding value of a
representation `ρ` intertwines the whole Burau representation with `ρ`. -/
theorem burau_mul_of_forall {β : Type*} [Fintype β] [DecidableEq β] {t : Rˣ}
    {C : Matrix (Fin n) β R} {ρ : BraidGroup n →* GL β R}
    (h : ∀ i : Fin (n - 1),
      burauMatrix (t : R) i * C = C * (ρ (BraidGroup.sigma i) : Matrix β β R))
    (b : BraidGroup n) :
    (burau n t b : Matrix (Fin n) (Fin n) R) * C = C * (ρ b : Matrix β β R) := by
  refine BraidGroup.sigma_induction_on
    (p := fun b => (burau n t b : Matrix (Fin n) (Fin n) R) * C = C * (ρ b : Matrix β β R)) b
    (fun i => by simp only [burau_sigma, coe_burauGL]; exact h i) ?_ ?_ ?_
  · rw [map_one, map_one, Units.val_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  · intro b b' hb hb'
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, hb', ← Matrix.mul_assoc,
      hb, Matrix.mul_assoc]
  · intro b hb
    have hM : ((burau n t b⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *
        ((burau n t b : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 := by
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    have hρ : ((ρ b : GL β R) : Matrix β β R) * ((ρ b⁻¹ : GL β R) : Matrix β β R) = 1 := by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    calc ((burau n t b⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * C
        = ((burau n t b⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *
            (C * ((ρ b : GL β R) : Matrix β β R)) * ((ρ b⁻¹ : GL β R) : Matrix β β R) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hρ, Matrix.mul_one]
      _ = ((burau n t b⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *
            (((burau n t b : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * C) *
            ((ρ b⁻¹ : GL β R) : Matrix β β R) := by rw [hb]
      _ = C * ((ρ b⁻¹ : GL β R) : Matrix β β R) := by
          rw [← Matrix.mul_assoc, hM, Matrix.one_mul]

/-- **The all-ones column vector is fixed by the Burau representation.** The line it spans is
therefore an invariant submodule; for `2 ≤ n` over a nontrivial ring it is a proper nonzero one,
so the unreduced Burau representation is reducible. -/
@[simp]
theorem burau_mulVec_one (t : Rˣ) (b : BraidGroup n) :
    (burau n t b : Matrix (Fin n) (Fin n) R) *ᵥ (1 : Fin n → R) = 1 :=
  burau_mulVec_of_forall (fun i => burauMatrix_mulVec_one (t : R) i) b

/-- **The geometric row vector `(1, t, …, t ^ (n - 1))` is fixed by the Burau representation.** Its
kernel is therefore an invariant submodule — for `2 ≤ n` over a nontrivial ring a proper nonzero
one — and it is what carries the reduced Burau representation. -/
@[simp]
theorem vecMul_burau_geom (t : Rˣ) (b : BraidGroup n) :
    (fun k : Fin n => (t : R) ^ (k : ℕ)) ᵥ* (burau n t b : Matrix (Fin n) (Fin n) R) =
      fun k : Fin n => (t : R) ^ (k : ℕ) :=
  vecMul_burau_of_forall (fun i => vecMul_burauMatrix_geom (t : R) i) b

end CommRing

end TauCeti.KnotTheory
