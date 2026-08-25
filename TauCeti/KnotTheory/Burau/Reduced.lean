/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Burau.Basic

/-!
# The reduced Burau representation of the braid group

The unreduced Burau representation of `TauCeti.KnotTheory.burau` is reducible: the row vector
`(1, t, …, t ^ (n - 1))` is fixed by it, so its kernel — a hyperplane in the free module of rank
`n` on the strands — is an invariant submodule. The *reduced Burau representation* is the
action on the free rank-`(n - 1)` submodule of that hyperplane spanned by the Burau columns. It is
the representation that computes the Alexander polynomial of a braid closure, and the one that is
faithful for `n ≤ 3`, unfaithful for `n ≥ 5`, and of unknown faithfulness for `n = 4`.

The submodule comes with a basis already in hand. The `n - 1` Burau columns
`burauCol t i = t • e i - e (i + 1)` are annihilated by the invariant covector
(`TauCeti.KnotTheory.geom_vecMul_burauColMatrix`) and are linearly independent: this file
assembles them into the `n × (n - 1)` matrix `TauCeti.KnotTheory.burauColMatrix` and exhibits an
explicit left inverse for it, `TauCeti.KnotTheory.burauColMatrixLeftInv`, whose `(i, a)` entry is
`-t ^ (a - i - 1)` for `i < a` and `0` otherwise. A left inverse is all that is needed: it makes
`burauColMatrix t` left cancellable, and cancellation is what transports every relation from the
unreduced matrices to the reduced ones.

That transport is the organising idea of the file. Write `C` for `burauColMatrix t`. The
**intertwining relation** `TauCeti.KnotTheory.burauMatrix_mul_burauColMatrix`,

`burauMatrix t j * C = C * reducedBurauMatrix t j`,

says exactly that `reducedBurauMatrix t j` is the matrix of the unreduced action of `sigma j` read
in the basis of Burau columns. Every relation among the reduced matrices — distant commutation,
the braid relation, invertibility — is then obtained by multiplying the corresponding unreduced
relation by `C` on the right and cancelling `C` on the left, so no rank-one matrix algebra is
redone here.

The reduced matrix is again an elementary rank-one update of the identity,
`reducedBurauMatrix t j = 1 - vecMulVec (Pi.single j 1) (reducedBurauRow t j)`, but now the rank-one
part is supported in the single row `j`, and the row vector is
`reducedBurauRow t j i = burauRow R j ⬝ᵥ burauCol t i`, the pairing of the `j`-th Burau row with
the `i`-th Burau column. The four values of that pairing are already available from the unreduced
file, so the closed form `TauCeti.KnotTheory.reducedBurauRow_apply` costs nothing: the row is
`(t + 1)` at `j`, `-1` at `j - 1`, `-t` at `j + 1`, and `0` elsewhere. Concretely
`reducedBurauMatrix t j` is the identity outside its `j`-th row, whose entries are `1` at `j - 1`,
`-t` at `j`, and `t` at `j + 1`. This is the normalisation the Burau columns produce; the matrices
displayed in the literature differ from it by the diagonal change of basis rescaling the `i`-th
basis vector by a power of `t`.

## Normalisation and non-degeneracy

The determinant of a reduced matrix is again `-t` (`TauCeti.KnotTheory.det_reducedBurauMatrix`),
so the reduced determinant character is again `(-t)` to the exponent sum. On at least three strands
no elementary reduced matrix is the identity (`TauCeti.KnotTheory.reducedBurauMatrix_ne_one`), and
the hypothesis `3 ≤ n` there is not an artefact: on two strands the reduced representation is the
one-by-one matrix `(-t)`, which *is* the identity when `t = -1`, so the reduced Burau
representation of `BraidGroup 2` is genuinely trivial at that one value of the parameter.

Two things are deliberately left out. That the Burau columns span the *whole* invariant hyperplane,
and not merely a free rank-`(n - 1)` submodule of it, is not proved here; nothing below needs it,
since a left inverse already gives the cancellation the transport runs on. Nor is the comparison
with the Seifert-matrix Alexander polynomial of `TauCeti/KnotTheory/Alexander.lean`, which needs
the closure of a braid to a link.

This is the Burau route of the "knot polynomials, each a project in itself, with several algorithms
apiece" bullet of Layer 4 ("knot theory, done properly") of the GeometricTopology roadmap.

## Main definitions

* `TauCeti.KnotTheory.burauColMatrix`: the `n × (n - 1)` matrix of the Burau columns, the basis of
  the invariant hyperplane.
* `TauCeti.KnotTheory.burauColMatrixLeftInv`: an explicit left inverse for it.
* `TauCeti.KnotTheory.reducedBurauRow`: the row vector of pairings governing a reduced matrix.
* `TauCeti.KnotTheory.reducedBurauMatrix`: the reduced Burau matrix of an elementary braid.
* `TauCeti.KnotTheory.reducedBurauGL`: the same matrix as an element of the general linear group.
* `TauCeti.KnotTheory.reducedBurau`: the reduced Burau representation
  `BraidGroup n →* GL (Fin (n - 1)) R`.

## Main results

* `TauCeti.KnotTheory.burauColMatrixLeftInv_mul_burauColMatrix` and
  `TauCeti.KnotTheory.burauColMatrix_mul_left_cancel`: the Burau columns are independent, so the
  matrix they form is left cancellable.
* `TauCeti.KnotTheory.geom_vecMul_burauColMatrix`: the Burau columns lie in the invariant
  hyperplane.
* `TauCeti.KnotTheory.burauMatrix_mul_burauColMatrix` and
  `TauCeti.KnotTheory.burau_mul_burauColMatrix`: the intertwining relation, for an elementary
  braid and for an arbitrary one.
* `TauCeti.KnotTheory.reducedBurauMatrix_mul_comm` and
  `TauCeti.KnotTheory.reducedBurauMatrix_braid`: the two braid relations.
* `TauCeti.KnotTheory.det_reducedBurauMatrix` and `TauCeti.KnotTheory.det_reducedBurau`: the
  determinant of an elementary reduced Burau matrix is `-t`, hence the determinant of the reduced
  Burau matrix of a braid is `-t` to its exponent sum.
* `TauCeti.KnotTheory.reducedBurauMatrix_ne_one`: on at least three strands no elementary reduced
  Burau matrix is the identity.

## References

* W. Burau, *Über Zopfgruppen und gleichsinnig verdrillte Verkettungen*, Abh. Math. Sem. Univ.
  Hamburg 11 (1935), 179-186.
* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82, Princeton
  University Press (1974), Chapter 3 (the reduced Burau representation).
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3.
-/

public section

open Matrix

namespace TauCeti.KnotTheory

variable {R : Type*} [CommRing R] {n : ℕ}

/-! ### The Burau columns and the invariant hyperplane -/

/-- The `n × (n - 1)` matrix whose `i`-th column is the Burau column
`burauCol t i = t • e i - e (i + 1)`. Its columns are independent and are annihilated by the
invariant covector `(1, t, …, t ^ (n - 1))`, and the reduced Burau matrices are the matrices of the
unreduced action read in them. -/
def burauColMatrix (t : R) : Matrix (Fin n) (Fin (n - 1)) R :=
  Matrix.of fun a i => burauCol t i a

@[simp]
theorem burauColMatrix_apply (t : R) (a : Fin n) (i : Fin (n - 1)) :
    burauColMatrix t a i = burauCol t i a := (rfl)

/-- Reading off a column of `TauCeti.KnotTheory.burauColMatrix`. -/
theorem burauColMatrix_mulVec_single (t : R) (j : Fin (n - 1)) :
    burauColMatrix t *ᵥ (Pi.single j 1 : Fin (n - 1) → R) = burauCol t j := by
  rw [Matrix.mulVec_single_one]
  rfl

/-- Multiplying `TauCeti.KnotTheory.burauColMatrix` by a row vector pairs that vector with each
Burau column in turn. -/
theorem vecMul_burauColMatrix (t : R) (w : Fin n → R) (i : Fin (n - 1)) :
    (w ᵥ* burauColMatrix t) i = w ⬝ᵥ burauCol t i := (rfl)

/-- **The Burau columns lie in the invariant hyperplane**: the geometric covector
`(1, t, …, t ^ (n - 1))` annihilates every column of `TauCeti.KnotTheory.burauColMatrix`. -/
@[simp]
theorem geom_vecMul_burauColMatrix (t : R) :
    (fun k : Fin n => t ^ (k : ℕ)) ᵥ* burauColMatrix (n := n) t = 0 := by
  funext i
  rw [vecMul_burauColMatrix, dotProduct_burauCol, BraidGroup.val_strand,
    BraidGroup.val_strandSucc, pow_succ]
  simp

/-- The explicit left inverse of `TauCeti.KnotTheory.burauColMatrix`: its `(i, a)` entry is
`-t ^ (a - i - 1)` when `i < a` and `0` otherwise. -/
def burauColMatrixLeftInv (t : R) : Matrix (Fin (n - 1)) (Fin n) R :=
  Matrix.of fun i a => if (i : ℕ) < (a : ℕ) then -t ^ ((a : ℕ) - (i : ℕ) - 1) else 0

@[simp]
theorem burauColMatrixLeftInv_apply (t : R) (i : Fin (n - 1)) (a : Fin n) :
    burauColMatrixLeftInv t i a =
      if (i : ℕ) < (a : ℕ) then -t ^ ((a : ℕ) - (i : ℕ) - 1) else 0 := (rfl)

/-- **The Burau columns are linearly independent**, witnessed by an explicit left inverse. -/
theorem burauColMatrixLeftInv_mul_burauColMatrix (t : R) :
    burauColMatrixLeftInv (n := n) t * burauColMatrix (n := n) t =
      (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) R) := by
  ext i k
  have hmul : (burauColMatrixLeftInv (n := n) t * burauColMatrix (n := n) t) i k =
      burauColMatrixLeftInv t i ⬝ᵥ burauCol t k := (rfl)
  rw [hmul, dotProduct_burauCol, burauColMatrixLeftInv_apply, burauColMatrixLeftInv_apply,
    BraidGroup.val_strand, BraidGroup.val_strandSucc]
  rcases lt_trichotomy (i : ℕ) (k : ℕ) with h | h | h
  · rw [ite_eq_left h, ite_eq_left (by omega),
      show (k : ℕ) + 1 - (i : ℕ) - 1 = (k : ℕ) - (i : ℕ) by omega, neg_mul, ← pow_succ,
      show (k : ℕ) - (i : ℕ) - 1 + 1 = (k : ℕ) - (i : ℕ) by omega,
      Matrix.one_apply_ne (by simp [Fin.ext_iff]; omega)]
    ring
  · have hik : i = k := Fin.val_injective h
    subst hik
    rw [ite_eq_right (by omega), ite_eq_left (by omega),
      show (i : ℕ) + 1 - (i : ℕ) - 1 = 0 by omega, Matrix.one_apply_eq]
    ring
  · rw [ite_eq_right (by omega), ite_eq_right (by omega),
      Matrix.one_apply_ne (by simp [Fin.ext_iff]; omega)]
    ring

/-- The matrix of Burau columns is left cancellable. This is what transports each relation among
the unreduced Burau matrices to the reduced ones. -/
theorem burauColMatrix_mul_left_cancel {m : Type*} (t : R)
    {A B : Matrix (Fin (n - 1)) m R}
    (h : burauColMatrix t * A = burauColMatrix t * B) : A = B := by
  have h' := congrArg (fun M : Matrix (Fin n) m R => burauColMatrixLeftInv t * M) h
  simpa only [← Matrix.mul_assoc, burauColMatrixLeftInv_mul_burauColMatrix, Matrix.one_mul]
    using h'

/-! ### The elementary reduced Burau matrices -/

/-- The row vector governing the reduced Burau matrix of the elementary braid `sigma j`: its `i`-th
entry is the pairing of the `j`-th Burau row with the `i`-th Burau column. -/
def reducedBurauRow (t : R) (j : Fin (n - 1)) : Fin (n - 1) → R :=
  fun i => burauRow R j ⬝ᵥ burauCol t i

@[simp]
theorem reducedBurauRow_self (t : R) (j : Fin (n - 1)) : reducedBurauRow t j j = t + 1 :=
  burauRow_dotProduct_burauCol_self t j

/-- The value of the reduced row of `sigma j` at the index just before `j`. -/
theorem reducedBurauRow_pred (t : R) {i j : Fin (n - 1)} (h : (i : ℕ) + 1 = j) :
    reducedBurauRow t j i = -1 :=
  burauRow_dotProduct_burauCol_of_succ_rev t h

/-- The value of the reduced row of `sigma j` at the index just after `j`. -/
theorem reducedBurauRow_succ (t : R) {i j : Fin (n - 1)} (h : (j : ℕ) + 1 = i) :
    reducedBurauRow t j i = -t :=
  burauRow_dotProduct_burauCol_of_succ t h

/-- The reduced row of `sigma j` vanishes away from `j` and its two neighbours. -/
theorem reducedBurauRow_of_not_adjacent (t : R) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) : reducedBurauRow t j i = 0 :=
  burauRow_dotProduct_burauCol_of_not_adjacent t h.symm

/-- The closed form of the reduced row of `sigma j`: it is `t + 1` at `j`, `-1` at `j - 1`, `-t`
at `j + 1`, and `0` elsewhere. -/
theorem reducedBurauRow_apply (t : R) (j i : Fin (n - 1)) :
    reducedBurauRow t j i = (if (i : ℕ) = j then t + 1 else 0) - (if (i : ℕ) + 1 = j then 1 else 0)
      - (if (j : ℕ) + 1 = i then t else 0) := by
  rcases eq_or_ne (i : ℕ) (j : ℕ) with h | h
  · have hij : i = j := Fin.val_injective h
    subst hij
    rw [reducedBurauRow_self, ite_eq_left rfl, ite_eq_right (by omega), ite_eq_right (by omega)]
    ring
  · by_cases h₁ : (i : ℕ) + 1 = j
    · rw [reducedBurauRow_pred t h₁, ite_eq_right h, ite_eq_left h₁, ite_eq_right (by omega)]
      ring
    · by_cases h₂ : (j : ℕ) + 1 = i
      · rw [reducedBurauRow_succ t h₂, ite_eq_right h, ite_eq_right h₁, ite_eq_left h₂]
        ring
      · rw [reducedBurauRow_of_not_adjacent t (by omega), ite_eq_right h, ite_eq_right h₁,
          ite_eq_right h₂]
        ring

/-- The reduced Burau matrix of the elementary braid `TauCeti.BraidGroup.sigma j`: the identity
outside its `j`-th row, whose entries are `1` at `j - 1`, `-t` at `j` and `t` at `j + 1`. -/
def reducedBurauMatrix (t : R) (j : Fin (n - 1)) : Matrix (Fin (n - 1)) (Fin (n - 1)) R :=
  1 - vecMulVec (Pi.single j 1) (reducedBurauRow t j)

/-- The defining formula for an elementary reduced Burau matrix: it differs from the identity by a
rank-one matrix supported in the row `j`. -/
theorem reducedBurauMatrix_def (t : R) (j : Fin (n - 1)) :
    reducedBurauMatrix t j = 1 - vecMulVec (Pi.single j 1) (reducedBurauRow t j) := by
  rw [reducedBurauMatrix]

/-- The entries of an elementary reduced Burau matrix. -/
theorem reducedBurauMatrix_apply (t : R) (j a b : Fin (n - 1)) :
    reducedBurauMatrix t j a b =
      (if a = b then 1 else 0) - (if a = j then 1 else 0) * reducedBurauRow t j b := by
  rw [reducedBurauMatrix_def, Matrix.sub_apply, vecMulVec_apply, Matrix.one_apply, Pi.single_apply]

/-- Outside the row `j` an elementary reduced Burau matrix has the rows of the identity. -/
theorem reducedBurauMatrix_apply_of_ne (t : R) {j a : Fin (n - 1)} (h : a ≠ j) (b : Fin (n - 1)) :
    reducedBurauMatrix t j a b = if a = b then 1 else 0 := by
  rw [reducedBurauMatrix_apply, ite_eq_right h]
  ring

/-- The row `j` of an elementary reduced Burau matrix. -/
theorem reducedBurauMatrix_apply_row (t : R) (j b : Fin (n - 1)) :
    reducedBurauMatrix t j j b = (if j = b then 1 else 0) - reducedBurauRow t j b := by
  rw [reducedBurauMatrix_apply, ite_eq_left rfl, one_mul]

/-- The diagonal entry of an elementary reduced Burau matrix in its distinguished row. -/
@[simp]
theorem reducedBurauMatrix_apply_self (t : R) (j : Fin (n - 1)) :
    reducedBurauMatrix t j j j = -t := by
  rw [reducedBurauMatrix_apply_row, ite_eq_left rfl, reducedBurauRow_self]
  ring

/-! ### The intertwining relation -/

/-- Every rank-one update of the identity along the `j`-th Burau row and column intertwines with
the corresponding update along the `j`-th reduced row. Both the elementary reduced Burau matrix and
its inverse are instances, at `c = 1` and `c = t⁻¹`. -/
theorem one_sub_smul_vecMulVec_mul_burauColMatrix (t c : R) (j : Fin (n - 1)) :
    (1 - c • vecMulVec (burauCol t j) (burauRow R j)) * burauColMatrix (n := n) t =
      burauColMatrix t * (1 - c • vecMulVec (Pi.single j 1) (reducedBurauRow t j)) := by
  have hrow : burauRow R j ᵥ* burauColMatrix (n := n) t = reducedBurauRow t j := (rfl)
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, vecMulVec_mul, mul_vecMulVec, hrow, burauColMatrix_mulVec_single]

/-- Intertwining passes to inverses: if `A' * A = 1`, `D * D' = 1` and `A * C = C * D`, then
`A' * C = C * D'`. This is the inverse step of the induction in
`TauCeti.KnotTheory.burau_mul_burauColMatrix`. -/
private theorem intertwine_inv {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p]
    [DecidableEq q] {A A' : Matrix p p R} {D D' : Matrix q q R} {C : Matrix p q R}
    (hA : A' * A = 1) (hD : D * D' = 1) (h : A * C = C * D) : A' * C = C * D' := by
  calc A' * C = A' * (C * (D * D')) := by rw [hD, Matrix.mul_one]
    _ = A' * (C * D * D') := by rw [Matrix.mul_assoc]
    _ = A' * (A * C * D') := by rw [h]
    _ = A' * A * (C * D') := by rw [Matrix.mul_assoc, Matrix.mul_assoc]
    _ = C * D' := by rw [hA, Matrix.one_mul]

/-- **The intertwining relation**: the reduced Burau matrix of `sigma j` is the unreduced Burau
matrix of `sigma j` read in the basis of Burau columns. -/
theorem burauMatrix_mul_burauColMatrix (t : R) (j : Fin (n - 1)) :
    burauMatrix t j * burauColMatrix (n := n) t =
      burauColMatrix t * reducedBurauMatrix t j := by
  rw [burauMatrix_def, reducedBurauMatrix_def, ← one_smul R (vecMulVec (burauCol t j) _),
    ← one_smul R (vecMulVec (Pi.single j 1) _)]
  exact one_sub_smul_vecMulVec_mul_burauColMatrix t 1 j

/-- The same intertwining relation for the inverse of an elementary Burau matrix. -/
theorem inv_burauMatrix_mul_burauColMatrix (t : Rˣ) (j : Fin (n - 1)) :
    (burauMatrix (t : R) j)⁻¹ * burauColMatrix (n := n) (t : R) =
      burauColMatrix (t : R) *
        (1 - ((t⁻¹ : Rˣ) : R) • vecMulVec (Pi.single j 1) (reducedBurauRow (t : R) j)) := by
  rw [inv_burauMatrix]
  exact one_sub_smul_vecMulVec_mul_burauColMatrix (t : R) ((t⁻¹ : Rˣ) : R) j

/-- Two elementary reduced Burau matrices multiply the way the unreduced ones do. -/
private theorem burauColMatrix_mul_reducedBurauMatrix_mul (t : R) (i j : Fin (n - 1)) :
    burauColMatrix t * (reducedBurauMatrix t i * reducedBurauMatrix t j) =
      burauMatrix t i * burauMatrix t j * burauColMatrix t := by
  rw [← Matrix.mul_assoc, ← burauMatrix_mul_burauColMatrix, Matrix.mul_assoc,
    ← burauMatrix_mul_burauColMatrix, ← Matrix.mul_assoc]

private theorem burauColMatrix_mul_reducedBurauMatrix_mul_mul (t : R) (i j k : Fin (n - 1)) :
    burauColMatrix t * (reducedBurauMatrix t i * reducedBurauMatrix t j * reducedBurauMatrix t k) =
      burauMatrix t i * burauMatrix t j * burauMatrix t k * burauColMatrix t := by
  rw [← Matrix.mul_assoc, burauColMatrix_mul_reducedBurauMatrix_mul, Matrix.mul_assoc,
    ← burauMatrix_mul_burauColMatrix, ← Matrix.mul_assoc]

/-- **The distant commutation relation** for the elementary reduced Burau matrices. -/
theorem reducedBurauMatrix_mul_comm (t : R) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    reducedBurauMatrix t i * reducedBurauMatrix t j =
      reducedBurauMatrix t j * reducedBurauMatrix t i := by
  refine burauColMatrix_mul_left_cancel t ?_
  rw [burauColMatrix_mul_reducedBurauMatrix_mul, burauColMatrix_mul_reducedBurauMatrix_mul,
    burauMatrix_mul_comm t h]

/-- **The braid relation** for the elementary reduced Burau matrices. -/
theorem reducedBurauMatrix_braid (t : R) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    reducedBurauMatrix t i * reducedBurauMatrix t j * reducedBurauMatrix t i =
      reducedBurauMatrix t j * reducedBurauMatrix t i * reducedBurauMatrix t j := by
  refine burauColMatrix_mul_left_cancel t ?_
  rw [burauColMatrix_mul_reducedBurauMatrix_mul_mul,
    burauColMatrix_mul_reducedBurauMatrix_mul_mul, burauMatrix_braid t h]

/-- The inverse of an elementary reduced Burau matrix is
`1 - t⁻¹ • vecMulVec (Pi.single j 1) (reducedBurauRow t j)`. -/
private theorem reducedBurauMatrix_mul_inv (t : Rˣ) (j : Fin (n - 1)) :
    reducedBurauMatrix (t : R) j *
      (1 - ((t⁻¹ : Rˣ) : R) • vecMulVec (Pi.single j 1) (reducedBurauRow (t : R) j)) = 1 := by
  refine burauColMatrix_mul_left_cancel (t : R) ?_
  have hdet : IsUnit (burauMatrix (t : R) j).det := by
    rw [det_burauMatrix]
    exact t.isUnit.neg
  have hcancel : burauMatrix (t : R) j * (burauMatrix (t : R) j)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hdet
  rw [← Matrix.mul_assoc, ← burauMatrix_mul_burauColMatrix, Matrix.mul_assoc,
    ← inv_burauMatrix_mul_burauColMatrix, ← Matrix.mul_assoc, hcancel, Matrix.one_mul,
    Matrix.mul_one]

/-- The determinant of an elementary reduced Burau matrix is `-t`, as for the unreduced ones. -/
@[simp]
theorem det_reducedBurauMatrix (t : R) (j : Fin (n - 1)) :
    (reducedBurauMatrix t j).det = -t := by
  rw [reducedBurauMatrix_def, sub_eq_add_neg, ← neg_vecMulVec, vecMulVec_eq Unit,
    det_one_add_replicateCol_mul_replicateRow, dotProduct_neg, dotProduct_single,
    reducedBurauRow_self]
  ring

/-- **On at least three strands no elementary reduced Burau matrix is the identity.** The
hypothesis `3 ≤ n` is necessary: on two strands the reduced representation is the one-by-one
matrix `(-t)`, which is the identity when `t = -1`. -/
theorem reducedBurauMatrix_ne_one [Nontrivial R] {t : R} (ht : t ≠ 0) (j : Fin (n - 1))
    (hn : 3 ≤ n) : reducedBurauMatrix t j ≠ 1 := by
  intro h
  -- were the matrix the identity, the whole reduced row would vanish
  have key : ∀ b : Fin (n - 1), reducedBurauRow t j b = 0 := by
    intro b
    have hb := congrArg (fun M : Matrix (Fin (n - 1)) (Fin (n - 1)) R => M j b) h
    rw [reducedBurauMatrix_apply_row, Matrix.one_apply] at hb
    exact sub_eq_self.mp hb
  rcases lt_or_ge ((j : ℕ) + 1) (n - 1) with hj | hj
  · -- the reduced row is `-t` at `j + 1`, so the matrix entry there is `t`
    have hentry := key ⟨(j : ℕ) + 1, hj⟩
    rw [reducedBurauRow_succ t (i := ⟨(j : ℕ) + 1, hj⟩) (j := j) rfl] at hentry
    exact ht (neg_eq_zero.mp hentry)
  · -- otherwise `j` is the last index, and the reduced row is `-1` at `j - 1`
    have hjlt := j.isLt
    have hb : (j : ℕ) - 1 < n - 1 := by omega
    have hentry := key ⟨(j : ℕ) - 1, hb⟩
    rw [reducedBurauRow_pred t (i := ⟨(j : ℕ) - 1, hb⟩) (j := j)
      (show (j : ℕ) - 1 + 1 = (j : ℕ) by omega)] at hentry
    exact one_ne_zero (neg_eq_zero.mp hentry)

/-! ### The reduced Burau representation -/

/-- An elementary reduced Burau matrix as an element of the general linear group. -/
def reducedBurauGL (t : Rˣ) (j : Fin (n - 1)) : GL (Fin (n - 1)) R where
  val := reducedBurauMatrix (t : R) j
  inv := 1 - ((t⁻¹ : Rˣ) : R) • vecMulVec (Pi.single j 1) (reducedBurauRow (t : R) j)
  val_inv := reducedBurauMatrix_mul_inv t j
  inv_val := mul_eq_one_comm.mp (reducedBurauMatrix_mul_inv t j)

/-- The matrix underlying `TauCeti.KnotTheory.reducedBurauGL`. -/
@[simp]
theorem coe_reducedBurauGL (t : Rˣ) (j : Fin (n - 1)) :
    (reducedBurauGL t j : Matrix (Fin (n - 1)) (Fin (n - 1)) R) = reducedBurauMatrix (t : R) j :=
  (rfl)

/-- The nonsingular inverse of an elementary reduced Burau matrix. -/
@[simp]
theorem inv_reducedBurauMatrix (t : Rˣ) (j : Fin (n - 1)) :
    (reducedBurauMatrix (t : R) j)⁻¹ =
      1 - ((t⁻¹ : Rˣ) : R) • vecMulVec (Pi.single j 1) (reducedBurauRow (t : R) j) :=
  Matrix.inv_eq_right_inv (reducedBurauMatrix_mul_inv t j)

/-- **The reduced Burau representation** of the braid group on `n` strands at a unit `t`: the
restriction of the unreduced representation to the free rank-`(n - 1)` submodule spanned by the
Burau columns, which lies in the hyperplane annihilated by the invariant covector, written in that
basis. -/
def reducedBurau (n : ℕ) (t : Rˣ) : BraidGroup n →* GL (Fin (n - 1)) R :=
  BraidGroup.lift (reducedBurauGL t) (fun h => Units.ext (reducedBurauMatrix_mul_comm _ h))
    (fun h => Units.ext (reducedBurauMatrix_braid _ h))

/-- The reduced Burau representation takes an elementary braid to the elementary reduced Burau
matrix. -/
@[simp]
theorem reducedBurau_sigma (t : Rˣ) (i : Fin (n - 1)) :
    reducedBurau n t (BraidGroup.sigma i) = (reducedBurauGL t i : GL (Fin (n - 1)) R) :=
  BraidGroup.lift_sigma _ _ _ i

/-- The determinant of the reduced Burau matrix of a braid is `-t` raised to its exponent sum,
exactly as for the unreduced representation. -/
theorem det_reducedBurau (t : Rˣ) (b : BraidGroup n) :
    Matrix.GeneralLinearGroup.det (reducedBurau n t b : GL (Fin (n - 1)) R) =
      (-t) ^ Multiplicative.toAdd (ArtinGroup.exponentSum (CoxeterMatrix.A (n - 1)) b) := by
  have key : (Matrix.GeneralLinearGroup.det (n := Fin (n - 1)) (R := R)).comp (reducedBurau n t) =
      (zpowersHom Rˣ (-t)).comp (ArtinGroup.exponentSum (CoxeterMatrix.A (n - 1))) := by
    refine BraidGroup.hom_ext fun i => ?_
    apply Units.ext
    simp [det_reducedBurauMatrix]
  exact congrArg (fun f : BraidGroup n →* Rˣ => f b) key

/-- **The reduced Burau representation is a subrepresentation of the unreduced one**: the matrix of
Burau columns intertwines them, for every braid, and is left cancellable by
`TauCeti.KnotTheory.burauColMatrix_mul_left_cancel`. -/
theorem burau_mul_burauColMatrix (t : Rˣ) (b : BraidGroup n) :
    (burau n t b : Matrix (Fin n) (Fin n) R) * burauColMatrix (t : R) =
      burauColMatrix (t : R) *
        (reducedBurau n t b : Matrix (Fin (n - 1)) (Fin (n - 1)) R) := by
  refine BraidGroup.sigma_induction_on
    (p := fun b => (burau n t b : Matrix (Fin n) (Fin n) R) * burauColMatrix (t : R) =
      burauColMatrix (t : R) *
        (reducedBurau n t b : Matrix (Fin (n - 1)) (Fin (n - 1)) R)) b ?_ ?_ ?_ ?_
  · intro i
    simp only [burau_sigma, coe_burauGL, reducedBurau_sigma, coe_reducedBurauGL]
    exact burauMatrix_mul_burauColMatrix (t : R) i
  · rw [map_one, map_one, Units.val_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  · intro b b' hb hb'
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, hb',
      ← Matrix.mul_assoc, hb, Matrix.mul_assoc]
  · intro b hb
    rw [map_inv, map_inv]
    refine intertwine_inv ?_ ?_ hb
    · rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    · rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

end TauCeti.KnotTheory
