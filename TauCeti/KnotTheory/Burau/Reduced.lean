/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Burau.Basic

/-!
# The reduced Burau representation of the braid group

The unreduced Burau representation `TauCeti.KnotTheory.burau` of `TauCeti.BraidGroup n`, built in
`TauCeti/KnotTheory/Burau/Basic.lean`, is reducible: the row vector `(1, t, …, t ^ (n - 1))` is
fixed by every Burau matrix, so its kernel is an invariant submodule. That kernel contains the
`n - 1` Burau columns `burauCol t i = t • e i - e (i + 1)`, and they are independent over any base
ring in which `t` is a unit. The braid group acts on their span, and the matrices of that action in
the basis of Burau columns form the **reduced Burau representation**
`TauCeti.KnotTheory.reducedBurau`, of rank `n - 1`. Geometrically the unreduced representation is
the first homology of the infinite cyclic cover of the `n`-punctured disc *relative* to the fibre
over a basepoint, and the reduced one is the absolute first homology of that cover.

The construction here is deliberately basis-first, and reuses the pairings of the unreduced file.
The calculus those pairings feed is set up once, for an arbitrary family of matrices
`1 - u i ⊗ v i` over an arbitrary index type, in the `TauCeti.KnotTheory.RankOneMatrix` namespace:
the product of two members, the braid relations, the quadratic relation, the inverse, the
determinant, and the braid-group representation a family with the Burau pairings defines. Writing
`M i = 1 - vecMulVec (burauCol t i) (burauRow R i)` for the elementary Burau matrix, the action on
the Burau columns is
`M i *ᵥ burauCol t j = burauCol t j - (burauRow R i ⬝ᵥ burauCol t j) • burauCol t i`,
so the matrix of the action in the basis of Burau columns is again a rank-one perturbation of the
identity,
`reducedBurauMatrix t i = 1 - vecMulVec (Pi.single i 1) (reducedBurauRow t i)`,
whose row `TauCeti.KnotTheory.reducedBurauRow` collects the very same pairings
`burauRow R i ⬝ᵥ burauCol t j` that drive the unreduced file — `t + 1` on the diagonal, `-t` and
`-1` on the two off-diagonals, and `0` away from them. Consequently the braid relations, the
inverse and the determinant of the reduced matrices follow from exactly the same four pairings, and
`TauCeti.KnotTheory.burauMatrix_mul_burauColMatrix` records that the two representations are
intertwined by the matrix `TauCeti.KnotTheory.burauColMatrix` of Burau columns.

Two theorems keep the reduction honest. The Burau columns really do lie in the invariant submodule
(`TauCeti.KnotTheory.geom_vecMul_burauColMatrix`: the geometric covector annihilates them), and
they really are independent: `TauCeti.KnotTheory.burauCoordMatrix_mul_burauColMatrix` exhibits an
explicit left inverse of `burauColMatrix`, built from the powers of `t⁻¹`. That left inverse also
recovers the reduced matrix of a braid from the unreduced one
(`TauCeti.KnotTheory.reducedBurau_eq`), so no information is lost or invented in passing to the
reduced representation.

Finally, `TauCeti.KnotTheory.reducedBurauMatrix_mul_self` records the quadratic relation
`x * x = (1 - t) • x + t • 1`, that is, `(x - 1) * (x + t) = 0`: together with the braid relations
this is the Iwahori-Hecke relation in the normalisation with eigenvalues `1` and `-t`, so the
reduced Burau representation factors through a Hecke algebra of type `A`. The comparison with the
Alexander polynomial of `TauCeti/KnotTheory/Alexander.lean` needs the closure of a braid to a link
and is not built here.

This is the Burau route of the "knot polynomials, each a project in itself, with several algorithms
apiece" bullet of Layer 4 ("knot theory, done properly") of the GeometricTopology roadmap.

## Main definitions

* `TauCeti.KnotTheory.RankOneMatrix.family`, `TauCeti.KnotTheory.RankOneMatrix.unit` and
  `TauCeti.KnotTheory.RankOneMatrix.representation`: the family of matrices `1 - u i ⊗ v i`
  attached to two families of vectors, its members as elements of the general linear group, and
  the braid-group representation they define when the pairings `v i ⬝ᵥ u j` take the Burau values.
* `TauCeti.KnotTheory.burauColMatrix`: the `n × (n - 1)` matrix whose columns are the Burau
  columns, that is, the inclusion of the invariant submodule they span.
* `TauCeti.KnotTheory.burauCoordMatrix`: an explicit left inverse of `burauColMatrix` at a unit
  `t`, so the Burau columns are independent and span a free rank `n - 1` direct summand.
* `TauCeti.KnotTheory.reducedBurauRow`: the pairings of one Burau row against all Burau columns.
* `TauCeti.KnotTheory.reducedBurauMatrix`: the reduced Burau matrix of an elementary braid.
* `TauCeti.KnotTheory.reducedBurauGL` and `TauCeti.KnotTheory.reducedBurau`: the reduced Burau
  representation `BraidGroup n →* GL (Fin (n - 1)) R`.

## Main results

* `TauCeti.KnotTheory.burauMatrix_mul_burauColMatrix` and
  `TauCeti.KnotTheory.burau_mul_burauColMatrix`: **the reduced representation is the restriction of
  the unreduced one** to the span of the Burau columns, at the level of elementary braids and of
  the whole braid group.
* `TauCeti.KnotTheory.reducedBurau_eq`: conversely, the reduced Burau matrix of a braid is read off
  from the unreduced one through `burauCoordMatrix`.
* `TauCeti.KnotTheory.reducedBurauMatrix_mul_comm` and
  `TauCeti.KnotTheory.reducedBurauMatrix_braid`: the two braid relations.
* `TauCeti.KnotTheory.det_reducedBurauMatrix` and `TauCeti.KnotTheory.det_reducedBurau`: the
  determinant of an elementary reduced Burau matrix is `-t`, hence that of a braid is `-t` to its
  exponent sum.
* `TauCeti.KnotTheory.reducedBurauMatrix_mul_self`: the Iwahori-Hecke quadratic relation.
* `TauCeti.KnotTheory.reducedBurauMatrix_two`, `TauCeti.KnotTheory.reducedBurauMatrix_three_zero`
  and `TauCeti.KnotTheory.reducedBurauMatrix_three_one`: the classical reduced Burau matrices on
  two and three strands.

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82, Princeton
  University Press (1974), Chapter 3 (the reduced Burau representation).
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3.
-/

public section

open Matrix

namespace TauCeti.KnotTheory

variable {R : Type*} {n : ℕ}

/-! ### Rank-one matrix families -/

namespace RankOneMatrix

variable {ι α : Type*}

section Ring

variable [Ring R] [DecidableEq α]

/-- The family of matrices `1 - u i ⊗ v i` associated to two families of vectors. -/
def family (u v : ι → α → R) (i : ι) : Matrix α α R :=
  1 - vecMulVec (u i) (v i)

/-- The defining formula for a rank-one matrix family. -/
lemma family_def (u v : ι → α → R) (i : ι) :
    family u v i = 1 - vecMulVec (u i) (v i) :=
  (rfl)

end Ring

section CommRing

variable [CommRing R] [Fintype α] [DecidableEq α]

/-- The product of two members of a rank-one matrix family. -/
theorem family_mul_family (u v : ι → α → R) (i j : ι) :
    family u v i * family u v j =
      1 - vecMulVec (u i) (v i) - vecMulVec (u j) (v j) +
        (v i ⬝ᵥ u j) • vecMulVec (u i) (v j) := by
  simp only [family, sub_mul, mul_sub, one_mul, mul_one, vecMulVec_mul_vecMulVec,
    vecMulVec_smul]
  abel

/-- Two members of a rank-one matrix family commute when their cross-pairings vanish. -/
theorem family_mul_comm (u v : ι → α → R) {i j : ι} (hij : v i ⬝ᵥ u j = 0)
    (hji : v j ⬝ᵥ u i = 0) : family u v i * family u v j = family u v j * family u v i := by
  rw [family_mul_family, family_mul_family, hij, hji]
  simp only [zero_smul, add_zero]
  abel

/-- Two members of a rank-one matrix family obey the braid relation when their four pairings have
the values occurring in the Burau representation. -/
theorem family_braid (t : R) (u v : ι → α → R) {i j : ι} (hii : v i ⬝ᵥ u i = t + 1)
    (hjj : v j ⬝ᵥ u j = t + 1) (hij : v i ⬝ᵥ u j = -t) (hji : v j ⬝ᵥ u i = -1) :
    family u v i * family u v j * family u v i =
      family u v j * family u v i * family u v j := by
  simp only [family, sub_mul, mul_sub, one_mul, mul_one, vecMulVec_mul_vecMulVec,
    vecMulVec_smul, smul_mul_assoc, smul_smul, hii, hjj, hij, hji]
  module

/-- The braid relation for two members of a rank-one matrix family indexed by adjacent generators,
in the symmetric form: the two possible adjacency orders are covered at once. -/
theorem family_braid_or (t : R) (u v : Fin (n - 1) → α → R)
    (hself : ∀ i, v i ⬝ᵥ u i = t + 1)
    (hbraid : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 1 = j → v i ⬝ᵥ u j = -t ∧ v j ⬝ᵥ u i = -1)
    {i j : Fin (n - 1)} (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    family u v i * family u v j * family u v i =
      family u v j * family u v i * family u v j := by
  rcases h with h | h
  · exact family_braid t u v (hself i) (hself j) (hbraid h).1 (hbraid h).2
  · exact (family_braid t u v (hself j) (hself i) (hbraid h).1 (hbraid h).2).symm

/-- The quadratic relation for a member of a rank-one matrix family whose self-pairing is
`t + 1`. -/
theorem family_mul_self (t : R) (u v : ι → α → R) (i : ι) (hii : v i ⬝ᵥ u i = t + 1) :
    family u v i * family u v i = (1 - t) • family u v i + t • 1 := by
  rw [family_mul_family, hii, family]
  module

/-- A right inverse for a member of a rank-one matrix family whose self-pairing is `t + 1`. -/
theorem family_mul_inv (t : Rˣ) (u v : ι → α → R) (i : ι)
    (hii : v i ⬝ᵥ u i = (t : R) + 1) :
    family u v i * (1 - ((t⁻¹ : Rˣ) : R) • vecMulVec (u i) (v i)) = 1 := by
  have hb : vecMulVec (u i) (v i) * vecMulVec (u i) (v i) =
      ((t : R) + 1) • vecMulVec (u i) (v i) := by
    rw [vecMulVec_mul_vecMulVec, hii, vecMulVec_smul]
  have hc : ((t⁻¹ : Rˣ) : R) * ((t : R) + 1) = 1 + ((t⁻¹ : Rˣ) : R) := by
    rw [mul_add, mul_one, Units.inv_mul]
  simp only [family, sub_mul, mul_sub, one_mul, mul_one, mul_smul_comm, hb, smul_sub]
  rw [smul_smul, hc, add_smul, one_smul]
  abel

/-- A left inverse for a member of a rank-one matrix family whose self-pairing is `t + 1`. -/
theorem family_inv_mul (t : Rˣ) (u v : ι → α → R) (i : ι)
    (hii : v i ⬝ᵥ u i = (t : R) + 1) :
    (1 - ((t⁻¹ : Rˣ) : R) • vecMulVec (u i) (v i)) * family u v i = 1 :=
  mul_eq_one_comm.mp (family_mul_inv t u v i hii)

/-- The determinant of a member of a rank-one matrix family in terms of its self-pairing. -/
theorem det_family (u v : ι → α → R) (i : ι) :
    (family u v i).det = 1 - v i ⬝ᵥ u i := by
  rw [family, sub_eq_add_neg, ← neg_vecMulVec, vecMulVec_eq Unit,
    det_one_add_replicateCol_mul_replicateRow, dotProduct_neg]
  ring

/-- A member of a rank-one matrix family as an element of the general linear group, when its
self-pairing is `t + 1`. -/
def unit (t : Rˣ) (u v : ι → α → R) (hself : ∀ i, v i ⬝ᵥ u i = (t : R) + 1) (i : ι) :
    GL α R where
  val := family u v i
  inv := 1 - ((t⁻¹ : Rˣ) : R) • vecMulVec (u i) (v i)
  val_inv := family_mul_inv t u v i (hself i)
  inv_val := family_inv_mul t u v i (hself i)

/-- The matrix underlying `TauCeti.KnotTheory.RankOneMatrix.unit`. -/
@[simp]
theorem coe_unit (t : Rˣ) (u v : ι → α → R) (hself : ∀ i, v i ⬝ᵥ u i = (t : R) + 1)
    (i : ι) : (unit t u v hself i : Matrix α α R) = family u v i :=
  (rfl)

/-- The inverse of a member of a rank-one matrix family whose self-pairing is `t + 1`. -/
theorem inv_family (t : Rˣ) (u v : ι → α → R) (i : ι)
    (hii : v i ⬝ᵥ u i = (t : R) + 1) :
    (family u v i)⁻¹ = 1 - ((t⁻¹ : Rˣ) : R) • vecMulVec (u i) (v i) :=
  Matrix.inv_eq_right_inv (family_mul_inv t u v i hii)

/-- The braid-group representation associated to a rank-one matrix family with the Burau
pairings. -/
def representation (n : ℕ) (t : Rˣ) (u v : Fin (n - 1) → α → R)
    (hself : ∀ i, v i ⬝ᵥ u i = (t : R) + 1)
    (hcomm : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i →
      v i ⬝ᵥ u j = 0 ∧ v j ⬝ᵥ u i = 0)
    (hbraid : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 1 = j →
      v i ⬝ᵥ u j = -(t : R) ∧ v j ⬝ᵥ u i = -1) : BraidGroup n →* GL α R :=
  BraidGroup.lift (unit t u v hself)
    (fun h => Units.ext (family_mul_comm u v (hcomm h).1 (hcomm h).2))
    (fun h => Units.ext (family_braid_or (t : R) u v hself hbraid h))

/-- A rank-one braid-group representation takes an elementary braid to its corresponding unit. -/
@[simp]
theorem representation_sigma (n : ℕ) (t : Rˣ) (u v : Fin (n - 1) → α → R)
    (hself : ∀ i, v i ⬝ᵥ u i = (t : R) + 1)
    (hcomm : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i →
      v i ⬝ᵥ u j = 0 ∧ v j ⬝ᵥ u i = 0)
    (hbraid : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 1 = j →
      v i ⬝ᵥ u j = -(t : R) ∧ v j ⬝ᵥ u i = -1) (i : Fin (n - 1)) :
    representation n t u v hself hcomm hbraid (BraidGroup.sigma i) = unit t u v hself i :=
  BraidGroup.lift_sigma _ _ _ i

/-- The determinant character of a rank-one braid-group representation with the Burau
pairings. -/
theorem det_representation (n : ℕ) (t : Rˣ) (u v : Fin (n - 1) → α → R)
    (hself : ∀ i, v i ⬝ᵥ u i = (t : R) + 1)
    (hcomm : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i →
      v i ⬝ᵥ u j = 0 ∧ v j ⬝ᵥ u i = 0)
    (hbraid : ∀ {i j : Fin (n - 1)}, (i : ℕ) + 1 = j →
      v i ⬝ᵥ u j = -(t : R) ∧ v j ⬝ᵥ u i = -1) (b : BraidGroup n) :
    Matrix.GeneralLinearGroup.det (representation n t u v hself hcomm hbraid b) =
      (-t) ^ Multiplicative.toAdd (ArtinGroup.exponentSum (CoxeterMatrix.A (n - 1)) b) := by
  have key : (Matrix.GeneralLinearGroup.det (n := α) (R := R)).comp
      (representation n t u v hself hcomm hbraid) =
      (zpowersHom Rˣ (-t)).comp (ArtinGroup.exponentSum (CoxeterMatrix.A (n - 1))) := by
    refine BraidGroup.hom_ext fun i => ?_
    apply Units.ext
    simp [det_family, hself]
  exact congrArg (fun f : BraidGroup n →* Rˣ => f b) key

end CommRing

end RankOneMatrix

section CommRing

variable [CommRing R]

/-! ### The submodule spanned by the Burau columns -/

/-- The `n × (n - 1)` matrix whose `i`-th column is the Burau column
`TauCeti.KnotTheory.burauCol t i`. Its image is the submodule of the unreduced Burau
representation that carries the reduced one. -/
def burauColMatrix (n : ℕ) (t : R) : Matrix (Fin n) (Fin (n - 1)) R :=
  Matrix.of fun a i => burauCol t i a

/-- The entries of `TauCeti.KnotTheory.burauColMatrix`. -/
@[simp]
theorem burauColMatrix_apply (n : ℕ) (t : R) (a : Fin n) (i : Fin (n - 1)) :
    burauColMatrix n t a i = burauCol t i a :=
  (rfl)

/-- Multiplying a matrix into `TauCeti.KnotTheory.burauColMatrix` pairs its rows with the Burau
columns. -/
theorem mul_burauColMatrix_apply {m : ℕ} (M : Matrix (Fin m) (Fin n) R) (t : R) (a : Fin m)
    (i : Fin (n - 1)) : (M * burauColMatrix n t) a i = M a ⬝ᵥ burauCol t i :=
  (rfl)

/-- Multiplying a row vector into `TauCeti.KnotTheory.burauColMatrix` pairs it with the Burau
columns. -/
theorem vecMul_burauColMatrix_apply (t : R) (v : Fin n → R) (i : Fin (n - 1)) :
    (v ᵥ* burauColMatrix n t) i = v ⬝ᵥ burauCol t i :=
  (rfl)

/-- The `i`-th column of `TauCeti.KnotTheory.burauColMatrix` is the `i`-th Burau column. -/
@[simp]
theorem burauColMatrix_col (n : ℕ) (t : R) (i : Fin (n - 1)) :
    (burauColMatrix n t).col i = burauCol t i :=
  (rfl)

/-- `TauCeti.KnotTheory.burauColMatrix` sends the `i`-th basis vector to the `i`-th Burau
column. -/
theorem burauColMatrix_mulVec_single (n : ℕ) (t : R) (i : Fin (n - 1)) :
    burauColMatrix n t *ᵥ Pi.single i 1 = burauCol t i := by
  rw [Matrix.mulVec_single_one, burauColMatrix_col]

/-- **The Burau columns lie in the kernel of the geometric covector**, the invariant submodule of
`TauCeti.KnotTheory.vecMul_burau_geom`. -/
@[simp]
theorem geom_vecMul_burauColMatrix (n : ℕ) (t : R) :
    (fun k : Fin n => t ^ (k : ℕ)) ᵥ* burauColMatrix n t = 0 := by
  funext i
  rw [vecMul_burauColMatrix_apply, geom_dotProduct_burauCol, Pi.zero_apply]

/-- The coordinates of a vector of the span of the Burau columns in that basis: the `(i, a)` entry
is `t ^ (a - i - 1)`, that is, `t⁻¹ ^ (i + 1 - a)` for `a ≤ i`, and `0` otherwise. This is the
explicit left inverse of `TauCeti.KnotTheory.burauColMatrix` of
`TauCeti.KnotTheory.burauCoordMatrix_mul_burauColMatrix`. -/
def burauCoordMatrix (n : ℕ) (t : Rˣ) : Matrix (Fin (n - 1)) (Fin n) R :=
  Matrix.of fun i a =>
    if (a : ℕ) ≤ (i : ℕ) then ((t⁻¹ : Rˣ) : R) ^ ((i : ℕ) + 1 - (a : ℕ)) else 0

/-- The entries of `TauCeti.KnotTheory.burauCoordMatrix`. -/
theorem burauCoordMatrix_apply (n : ℕ) (t : Rˣ) (i : Fin (n - 1)) (a : Fin n) :
    burauCoordMatrix n t i a =
      if (a : ℕ) ≤ (i : ℕ) then ((t⁻¹ : Rˣ) : R) ^ ((i : ℕ) + 1 - (a : ℕ)) else 0 :=
  (rfl)

/-- **The Burau columns are independent**: at a unit `t` the matrix of Burau columns has an
explicit left inverse. In particular the submodule they span is free of rank `n - 1` and is a
direct summand of the free module on the strands. -/
theorem burauCoordMatrix_mul_burauColMatrix (n : ℕ) (t : Rˣ) :
    burauCoordMatrix n t * burauColMatrix n (t : R) = 1 := by
  ext i k
  rw [mul_burauColMatrix_apply, dotProduct_burauCol, burauCoordMatrix_apply,
    burauCoordMatrix_apply, BraidGroup.val_strand, BraidGroup.val_strandSucc]
  rcases lt_trichotomy (k : ℕ) (i : ℕ) with hlt | heq | hgt
  · have hne : i ≠ k := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
    have hsplit : (i : ℕ) + 1 - (k : ℕ) = ((i : ℕ) + 1 - ((k : ℕ) + 1)) + 1 := by omega
    rw [ite_eq_left hlt.le, ite_eq_left (by omega : (k : ℕ) + 1 ≤ (i : ℕ)), hsplit, pow_succ,
      mul_assoc, Units.inv_mul, mul_one, sub_self, Matrix.one_apply_ne hne]
  · have hik : i = k := Fin.ext heq.symm
    rw [ite_eq_left heq.le, ite_eq_right (by omega : ¬ (k : ℕ) + 1 ≤ (i : ℕ)), heq,
      Nat.add_sub_cancel_left, pow_one, Units.inv_mul, sub_zero, Matrix.one_apply,
      ite_eq_left hik]
  · have hne : i ≠ k := fun h => by rw [h] at hgt; exact lt_irrefl _ hgt
    rw [ite_eq_right (by omega : ¬ (k : ℕ) ≤ (i : ℕ)),
      ite_eq_right (by omega : ¬ (k : ℕ) + 1 ≤ (i : ℕ)), zero_mul, sub_zero,
      Matrix.one_apply_ne hne]

/-! ### The elementary reduced Burau matrices -/

/-- The pairings of the `i`-th Burau row against all the Burau columns. This is the row in which
the reduced Burau matrix of `TauCeti.BraidGroup.sigma i` differs from the identity. -/
def reducedBurauRow (t : R) (i : Fin (n - 1)) : Fin (n - 1) → R :=
  fun j => burauRow R i ⬝ᵥ burauCol t j

/-- Pairing a Burau row against the Burau columns is what multiplying into
`TauCeti.KnotTheory.burauColMatrix` computes. -/
theorem burauRow_vecMul_burauColMatrix (t : R) (i : Fin (n - 1)) :
    burauRow R i ᵥ* burauColMatrix n t = reducedBurauRow t i :=
  (rfl)

/-- The diagonal value of `TauCeti.KnotTheory.reducedBurauRow` is `t + 1`. -/
@[simp]
theorem reducedBurauRow_self (t : R) (i : Fin (n - 1)) : reducedBurauRow t i i = t + 1 :=
  burauRow_dotProduct_burauCol_self t i

/-- The value of `TauCeti.KnotTheory.reducedBurauRow` just above the diagonal is `-t`. -/
theorem reducedBurauRow_of_succ (t : R) {i j : Fin (n - 1)} (h : (i : ℕ) + 1 = j) :
    reducedBurauRow t i j = -t :=
  burauRow_dotProduct_burauCol_of_succ t h

/-- The value of `TauCeti.KnotTheory.reducedBurauRow` just below the diagonal is `-1`. -/
theorem reducedBurauRow_of_succ_rev (t : R) {i j : Fin (n - 1)} (h : (j : ℕ) + 1 = i) :
    reducedBurauRow t i j = -1 :=
  burauRow_dotProduct_burauCol_of_succ_rev t h

/-- Away from the diagonal and its two neighbours `TauCeti.KnotTheory.reducedBurauRow` vanishes. -/
theorem reducedBurauRow_of_not_adjacent (t : R) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) : reducedBurauRow t i j = 0 :=
  burauRow_dotProduct_burauCol_of_not_adjacent t h

/-- The reduced Burau matrix of the elementary braid `TauCeti.BraidGroup.sigma i` at the parameter
`t`: the identity outside the `i`-th row, which is `(…, 1, -t, t, …)` with `-t` on the diagonal. -/
def reducedBurauMatrix (t : R) (i : Fin (n - 1)) : Matrix (Fin (n - 1)) (Fin (n - 1)) R :=
  RankOneMatrix.family (fun i => Pi.single i 1) (reducedBurauRow t) i

/-- The defining formula for an elementary reduced Burau matrix: it differs from the identity by
the rank-one matrix `vecMulVec (Pi.single i 1) (reducedBurauRow t i)`, supported in the `i`-th
row. -/
theorem reducedBurauMatrix_def (t : R) (i : Fin (n - 1)) :
    reducedBurauMatrix t i = 1 - vecMulVec (Pi.single i 1) (reducedBurauRow t i) := by
  rw [reducedBurauMatrix, RankOneMatrix.family_def]

/-- The entries of an elementary reduced Burau matrix. -/
theorem reducedBurauMatrix_apply (t : R) (i a b : Fin (n - 1)) :
    reducedBurauMatrix t i a b =
      (if a = b then 1 else 0) - (if a = i then 1 else 0) * reducedBurauRow t i b := by
  rw [reducedBurauMatrix_def, Matrix.sub_apply, vecMulVec_apply, Matrix.one_apply,
    Pi.single_apply]

/-- Outside its `i`-th row an elementary reduced Burau matrix has the rows of the identity. -/
theorem reducedBurauMatrix_apply_of_ne (t : R) {i a : Fin (n - 1)} (h : a ≠ i) (b : Fin (n - 1)) :
    reducedBurauMatrix t i a b = if a = b then 1 else 0 := by
  rw [reducedBurauMatrix_apply, ite_eq_right h, zero_mul, sub_zero]

/-- The diagonal entry of an elementary reduced Burau matrix in its nontrivial row is `-t`. -/
@[simp]
theorem reducedBurauMatrix_apply_self (t : R) (i : Fin (n - 1)) :
    reducedBurauMatrix t i i i = -t := by
  rw [reducedBurauMatrix_apply, reducedBurauRow_self]
  simp

/-- The entry just above the diagonal in the nontrivial row of an elementary reduced Burau matrix
is `t`. -/
theorem reducedBurauMatrix_apply_succ (t : R) {i j : Fin (n - 1)} (h : (i : ℕ) + 1 = j) :
    reducedBurauMatrix t i i j = t := by
  have hne : i ≠ j := fun hij => by rw [hij] at h; omega
  rw [reducedBurauMatrix_apply, reducedBurauRow_of_succ t h, ite_eq_right hne]
  simp

/-- The entry just below the diagonal in the nontrivial row of an elementary reduced Burau matrix
is `1`. -/
theorem reducedBurauMatrix_apply_succ_rev (t : R) {i j : Fin (n - 1)} (h : (j : ℕ) + 1 = i) :
    reducedBurauMatrix t i i j = 1 := by
  have hne : i ≠ j := fun hij => by rw [hij] at h; omega
  rw [reducedBurauMatrix_apply, reducedBurauRow_of_succ_rev t h, ite_eq_right hne]
  simp

/-- Away from the diagonal and its two neighbours the nontrivial row of an elementary reduced
Burau matrix vanishes. -/
theorem reducedBurauMatrix_apply_of_not_adjacent (t : R) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) : reducedBurauMatrix t i i j = 0 := by
  have hne : i ≠ j := fun hij => by rw [hij] at h; omega
  rw [reducedBurauMatrix_apply, reducedBurauRow_of_not_adjacent t h, ite_eq_right hne]
  simp

/-- The determinant of an elementary reduced Burau matrix is `-t`, as for the unreduced one. -/
@[simp]
theorem det_reducedBurauMatrix (t : R) (i : Fin (n - 1)) : (reducedBurauMatrix t i).det = -t := by
  rw [reducedBurauMatrix, RankOneMatrix.det_family, dotProduct_single_one,
    reducedBurauRow_self]
  ring

/-! ### The reduced matrices are the restriction of the unreduced ones -/

/-- The general form of `TauCeti.KnotTheory.burauMatrix_mul_burauColMatrix`, stated for an
arbitrary multiple of the rank-one part so that it covers the elementary Burau matrix and its
inverse at once. -/
private theorem one_sub_smul_vecMulVec_mul_burauColMatrix (t : R) (i : Fin (n - 1)) (a : R) :
    (1 - a • vecMulVec (burauCol t i) (burauRow R i)) * burauColMatrix n t =
      burauColMatrix n t * (1 - a • vecMulVec (Pi.single i 1) (reducedBurauRow t i)) := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, vecMulVec_mul, mul_vecMulVec, burauRow_vecMul_burauColMatrix,
    burauColMatrix_mulVec_single]

/-- **An elementary Burau matrix restricts to the elementary reduced Burau matrix** on the span of
the Burau columns. -/
theorem burauMatrix_mul_burauColMatrix (t : R) (i : Fin (n - 1)) :
    burauMatrix t i * burauColMatrix n t = burauColMatrix n t * reducedBurauMatrix t i := by
  rw [reducedBurauMatrix_def, ← one_smul R (vecMulVec (Pi.single i (1 : R)) (reducedBurauRow t i)),
    ← one_sub_smul_vecMulVec_mul_burauColMatrix, burauMatrix_def, one_smul]

/-- The inverse of an elementary Burau matrix restricts to
`1 - t⁻¹ • vecMulVec (Pi.single i 1) (reducedBurauRow t i)`. -/
theorem inv_burauMatrix_mul_burauColMatrix (t : Rˣ) (i : Fin (n - 1)) :
    (burauMatrix (t : R) i)⁻¹ * burauColMatrix n (t : R) =
      burauColMatrix n (t : R) *
        (1 - ((t⁻¹ : Rˣ) : R) • vecMulVec (Pi.single i 1) (reducedBurauRow (t : R) i)) := by
  rw [inv_burauMatrix, one_sub_smul_vecMulVec_mul_burauColMatrix]

/-- Multiplication by the matrix of Burau columns is injective, by
`TauCeti.KnotTheory.burauCoordMatrix_mul_burauColMatrix`. -/
theorem eq_of_burauColMatrix_mul_eq {t : Rˣ} {X Y : Matrix (Fin (n - 1)) (Fin (n - 1)) R}
    (h : burauColMatrix n (t : R) * X = burauColMatrix n (t : R) * Y) : X = Y := by
  have hX := congrArg (fun M => burauCoordMatrix n t * M) h
  simpa only [← Matrix.mul_assoc, burauCoordMatrix_mul_burauColMatrix, Matrix.one_mul] using hX

/-! ### The braid relations, the inverse and the Hecke relation -/

private theorem reducedBurauSelfPairing (t : R) (i : Fin (n - 1)) :
    reducedBurauRow t i ⬝ᵥ Pi.single i 1 = t + 1 := by
  rw [dotProduct_single_one, reducedBurauRow_self]

private theorem reducedBurauDistantPairings (t : R) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    reducedBurauRow t i ⬝ᵥ Pi.single j 1 = 0 ∧
      reducedBurauRow t j ⬝ᵥ Pi.single i 1 = 0 := by
  rw [dotProduct_single_one, dotProduct_single_one, reducedBurauRow_of_not_adjacent t h,
    reducedBurauRow_of_not_adjacent t h.symm]
  exact ⟨rfl, rfl⟩

private theorem reducedBurauAdjacentPairings (t : R) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 1 = j) :
    reducedBurauRow t i ⬝ᵥ Pi.single j 1 = -t ∧
      reducedBurauRow t j ⬝ᵥ Pi.single i 1 = -1 := by
  rw [dotProduct_single_one, dotProduct_single_one, reducedBurauRow_of_succ t h,
    reducedBurauRow_of_succ_rev t h]
  exact ⟨rfl, rfl⟩

/-- **The distant commutation relation** for the elementary reduced Burau matrices. -/
theorem reducedBurauMatrix_mul_comm (t : R) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    reducedBurauMatrix t i * reducedBurauMatrix t j =
      reducedBurauMatrix t j * reducedBurauMatrix t i :=
  RankOneMatrix.family_mul_comm (fun i => Pi.single i (1 : R)) (reducedBurauRow t)
    (reducedBurauDistantPairings t h).1 (reducedBurauDistantPairings t h).2

/-- **The braid relation** for the elementary reduced Burau matrices. -/
theorem reducedBurauMatrix_braid (t : R) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    reducedBurauMatrix t i * reducedBurauMatrix t j * reducedBurauMatrix t i =
      reducedBurauMatrix t j * reducedBurauMatrix t i * reducedBurauMatrix t j :=
  RankOneMatrix.family_braid_or t (fun i => Pi.single i (1 : R)) (reducedBurauRow t)
    (reducedBurauSelfPairing t) (reducedBurauAdjacentPairings t) h

/-- **The quadratic relation** for the elementary reduced Burau matrices, equivalently
`(x - 1) * (x + t) = 0`: with the braid relations this is the Iwahori-Hecke relation in the
normalisation with eigenvalues `1` and `-t`, so the reduced Burau representation factors through a
Hecke algebra of type `A`. -/
theorem reducedBurauMatrix_mul_self (t : R) (i : Fin (n - 1)) :
    reducedBurauMatrix t i * reducedBurauMatrix t i =
      (1 - t) • reducedBurauMatrix t i + t • 1 :=
  RankOneMatrix.family_mul_self t (fun i => Pi.single i (1 : R)) (reducedBurauRow t) i
    (reducedBurauSelfPairing t i)

/-! ### The reduced Burau representation -/

/-- An elementary reduced Burau matrix as an element of the general linear group, with inverse
`1 - t⁻¹ • vecMulVec (Pi.single i 1) (reducedBurauRow t i)`. -/
def reducedBurauGL (t : Rˣ) (i : Fin (n - 1)) : GL (Fin (n - 1)) R :=
  RankOneMatrix.unit t (fun i => Pi.single i (1 : R)) (reducedBurauRow (t : R))
    (reducedBurauSelfPairing (t : R)) i

/-- The matrix underlying `TauCeti.KnotTheory.reducedBurauGL`. -/
@[simp]
theorem coe_reducedBurauGL (t : Rˣ) (i : Fin (n - 1)) :
    (reducedBurauGL t i : Matrix (Fin (n - 1)) (Fin (n - 1)) R) = reducedBurauMatrix (t : R) i :=
  by rw [reducedBurauGL, RankOneMatrix.coe_unit, reducedBurauMatrix]

/-- The nonsingular inverse of an elementary reduced Burau matrix. -/
@[simp]
theorem inv_reducedBurauMatrix (t : Rˣ) (i : Fin (n - 1)) :
    (reducedBurauMatrix (t : R) i)⁻¹ =
      1 - ((t⁻¹ : Rˣ) : R) • vecMulVec (Pi.single i 1) (reducedBurauRow (t : R) i) :=
  RankOneMatrix.inv_family t (fun i => Pi.single i (1 : R)) (reducedBurauRow (t : R)) i
    (reducedBurauSelfPairing (t : R) i)

/-- **The reduced Burau representation** of the braid group on `n` strands at a unit `t`, sending
the elementary braid `sigma i` to `TauCeti.KnotTheory.reducedBurauGL t i`. -/
def reducedBurau (n : ℕ) (t : Rˣ) : BraidGroup n →* GL (Fin (n - 1)) R :=
  RankOneMatrix.representation n t (fun i => Pi.single i (1 : R)) (reducedBurauRow (t : R))
    (reducedBurauSelfPairing (t : R)) (reducedBurauDistantPairings (t : R))
    (reducedBurauAdjacentPairings (t : R))

/-- The reduced Burau representation takes an elementary braid to the elementary reduced Burau
matrix. -/
@[simp]
theorem reducedBurau_sigma (t : Rˣ) (i : Fin (n - 1)) :
    reducedBurau n t (BraidGroup.sigma i) = (reducedBurauGL t i : GL (Fin (n - 1)) R) :=
  RankOneMatrix.representation_sigma n t (fun i => Pi.single i (1 : R))
    (reducedBurauRow (t : R)) (reducedBurauSelfPairing (t : R))
    (reducedBurauDistantPairings (t : R)) (reducedBurauAdjacentPairings (t : R)) i

/-- The determinant of the reduced Burau matrix of a braid is `-t` raised to its exponent sum, as
for the unreduced representation. -/
theorem det_reducedBurau (t : Rˣ) (b : BraidGroup n) :
    Matrix.GeneralLinearGroup.det (reducedBurau n t b : GL (Fin (n - 1)) R) =
      (-t) ^ Multiplicative.toAdd (ArtinGroup.exponentSum (CoxeterMatrix.A (n - 1)) b) :=
  RankOneMatrix.det_representation n t (fun i => Pi.single i (1 : R))
    (reducedBurauRow (t : R)) (reducedBurauSelfPairing (t : R))
    (reducedBurauDistantPairings (t : R)) (reducedBurauAdjacentPairings (t : R)) b

/-- **The reduced Burau representation is the restriction of the unreduced one** to the span of the
Burau columns. -/
theorem burau_mul_burauColMatrix (t : Rˣ) (b : BraidGroup n) :
    (burau n t b : Matrix (Fin n) (Fin n) R) * burauColMatrix n (t : R) =
      burauColMatrix n (t : R) *
        (reducedBurau n t b : Matrix (Fin (n - 1)) (Fin (n - 1)) R) := by
  refine BraidGroup.sigma_induction_on
    (p := fun b => (burau n t b : Matrix (Fin n) (Fin n) R) * burauColMatrix n (t : R) =
      burauColMatrix n (t : R) *
        (reducedBurau n t b : Matrix (Fin (n - 1)) (Fin (n - 1)) R)) b
    (fun i => by
      simp only [burau_sigma, coe_burauGL, reducedBurau_sigma, coe_reducedBurauGL]
      exact burauMatrix_mul_burauColMatrix (t : R) i) ?_ ?_ ?_
  · rw [map_one, map_one, Units.val_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  · intro b b' hb hb'
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, hb', ← Matrix.mul_assoc,
      hb, Matrix.mul_assoc]
  · intro b hb
    have hM : ((burau n t b⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *
        ((burau n t b : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 := by
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    have hRed : ((reducedBurau n t b : GL (Fin (n - 1)) R) :
          Matrix (Fin (n - 1)) (Fin (n - 1)) R) *
        ((reducedBurau n t b⁻¹ : GL (Fin (n - 1)) R) :
          Matrix (Fin (n - 1)) (Fin (n - 1)) R) = 1 := by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    calc ((burau n t b⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * burauColMatrix n (t : R)
        = ((burau n t b⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *
            (burauColMatrix n (t : R) *
              ((reducedBurau n t b : GL (Fin (n - 1)) R) :
                Matrix (Fin (n - 1)) (Fin (n - 1)) R)) *
            ((reducedBurau n t b⁻¹ : GL (Fin (n - 1)) R) :
              Matrix (Fin (n - 1)) (Fin (n - 1)) R) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hRed, Matrix.mul_one]
      _ = ((burau n t b⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *
            (((burau n t b : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *
              burauColMatrix n (t : R)) *
            ((reducedBurau n t b⁻¹ : GL (Fin (n - 1)) R) :
              Matrix (Fin (n - 1)) (Fin (n - 1)) R) := by rw [hb]
      _ = burauColMatrix n (t : R) *
            ((reducedBurau n t b⁻¹ : GL (Fin (n - 1)) R) :
              Matrix (Fin (n - 1)) (Fin (n - 1)) R) := by
          rw [← Matrix.mul_assoc, hM, Matrix.one_mul]

/-- Conversely, the reduced Burau matrix of a braid is read off from the unreduced one in the basis
of Burau columns. -/
theorem reducedBurau_eq (t : Rˣ) (b : BraidGroup n) :
    (reducedBurau n t b : Matrix (Fin (n - 1)) (Fin (n - 1)) R) =
      burauCoordMatrix n t * (burau n t b : Matrix (Fin n) (Fin n) R) *
        burauColMatrix n (t : R) := by
  rw [Matrix.mul_assoc, burau_mul_burauColMatrix, ← Matrix.mul_assoc,
    burauCoordMatrix_mul_burauColMatrix, Matrix.one_mul]

/-! ### The reduced Burau matrices on two and three strands -/

/-- On two strands the reduced Burau representation is one-dimensional, sending the single
elementary braid to `-t`. -/
theorem reducedBurauMatrix_two (t : R) (i : Fin (2 - 1)) :
    reducedBurauMatrix t i = !![-t] := by
  ext a b
  fin_cases i
  fin_cases a
  fin_cases b
  simp [reducedBurauMatrix_apply_self]

/-- The reduced Burau matrix of the first elementary braid on three strands. -/
theorem reducedBurauMatrix_three_zero (t : R) :
    reducedBurauMatrix t (0 : Fin (3 - 1)) = !![-t, t; 0, 1] := by
  rw [Matrix.eta_fin_two (reducedBurauMatrix t (0 : Fin (3 - 1))),
    reducedBurauMatrix_apply_self, reducedBurauMatrix_apply_succ t (by decide),
    reducedBurauMatrix_apply_of_ne t (show (1 : Fin (3 - 1)) ≠ 0 by decide),
    reducedBurauMatrix_apply_of_ne t (show (1 : Fin (3 - 1)) ≠ 0 by decide)]
  norm_num

/-- The reduced Burau matrix of the second elementary braid on three strands. -/
theorem reducedBurauMatrix_three_one (t : R) :
    reducedBurauMatrix t (1 : Fin (3 - 1)) = !![1, 0; 1, -t] := by
  rw [Matrix.eta_fin_two (reducedBurauMatrix t (1 : Fin (3 - 1))),
    reducedBurauMatrix_apply_of_ne t (show (0 : Fin (3 - 1)) ≠ 1 by decide),
    reducedBurauMatrix_apply_of_ne t (show (0 : Fin (3 - 1)) ≠ 1 by decide),
    reducedBurauMatrix_apply_succ_rev t (by decide), reducedBurauMatrix_apply_self]
  norm_num

end CommRing

end TauCeti.KnotTheory
