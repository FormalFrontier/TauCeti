/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Burau.Basic
public import TauCeti.KnotTheory.Burau.RankOneMatrix

/-!
# The reduced Burau representation of the braid group

The unreduced Burau representation `TauCeti.KnotTheory.burau` of `TauCeti.BraidGroup n`, built in
`TauCeti/KnotTheory/Burau/Basic.lean`, is reducible: the row vector `(1, t, …, t ^ (n - 1))` is
fixed by every Burau matrix, so its kernel is an invariant submodule. That kernel contains the
`n - 1` Burau columns `burauCol t i = t • e i - e (i + 1)`, and at a unit `t` they form a basis of
that kernel. The braid group acts on their span, and the matrices of that action in the basis of
Burau columns form the **reduced Burau representation**
`TauCeti.KnotTheory.reducedBurau`, of rank `n - 1`. Geometrically the unreduced representation is
the first homology of the infinite cyclic cover of the `n`-punctured disc *relative* to the fibre
over a basepoint, and the reduced one is the absolute first homology of that cover.

The construction here is deliberately basis-first, and reuses the pairings of the unreduced file.
The calculus those pairings feed is set up once, for an arbitrary family of matrices
`1 - u i ⊗ v i` over an arbitrary index type, in
`TauCeti/LinearAlgebra/Matrix/RankOne.lean`: the product of two members, the braid relations, the
quadratic relation, the inverse, and the determinant. The braid-group representation a family with
the Burau pairings defines is in `TauCeti/KnotTheory/Burau/RankOneMatrix.lean`. Writing
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

Three theorems keep the reduction honest. The Burau columns really do lie in the invariant submodule
(`TauCeti.KnotTheory.geom_vecMul_burauColMatrix`: the geometric covector annihilates them), and
they really are independent: `TauCeti.KnotTheory.burauCoordMatrix_mul_burauColMatrix` exhibits an
explicit left inverse of `burauColMatrix`, built from the powers of `t⁻¹`. Conversely,
`TauCeti.KnotTheory.burauColMatrix_mulVec_burauCoordMatrix_mulVec` reconstructs every vector in the
geometric kernel from those coordinates. The left inverse also recovers the reduced matrix of a
braid from the unreduced one
(`TauCeti.KnotTheory.reducedBurau_eq`): the reduced matrix is canonically computed from the
unreduced matrix using the explicit left inverse.

Finally, `TauCeti.KnotTheory.reducedBurauMatrix_mul_self` records the quadratic relation
`x * x = (1 - t) • x + t • 1`, that is, `(x - 1) * (x + t) = 0`: together with the braid relations
this is the Iwahori-Hecke quadratic relation in the normalisation with eigenvalues `1` and `-t`.
The comparison with the Alexander polynomial of `TauCeti/KnotTheory/Alexander.lean` needs the
closure of a braid to a link and is not built here.

This is the Burau route of the "knot polynomials, each a project in itself, with several algorithms
apiece" bullet of Layer 4 ("knot theory, done properly") of the GeometricTopology roadmap.

## Main definitions

* `TauCeti.KnotTheory.burauColMatrix`: the `n × (n - 1)` matrix whose columns are the Burau
  columns, that is, the inclusion of the invariant submodule they span.
* `TauCeti.KnotTheory.burauCoordMatrix`: an explicit left inverse of `burauColMatrix` at a unit
  `t`, so the Burau columns are independent and span a free rank `n - 1` direct summand.
* `TauCeti.KnotTheory.reducedBurauRow`: the pairings of one Burau row against all Burau columns.
* `TauCeti.KnotTheory.reducedBurauMatrix`: the reduced Burau matrix of an elementary braid.
* `TauCeti.KnotTheory.reducedBurauGL` and `TauCeti.KnotTheory.reducedBurau`: the reduced Burau
  representation `BraidGroup n →* GL (Fin (n - 1)) R`.

## Main results

* `TauCeti.KnotTheory.geom_vecMul_burauColMatrix` and
  `TauCeti.KnotTheory.burauColMatrix_mulVec_burauCoordMatrix_mulVec`: the Burau columns lie in and
  span the geometric kernel.
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


section Ring

variable [Ring R]

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
@[simp]
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

private theorem burauCoordMatrix_mulVec_eq_sum_range (m : ℕ) (t : Rˣ)
    (x : Fin (m + 1) → R) (i : Fin m) :
    (burauCoordMatrix (m + 1) t *ᵥ x) i =
      ∑ a ∈ Finset.range ((i : ℕ) + 1),
        ((t⁻¹ : Rˣ) : R) ^ ((i : ℕ) + 1 - a) * x (Fin.ofNat (m + 1) a) := by
  rw [Matrix.mulVec, dotProduct]
  simp only [burauCoordMatrix_apply, ite_mul, zero_mul]
  calc
    _ = ∑ a ∈ Finset.range (m + 1), if a ≤ (i : ℕ) then
        ((t⁻¹ : Rˣ) : R) ^ ((i : ℕ) + 1 - a) * x (Fin.ofNat (m + 1) a) else 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro a ha
      simp [Fin.ofNat_eq_cast]
    _ = _ := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext a
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      · intro a ha
        rfl

private theorem burauColMatrix_mulVec_zero (m : ℕ) (hm : 0 < m) (t : R) (c : Fin m → R) :
    (burauColMatrix (m + 1) t *ᵥ c) 0 = t * c ⟨0, hm⟩ := by
  rw [Matrix.mulVec, dotProduct]
  simp only [burauColMatrix_apply, burauCol_apply]
  simp only [sub_mul, ite_mul, zero_mul, one_mul, Finset.sum_sub_distrib]
  have heq (i : Fin m) : (0 : Fin (m + 1)) = BraidGroup.strand (n := m + 1) i ↔
      ⟨0, hm⟩ = i := by
    simp only [Fin.ext_iff, BraidGroup.val_strand, Fin.val_zero]
  have hsucc (i : Fin m) : (0 : Fin (m + 1)) ≠ BraidGroup.strandSucc (n := m + 1) i := by
    simp only [ne_eq, Fin.ext_iff, BraidGroup.val_strandSucc, Fin.val_zero]
    omega
  simp_rw [heq]
  simp [hsucc]

private theorem burauColMatrix_mulVec_succ (m : ℕ) (t : R) (c : Fin m → R) (i : Fin m) :
    (burauColMatrix (m + 1) t *ᵥ c) i.succ =
      (if h : (i : ℕ) + 1 < m then t * c ⟨(i : ℕ) + 1, h⟩ else 0) - c i := by
  rw [Matrix.mulVec, dotProduct]
  simp only [burauColMatrix_apply, burauCol_apply]
  simp only [sub_mul, ite_mul, zero_mul, one_mul, Finset.sum_sub_distrib]
  have heq (j : Fin m) : i.succ = BraidGroup.strandSucc (n := m + 1) j ↔ i = j := by
    simp only [Fin.ext_iff, Fin.val_succ, BraidGroup.val_strandSucc]
    omega
  simp_rw [heq]
  by_cases h : (i : ℕ) + 1 < m
  · have hsucc (j : Fin m) : i.succ = BraidGroup.strand (n := m + 1) j ↔
        ⟨(i : ℕ) + 1, h⟩ = j := by
      simp only [Fin.ext_iff, Fin.val_succ, BraidGroup.val_strand]
    simp_rw [hsucc]
    simp [h]
  · have hsucc (j : Fin m) : i.succ ≠ BraidGroup.strand (n := m + 1) j := fun he =>
      h (by
        have he' := congrArg Fin.val he
        simp only [Fin.val_succ, BraidGroup.val_strand] at he'
        rw [he']
        exact j.isLt)
    simp [h, hsucc]

private theorem unit_mul_inv_pow_succ (t : Rˣ) (k : ℕ) :
    (t : R) * ((t⁻¹ : Rˣ) : R) ^ (k + 1) = ((t⁻¹ : Rˣ) : R) ^ k := by
  rw [pow_succ', ← mul_assoc, ← Units.val_mul]
  simp

private theorem burauCoordMatrix_mulVec_zero (m : ℕ) (hm : 0 < m) (t : Rˣ)
    (x : Fin (m + 1) → R) :
    (t : R) * (burauCoordMatrix (m + 1) t *ᵥ x) ⟨0, hm⟩ = x 0 := by
  rw [burauCoordMatrix_mulVec_eq_sum_range]
  simp only [zero_add, Finset.range_one, Fin.ofNat_eq_cast, Finset.sum_singleton, tsub_zero,
    pow_one, Fin.natCast_zero, Units.mul_inv_cancel_left]

private theorem burauCoordMatrix_mulVec_succ (m : ℕ) (t : Rˣ) (x : Fin (m + 1) → R)
    (i : Fin m) (h : (i : ℕ) + 1 < m) :
    (t : R) * (burauCoordMatrix (m + 1) t *ᵥ x) ⟨(i : ℕ) + 1, h⟩ -
      (burauCoordMatrix (m + 1) t *ᵥ x) i = x i.succ := by
  rw [burauCoordMatrix_mulVec_eq_sum_range, burauCoordMatrix_mulVec_eq_sum_range,
    Finset.sum_range_succ, mul_add]
  have hsum : (t : R) * ∑ a ∈ Finset.range ((i : ℕ) + 1),
        ((t⁻¹ : Rˣ) : R) ^ ((i : ℕ) + 1 + 1 - a) * x (Fin.ofNat (m + 1) a) =
      ∑ a ∈ Finset.range ((i : ℕ) + 1),
        ((t⁻¹ : Rˣ) : R) ^ ((i : ℕ) + 1 - a) * x (Fin.ofNat (m + 1) a) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← mul_assoc, show (i : ℕ) + 1 + 1 - a = ((i : ℕ) + 1 - a) + 1 by
      simp only [Finset.mem_range] at ha; omega, unit_mul_inv_pow_succ]
  rw [hsum]
  simp only [Fin.ofNat_eq_cast, add_tsub_cancel_left, pow_one, Units.mul_inv_cancel_left,
    add_sub_cancel_left]
  apply congrArg x
  apply Fin.ext
  simp

private theorem inv_pow_mul_pow (t : Rˣ) {a m : ℕ} (h : a ≤ m) :
    ((t⁻¹ : Rˣ) : R) ^ m * (t : R) ^ a = ((t⁻¹ : Rˣ) : R) ^ (m - a) := by
  exact congrArg Units.val (inv_pow_sub t h).symm

private theorem burauCoordMatrix_mulVec_last (m : ℕ) (t : Rˣ) (x : Fin (m + 2) → R)
    (hx : (fun k : Fin (m + 2) => (t : R) ^ (k : ℕ)) ⬝ᵥ x = 0) :
    -(burauCoordMatrix (m + 2) t *ᵥ x) (Fin.last m) = x (Fin.last (m + 1)) := by
  have hxsum : (∑ a ∈ Finset.range (m + 2),
      (t : R) ^ a * x (Fin.ofNat (m + 2) a)) = 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    simpa [dotProduct, Fin.ofNat_eq_cast] using hx
  rw [Finset.sum_range_succ] at hxsum
  have hscaled := congrArg (fun z : R => ((t⁻¹ : Rˣ) : R) ^ (m + 1) * z) hxsum
  rw [mul_add, mul_zero] at hscaled
  have hprefix : ((t⁻¹ : Rˣ) : R) ^ (m + 1) *
        ∑ a ∈ Finset.range (m + 1), (t : R) ^ a * x (Fin.ofNat (m + 2) a) =
      ∑ a ∈ Finset.range (m + 1),
        ((t⁻¹ : Rˣ) : R) ^ (m + 1 - a) * x (Fin.ofNat (m + 2) a) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have ha' : a ≤ m + 1 := (Finset.mem_range.mp ha).le
    rw [← mul_assoc, inv_pow_mul_pow t ha']
  rw [hprefix, ← mul_assoc, inv_pow_mul_pow t le_rfl, Nat.sub_self, pow_zero, one_mul] at hscaled
  rw [burauCoordMatrix_mulVec_eq_sum_range]
  simpa [Fin.ofNat_eq_cast] using neg_eq_of_add_eq_zero_right hscaled

/-- **The Burau columns span the kernel of the geometric covector**: every vector annihilated by
`(1, t, …, t ^ (n - 1))` is reconstructed from its `burauCoordMatrix` coordinates. Together with
`TauCeti.KnotTheory.burauCoordMatrix_mul_burauColMatrix`, this identifies the kernel with the free
module on `Fin (n - 1)`. -/
theorem burauColMatrix_mulVec_burauCoordMatrix_mulVec (n : ℕ) (t : Rˣ) (x : Fin n → R)
    (hx : (fun k : Fin n => (t : R) ^ (k : ℕ)) ⬝ᵥ x = 0) :
    burauColMatrix n (t : R) *ᵥ (burauCoordMatrix n t *ᵥ x) = x := by
  cases n with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ m =>
      cases m with
      | zero =>
          funext i
          fin_cases i
          simpa [Matrix.mulVec, dotProduct] using hx.symm
      | succ m =>
          funext a
          refine Fin.cases ?_ (fun i => ?_) a
          · rw [burauColMatrix_mulVec_zero (m + 1) (by omega), burauCoordMatrix_mulVec_zero]
          · rw [burauColMatrix_mulVec_succ]
            by_cases h : (i : ℕ) + 1 < m + 1
            · rw [dite_eq_left h, burauCoordMatrix_mulVec_succ _ _ _ _ h]
            · rw [dite_eq_right h]
              have hi : i = Fin.last m := by
                ext
                simp only [Fin.val_last]
                omega
              subst i
              rw [zero_sub, burauCoordMatrix_mulVec_last m t x hx]
              congr

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

/-! ### The reduced matrices are the restriction of the unreduced ones -/

/-- **An elementary Burau matrix restricts to the elementary reduced Burau matrix** on the span of
the Burau columns. -/
theorem burauMatrix_mul_burauColMatrix (t : R) (i : Fin (n - 1)) :
    burauMatrix t i * burauColMatrix n t = burauColMatrix n t * reducedBurauMatrix t i := by
  rw [burauMatrix_def, reducedBurauMatrix_def, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
    Matrix.mul_one, vecMulVec_mul, mul_vecMulVec, burauRow_vecMul_burauColMatrix,
    burauColMatrix_mulVec_single]

/-- Multiplication by the matrix of Burau columns is injective, by
`TauCeti.KnotTheory.burauCoordMatrix_mul_burauColMatrix`. -/
theorem eq_of_burauColMatrix_mul_eq {t : Rˣ} {X Y : Matrix (Fin (n - 1)) (Fin (n - 1)) R}
    (h : burauColMatrix n (t : R) * X = burauColMatrix n (t : R) * Y) : X = Y := by
  have hX := congrArg (fun M => burauCoordMatrix n t * M) h
  simpa only [← Matrix.mul_assoc, burauCoordMatrix_mul_burauColMatrix, Matrix.one_mul] using hX

end Ring

section CommRing

variable [CommRing R]

/-- The determinant of an elementary reduced Burau matrix is `-t`, as for the unreduced one. -/
@[simp]
theorem det_reducedBurauMatrix (t : R) (i : Fin (n - 1)) : (reducedBurauMatrix t i).det = -t := by
  rw [reducedBurauMatrix, RankOneMatrix.det_family, dotProduct_single_one,
    reducedBurauRow_self]
  ring

/-- The general form of `TauCeti.KnotTheory.burauMatrix_mul_burauColMatrix`, stated for an
arbitrary multiple of the rank-one part so that it covers the elementary Burau matrix and its
inverse at once. -/
private theorem one_sub_smul_vecMulVec_mul_burauColMatrix (t : R) (i : Fin (n - 1)) (a : R) :
    (1 - a • vecMulVec (burauCol t i) (burauRow R i)) * burauColMatrix n t =
      burauColMatrix n t * (1 - a • vecMulVec (Pi.single i 1) (reducedBurauRow t i)) := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, vecMulVec_mul, mul_vecMulVec, burauRow_vecMul_burauColMatrix,
    burauColMatrix_mulVec_single]

/-- The inverse of an elementary Burau matrix restricts to
`1 - t⁻¹ • vecMulVec (Pi.single i 1) (reducedBurauRow t i)`. -/
theorem inv_burauMatrix_mul_burauColMatrix (t : Rˣ) (i : Fin (n - 1)) :
    (burauMatrix (t : R) i)⁻¹ * burauColMatrix n (t : R) =
      burauColMatrix n (t : R) *
        (1 - ((t⁻¹ : Rˣ) : R) • vecMulVec (Pi.single i 1) (reducedBurauRow (t : R) i)) := by
  rw [inv_burauMatrix, one_sub_smul_vecMulVec_mul_burauColMatrix]

/-! ### The braid relations, the inverse and the Hecke relation -/

private theorem reducedBurauSelfPairing (t : R) (i : Fin (n - 1)) :
    reducedBurauRow t i ⬝ᵥ Pi.single i 1 = t + 1 := by
  rw [dotProduct_single_one, reducedBurauRow_self]

/-- **The distant commutation relation** for the elementary reduced Burau matrices. -/
theorem reducedBurauMatrix_mul_comm (t : R) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    reducedBurauMatrix t i * reducedBurauMatrix t j =
      reducedBurauMatrix t j * reducedBurauMatrix t i :=
  RankOneMatrix.family_mul_comm (fun i => Pi.single i (1 : R)) (reducedBurauRow t)
    (by rw [dotProduct_single_one, reducedBurauRow_of_not_adjacent t h])
    (by rw [dotProduct_single_one, reducedBurauRow_of_not_adjacent t h.symm])

/-- **The braid relation** for the elementary reduced Burau matrices. -/
theorem reducedBurauMatrix_braid (t : R) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    reducedBurauMatrix t i * reducedBurauMatrix t j * reducedBurauMatrix t i =
      reducedBurauMatrix t j * reducedBurauMatrix t i * reducedBurauMatrix t j :=
  RankOneMatrix.family_braid_of_adjacent t (fun i => Pi.single i (1 : R)) (reducedBurauRow t)
    (reducedBurauSelfPairing t)
    (fun h => by rw [dotProduct_single_one, reducedBurauRow_of_succ t h])
    (fun h => by rw [dotProduct_single_one, reducedBurauRow_of_succ_rev t h]) h

/-- **The quadratic relation** for the elementary reduced Burau matrices, equivalently
`(x - 1) * (x + t) = 0`. This is the Iwahori-Hecke quadratic relation in the normalisation with
eigenvalues `1` and `-t`. -/
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
    (reducedBurauSelfPairing (t : R))
    (fun h => by rw [dotProduct_single_one, reducedBurauRow_of_not_adjacent (t : R) h])
    (fun h => by rw [dotProduct_single_one, reducedBurauRow_of_succ (t : R) h])
    (fun h => by rw [dotProduct_single_one, reducedBurauRow_of_succ_rev (t : R) h])

/-- The reduced Burau representation takes an elementary braid to the elementary reduced Burau
matrix. -/
@[simp]
theorem reducedBurau_sigma (t : Rˣ) (i : Fin (n - 1)) :
    reducedBurau n t (BraidGroup.sigma i) = (reducedBurauGL t i : GL (Fin (n - 1)) R) :=
  RankOneMatrix.representation_sigma n t (fun i => Pi.single i (1 : R))
    (reducedBurauRow (t : R)) (reducedBurauSelfPairing (t : R))
    (fun h => by rw [dotProduct_single_one, reducedBurauRow_of_not_adjacent (t : R) h])
    (fun h => by rw [dotProduct_single_one, reducedBurauRow_of_succ (t : R) h])
    (fun h => by rw [dotProduct_single_one, reducedBurauRow_of_succ_rev (t : R) h]) i

/-- The determinant of the reduced Burau matrix of a braid is `-t` raised to its exponent sum, as
for the unreduced representation. -/
theorem det_reducedBurau (t : Rˣ) (b : BraidGroup n) :
    Matrix.GeneralLinearGroup.det (reducedBurau n t b : GL (Fin (n - 1)) R) =
      (-t) ^ Multiplicative.toAdd (ArtinGroup.exponentSum (CoxeterMatrix.A (n - 1)) b) :=
  RankOneMatrix.det_representation n t (fun i => Pi.single i (1 : R))
    (reducedBurauRow (t : R)) (reducedBurauSelfPairing (t : R))
    (fun h => by rw [dotProduct_single_one, reducedBurauRow_of_not_adjacent (t : R) h])
    (fun h => by rw [dotProduct_single_one, reducedBurauRow_of_succ (t : R) h])
    (fun h => by rw [dotProduct_single_one, reducedBurauRow_of_succ_rev (t : R) h]) b

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
    reducedBurauMatrix_apply_of_ne t (by decide),
    reducedBurauMatrix_apply_of_ne t (by decide)]
  norm_num

/-- The reduced Burau matrix of the second elementary braid on three strands. -/
theorem reducedBurauMatrix_three_one (t : R) :
    reducedBurauMatrix t (1 : Fin (3 - 1)) = !![1, 0; 1, -t] := by
  rw [Matrix.eta_fin_two (reducedBurauMatrix t (1 : Fin (3 - 1))),
    reducedBurauMatrix_apply_of_ne t (by decide),
    reducedBurauMatrix_apply_of_ne t (by decide),
    reducedBurauMatrix_apply_succ_rev t (by decide), reducedBurauMatrix_apply_self]
  norm_num

end CommRing

end TauCeti.KnotTheory
