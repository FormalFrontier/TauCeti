/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.KnotTheory.Burau.Basic
public import TauCeti.KnotTheory.Burau.OneSubVecMulVec

/-!
# The reduced Burau representation

The unreduced Burau representation on `Rⁿ` fixes the row covector
`(1, t, ..., t ^ (n - 1))`. Its kernel is consequently an invariant submodule of rank `n - 1`;
the action on that kernel is the **reduced Burau representation**. This file constructs the
invariant kernel and the reduced representation over an arbitrary commutative ring at an arbitrary
unit, both in the canonical tail-coordinate system and in the basis of Burau columns. The latter
is named with the suffix `BurauCol` to distinguish the two coordinate systems.

For a braid on `n + 1` strands, the coefficient of the zeroth coordinate in the invariant
covector is `1`. The kernel is therefore canonically free on the remaining `n` coordinates:
`TauCeti.KnotTheory.reducedBurauSpaceEquiv` sends `x : Fin n → R` to the vector whose tail is
`x` and whose zeroth coordinate is the unique value making the weighted coordinate sum vanish.
Transporting the kernel action across this equivalence gives
`TauCeti.KnotTheory.reducedBurau`, a representation on `Fin n → R` ready for matrix and
determinant computations.

In the basis of Burau columns `burauCol t i = t • e i - e (i + 1)`, the action of an elementary
braid is given by the elementary reduced Burau matrix
`TauCeti.KnotTheory.reducedBurauColMatrix t i`,
which is a rank-one perturbation `1 - vecMulVec (Pi.single i 1) (reducedBurauColRow t i)`. The
pairings `burauRow R i ⬝ᵥ burauCol t j` feed the rank-one calculus of
`TauCeti/LinearAlgebra/Matrix/OneSubVecMulVec.lean`, yielding the braid relations, the inverse,
the determinant `-t`, and the Iwahori-Hecke quadratic relation.

This is the reduced-representation prerequisite for the braid route to the Alexander polynomial
in Layer 4 of the geometric-topology roadmap.

## Main definitions

* `TauCeti.KnotTheory.geometricCovector`: the invariant covector with coordinates `t ^ i`.
* `TauCeti.KnotTheory.ReducedBurauSpace`: its kernel.
* `TauCeti.KnotTheory.reducedBurauSpaceEquiv`: the explicit equivalence
  `(Fin n → R) ≃ₗ ReducedBurauSpace (n + 1) t`.
* `TauCeti.KnotTheory.burauRepresentation`: the unreduced matrix representation read as a module
  representation.
* `TauCeti.KnotTheory.reducedBurauSubrepresentation`: its restriction to the invariant kernel.
* `TauCeti.KnotTheory.reducedBurau`: the reduced representation in free coordinates.
* `TauCeti.KnotTheory.reducedBurauCol`: the reduced matrix homomorphism in the basis of Burau
  columns.
* `TauCeti.KnotTheory.burauColMatrix`: the `n × (n - 1)` matrix of Burau columns.
* `TauCeti.KnotTheory.burauCoordMatrix`: an explicit left inverse of `burauColMatrix` at a unit `t`.
* `TauCeti.KnotTheory.reducedBurauColRow`: the pairings of one Burau row against all Burau columns.
* `TauCeti.KnotTheory.reducedBurauColMatrix`: the reduced Burau matrix of an elementary braid.
* `TauCeti.KnotTheory.reducedBurauColGL`: an elementary reduced Burau matrix in
  `GL (Fin (n - 1)) R`.

## Main results

* `TauCeti.KnotTheory.geom_vecMul_burauColMatrix_eq_zero` and
  `TauCeti.KnotTheory.burauColMatrix_mulVec_burauCoordMatrix_mulVec`: the Burau columns lie in and
  span the invariant kernel `reducedBurauSpace`.
* `TauCeti.KnotTheory.burauMatrix_mul_burauColMatrix`: the elementary Burau matrix restricts to the
  elementary reduced Burau matrix on the span of the Burau columns.
* `TauCeti.KnotTheory.burau_mul_burauColMatrix`: the corresponding intertwining identity for every
  braid.
* `TauCeti.KnotTheory.reducedBurau_apply_burauColMatrix_mulVec`: comparison of the Burau-column and
  tail-coordinate reduced representations.
* `TauCeti.KnotTheory.reducedBurauColMatrix_mul_comm` and
  `TauCeti.KnotTheory.reducedBurauColMatrix_braid`: the two braid relations for the reduced
  matrices.
* `TauCeti.KnotTheory.det_reducedBurauColMatrix`: the determinant of an elementary reduced Burau
  matrix is `-t`.
* `TauCeti.KnotTheory.reducedBurauColMatrix_mul_self`: the Iwahori-Hecke quadratic relation.
* `TauCeti.KnotTheory.reducedBurauColMatrix_two` and the two
  `TauCeti.KnotTheory.reducedBurauColMatrix_three_*` theorems: explicit reduced matrices on two
  and three strands.

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82,
  Princeton University Press (1974), Chapter 3.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapters 1
  and 6.
-/

public section

open Matrix

namespace TauCeti.KnotTheory

variable {R : Type*}

section CommSemiring

variable [CommSemiring R]

/-- The Burau-invariant covector on `Rⁿ`, with coordinates `(1, t, ..., t ^ (n - 1))`. -/
def geometricCovector (n : ℕ) (t : R) : (Fin n → R) →ₗ[R] R :=
  dotProductBilin R R fun i ↦ t ^ (i : ℕ)

/-- The invariant covector is the weighted sum of the coordinates. -/
@[simp]
theorem geometricCovector_apply (n : ℕ) (t : R) (x : Fin n → R) :
    geometricCovector n t x = ∑ i : Fin n, t ^ (i : ℕ) * x i := by
  rfl

/-- The invariant submodule carrying the reduced Burau representation: the kernel of the
geometric covector. -/
def reducedBurauSpace (n : ℕ) (t : R) : Submodule R (Fin n → R) :=
  LinearMap.ker (geometricCovector n t)

/-- The type underlying the invariant submodule `reducedBurauSpace n t`. -/
abbrev ReducedBurauSpace (n : ℕ) (t : R) : Type _ := reducedBurauSpace n t

/-- Membership in the reduced Burau space means that the weighted coordinate sum vanishes. -/
@[simp]
theorem mem_reducedBurauSpace_iff (n : ℕ) (t : R) (x : Fin n → R) :
    x ∈ reducedBurauSpace n t ↔ ∑ i : Fin n, t ^ (i : ℕ) * x i = 0 := by
  simp [reducedBurauSpace]

end CommSemiring

section Ring

variable [Ring R] {n : ℕ}

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
theorem geom_vecMul_burauColMatrix_eq_zero (n : ℕ) (t : R) :
    (fun k : Fin n => t ^ (k : ℕ)) ᵥ* burauColMatrix n t = 0 := by
  funext i
  rw [vecMul_burauColMatrix_apply, geom_dotProduct_burauCol_eq_zero, Pi.zero_apply]

/-- The coordinates of a vector of the span of the Burau columns in that basis: the `(i, a)` entry
is `t⁻¹ ^ (i + 1 - a)` for `a ≤ i`, and `0` otherwise. This is the explicit left inverse of
`TauCeti.KnotTheory.burauColMatrix` of
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
@[simp]
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
    have hexponent : (i : ℕ) + 1 + 1 - a = ((i : ℕ) + 1 - a) + 1 := by
      simp only [Finset.mem_range] at ha
      omega
    rw [← mul_assoc, hexponent, unit_mul_inv_pow_succ]
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
              exact congrArg x (Fin.succ_last m).symm

/-! ### The elementary reduced Burau matrices -/

/-- The pairings of the `i`-th Burau row against all the Burau columns. This is the row in which
the reduced Burau matrix in the Burau-column basis differs from the identity. -/
def reducedBurauColRow (t : R) (i : Fin (n - 1)) : Fin (n - 1) → R :=
  fun j => burauRow R i ⬝ᵥ burauCol t j

/-- Pairing a Burau row against the Burau columns is what multiplying into
`TauCeti.KnotTheory.burauColMatrix` computes. -/
theorem burauRow_vecMul_burauColMatrix (t : R) (i : Fin (n - 1)) :
    burauRow R i ᵥ* burauColMatrix n t = reducedBurauColRow t i :=
  (rfl)

/-- The diagonal value of `TauCeti.KnotTheory.reducedBurauColRow` is `t + 1`. -/
@[simp]
theorem reducedBurauColRow_self (t : R) (i : Fin (n - 1)) : reducedBurauColRow t i i = t + 1 :=
  burauRow_dotProduct_burauCol_self t i

/-- The value of `TauCeti.KnotTheory.reducedBurauColRow` just above the diagonal is `-t`. -/
theorem reducedBurauColRow_of_succ (t : R) {i j : Fin (n - 1)} (h : (i : ℕ) + 1 = j) :
    reducedBurauColRow t i j = -t :=
  burauRow_dotProduct_burauCol_of_succ t h

/-- The value of `TauCeti.KnotTheory.reducedBurauColRow` just below the diagonal is `-1`. -/
theorem reducedBurauColRow_of_succ_rev (t : R) {i j : Fin (n - 1)} (h : (j : ℕ) + 1 = i) :
    reducedBurauColRow t i j = -1 :=
  burauRow_dotProduct_burauCol_of_succ_rev t h

/-- Away from the diagonal and its two neighbours
`TauCeti.KnotTheory.reducedBurauColRow` vanishes. -/
theorem reducedBurauColRow_of_not_adjacent (t : R) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) : reducedBurauColRow t i j = 0 :=
  burauRow_dotProduct_burauCol_of_not_adjacent t h

/-- The reduced Burau matrix in the Burau-column basis of the elementary braid
`TauCeti.BraidGroup.sigma i`: the identity outside the `i`-th row, which is
`(…, 1, -t, t, …)` with `-t` on the diagonal. -/
def reducedBurauColMatrix (t : R) (i : Fin (n - 1)) : Matrix (Fin (n - 1)) (Fin (n - 1)) R :=
  1 - vecMulVec (Pi.single i 1) (reducedBurauColRow t i)

/-- The defining formula for an elementary reduced Burau matrix: it differs from the identity by
the rank-one matrix `vecMulVec (Pi.single i 1) (reducedBurauColRow t i)`, supported in the `i`-th
row. -/
theorem reducedBurauColMatrix_def (t : R) (i : Fin (n - 1)) :
    reducedBurauColMatrix t i = 1 - vecMulVec (Pi.single i 1) (reducedBurauColRow t i) :=
  (rfl)

/-- The entries of an elementary reduced Burau matrix. -/
theorem reducedBurauColMatrix_apply (t : R) (i a b : Fin (n - 1)) :
    reducedBurauColMatrix t i a b =
      (if a = b then 1 else 0) - (if a = i then 1 else 0) * reducedBurauColRow t i b := by
  rw [reducedBurauColMatrix_def, Matrix.sub_apply, vecMulVec_apply, Matrix.one_apply,
    Pi.single_apply]

/-- Outside its `i`-th row an elementary reduced Burau matrix has the rows of the identity. -/
theorem reducedBurauColMatrix_apply_of_ne (t : R) {i a : Fin (n - 1)} (h : a ≠ i)
    (b : Fin (n - 1)) :
    reducedBurauColMatrix t i a b = if a = b then 1 else 0 := by
  rw [reducedBurauColMatrix_apply, ite_eq_right h, zero_mul, sub_zero]

/-- The diagonal entry of an elementary reduced Burau matrix in its nontrivial row is `-t`. -/
@[simp]
theorem reducedBurauColMatrix_apply_self (t : R) (i : Fin (n - 1)) :
    reducedBurauColMatrix t i i i = -t := by
  rw [reducedBurauColMatrix_apply, reducedBurauColRow_self]
  simp

/-- The entry just above the diagonal in the nontrivial row of an elementary reduced Burau matrix
is `t`. -/
theorem reducedBurauColMatrix_apply_of_succ (t : R) {i j : Fin (n - 1)} (h : (i : ℕ) + 1 = j) :
    reducedBurauColMatrix t i i j = t := by
  have hne : i ≠ j := fun hij => by rw [hij] at h; omega
  rw [reducedBurauColMatrix_apply, reducedBurauColRow_of_succ t h, ite_eq_right hne]
  simp

/-- The entry just below the diagonal in the nontrivial row of an elementary reduced Burau matrix
is `1`. -/
theorem reducedBurauColMatrix_apply_of_succ_rev (t : R) {i j : Fin (n - 1)} (h : (j : ℕ) + 1 = i) :
    reducedBurauColMatrix t i i j = 1 := by
  have hne : i ≠ j := fun hij => by rw [hij] at h; omega
  rw [reducedBurauColMatrix_apply, reducedBurauColRow_of_succ_rev t h, ite_eq_right hne]
  simp

/-- Away from the diagonal and its two neighbours the nontrivial row of an elementary reduced
Burau matrix vanishes. -/
theorem reducedBurauColMatrix_apply_of_not_adjacent (t : R) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) : reducedBurauColMatrix t i i j = 0 := by
  have hne : i ≠ j := fun hij => by rw [hij] at h; omega
  rw [reducedBurauColMatrix_apply, reducedBurauColRow_of_not_adjacent t h, ite_eq_right hne]
  simp

/-! ### The reduced matrices are the restriction of the unreduced ones -/

/-- **An elementary Burau matrix restricts to the elementary reduced Burau matrix** on the span of
the Burau columns. -/
theorem burauMatrix_mul_burauColMatrix (t : R) (i : Fin (n - 1)) :
    burauMatrix t i * burauColMatrix n t = burauColMatrix n t * reducedBurauColMatrix t i := by
  rw [burauMatrix_def, reducedBurauColMatrix_def, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
    Matrix.mul_one, vecMulVec_mul, mul_vecMulVec, burauRow_vecMul_burauColMatrix,
    burauColMatrix_mulVec_single]

/-! ### The reduced Burau matrices in the Burau-column basis on two and three strands -/

/-- On two strands the reduced Burau representation is one-dimensional, sending the single
elementary braid to `-t`. -/
theorem reducedBurauColMatrix_two (t : R) (i : Fin (2 - 1)) :
    reducedBurauColMatrix t i = !![-t] := by
  ext a b
  fin_cases i
  fin_cases a
  fin_cases b
  simp [reducedBurauColMatrix_apply_self]

/-- The reduced Burau matrix of the first elementary braid on three strands. -/
theorem reducedBurauColMatrix_three_zero (t : R) :
    reducedBurauColMatrix t (0 : Fin (3 - 1)) = !![-t, t; 0, 1] := by
  rw [Matrix.eta_fin_two (reducedBurauColMatrix t (0 : Fin (3 - 1))),
    reducedBurauColMatrix_apply_self, reducedBurauColMatrix_apply_of_succ t (by decide),
    reducedBurauColMatrix_apply_of_ne t (by decide),
    reducedBurauColMatrix_apply_of_ne t (by decide)]
  norm_num

/-- The reduced Burau matrix of the second elementary braid on three strands. -/
theorem reducedBurauColMatrix_three_one (t : R) :
    reducedBurauColMatrix t (1 : Fin (3 - 1)) = !![1, 0; 1, -t] := by
  rw [Matrix.eta_fin_two (reducedBurauColMatrix t (1 : Fin (3 - 1))),
    reducedBurauColMatrix_apply_of_ne t (by decide),
    reducedBurauColMatrix_apply_of_ne t (by decide),
    reducedBurauColMatrix_apply_of_succ_rev t (by decide), reducedBurauColMatrix_apply_self]
  norm_num

end Ring

section CommRing

variable [CommRing R] {n : ℕ}

/-- Every linear combination of the Burau columns belongs to the invariant kernel carrying the
reduced Burau representation. -/
theorem burauColMatrix_mulVec_mem_reducedBurauSpace (n : ℕ) (t : R)
    (c : Fin (n - 1) → R) :
    burauColMatrix n t *ᵥ c ∈ reducedBurauSpace n t := by
  rw [mem_reducedBurauSpace_iff]
  calc
    _ = (fun k : Fin n => t ^ (k : ℕ)) ⬝ᵥ (burauColMatrix n t *ᵥ c) := rfl
    _ = ((fun k : Fin n => t ^ (k : ℕ)) ᵥ* burauColMatrix n t) ⬝ᵥ c :=
      dotProduct_mulVec _ _ _
    _ = 0 := by rw [geom_vecMul_burauColMatrix_eq_zero]; simp

/-- Coordinates on the reduced Burau space of an `(n + 1)`-strand braid. The tail coordinates
are free, and the zeroth coordinate is determined by the equation
`x₀ + ∑ i, t ^ (i + 1) x_(i+1) = 0`. -/
def reducedBurauSpaceEquiv (n : ℕ) (t : R) :
    (Fin n → R) ≃ₗ[R] ReducedBurauSpace (n + 1) t where
  toFun x := ⟨Fin.cons (-∑ i : Fin n, t ^ ((i : ℕ) + 1) * x i) x, by
    simp only [reducedBurauSpace, LinearMap.mem_ker, geometricCovector_apply,
      Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, one_mul,
      Fin.val_succ]
    abel⟩
  invFun x := Fin.tail x.1
  left_inv x := by
    funext i
    simp
  right_inv x := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j ↦ by simp only [Fin.tail, Fin.cons_succ]) i
    have hx := x.2
    simp only [reducedBurauSpace, LinearMap.mem_ker, geometricCovector_apply,
      Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_mul, Fin.val_succ] at hx
    simpa only [Fin.tail, Fin.cons_zero] using (eq_neg_of_add_eq_zero_left hx).symm
  map_add' x y := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j ↦ by simp only [Submodule.coe_add, Pi.add_apply,
      Fin.cons_succ]) i
    simp only [Fin.cons_zero, Submodule.coe_add, Pi.add_apply]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    abel
  map_smul' c x := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j ↦ by simp only [Submodule.coe_smul, Pi.smul_apply,
      Fin.cons_succ, RingHom.id_apply]) i
    simp only [Fin.cons_zero, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    have hsum : (∑ i : Fin n, t ^ ((i : ℕ) + 1) * (c * x i)) =
        c * ∑ i : Fin n, t ^ ((i : ℕ) + 1) * x i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum]
    ring

/-- The vector underlying `reducedBurauSpaceEquiv`: the free coordinates form its tail. -/
@[simp]
theorem reducedBurauSpaceEquiv_apply_coe (n : ℕ) (t : R) (x : Fin n → R) :
    (reducedBurauSpaceEquiv n t x : Fin (n + 1) → R) =
      Fin.cons (-∑ i : Fin n, t ^ ((i : ℕ) + 1) * x i) x := by
  simp [reducedBurauSpaceEquiv]

/-- The inverse coordinate map takes the tail of a vector in the reduced Burau space. -/
@[simp]
theorem reducedBurauSpaceEquiv_symm_apply (n : ℕ) (t : R)
    (x : ReducedBurauSpace (n + 1) t) :
    (reducedBurauSpaceEquiv n t).symm x = Fin.tail x.1 := by
  simp [reducedBurauSpaceEquiv]

/-- The unreduced Burau matrix representation, regarded as a representation on the free module of
column vectors. -/
def burauRepresentation (n : ℕ) (t : Rˣ) : Representation R (BraidGroup n) (Fin n → R) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv R (Fin n → R)).toMonoidHom.comp
      (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp (burau n t)))

/-- The module action of the unreduced Burau representation is multiplication by its Burau
matrix. -/
@[simp]
theorem burauRepresentation_apply (n : ℕ) (t : Rˣ) (b : BraidGroup n) (x : Fin n → R) :
    burauRepresentation n t b x = (burau n t b : Matrix (Fin n) (Fin n) R) *ᵥ x :=
  by simp [burauRepresentation]

/-- The geometric covector is invariant under the unreduced Burau representation. -/
theorem geometricCovector_burauRepresentation (n : ℕ) (t : Rˣ) (b : BraidGroup n)
    (x : Fin n → R) :
    geometricCovector n (t : R) (burauRepresentation n t b x) =
      geometricCovector n (t : R) x := by
  rw [burauRepresentation_apply]
  calc
    geometricCovector n (t : R)
        ((burau n t b : Matrix (Fin n) (Fin n) R) *ᵥ x) =
        (fun k : Fin n ↦ (t : R) ^ (k : ℕ)) ⬝ᵥ
          ((burau n t b : Matrix (Fin n) (Fin n) R) *ᵥ x) := rfl
    _ = ((fun k : Fin n ↦ (t : R) ^ (k : ℕ)) ᵥ*
          (burau n t b : Matrix (Fin n) (Fin n) R)) ⬝ᵥ x := dotProduct_mulVec _ _ _
    _ = (fun k : Fin n ↦ (t : R) ^ (k : ℕ)) ⬝ᵥ x := by rw [vecMul_burau_geom]
    _ = geometricCovector n (t : R) x := rfl

/-- The kernel of the geometric covector is invariant under the unreduced Burau action. -/
theorem reducedBurauSpace_invariant (n : ℕ) (t : Rˣ) (b : BraidGroup n) :
    reducedBurauSpace n (t : R) ≤
      (reducedBurauSpace n (t : R)).comap (burauRepresentation n t b) := by
  intro x hx
  rw [reducedBurauSpace] at hx ⊢
  rw [LinearMap.mem_ker] at hx
  rw [Submodule.mem_comap, LinearMap.mem_ker]
  rw [geometricCovector_burauRepresentation, hx]

/-- The reduced Burau representation on the invariant kernel of the geometric covector. -/
def reducedBurauSubrepresentation (n : ℕ) (t : Rˣ) :
    Representation R (BraidGroup n) (ReducedBurauSpace n (t : R)) :=
  (burauRepresentation n t).subrepresentation (reducedBurauSpace n (t : R))
    (reducedBurauSpace_invariant n t)

/-- The kernel representation acts by the unreduced Burau matrix on underlying vectors. -/
@[simp]
theorem coe_reducedBurauSubrepresentation_apply (n : ℕ) (t : Rˣ) (b : BraidGroup n)
    (x : ReducedBurauSpace n (t : R)) :
    (reducedBurauSubrepresentation n t b x : Fin n → R) =
      (burau n t b : Matrix (Fin n) (Fin n) R) *ᵥ x.1 :=
  by
    rw [reducedBurauSubrepresentation, Representation.subrepresentation_apply]
    exact burauRepresentation_apply n t b x

/-- The reduced Burau representation of the braid group on `n + 1` strands, transported from the
invariant kernel to its `n` free tail coordinates. -/
def reducedBurau (n : ℕ) (t : Rˣ) : Representation R (BraidGroup (n + 1)) (Fin n → R) :=
  ((reducedBurauSpaceEquiv n (t : R)).symm.conjRingEquiv).toMonoidHom.comp
    (reducedBurauSubrepresentation (n + 1) t)

/-- The reduced action is obtained by inserting free coordinates into the invariant kernel,
applying the unreduced Burau matrix, and taking the tail. -/
@[simp]
theorem reducedBurau_apply (n : ℕ) (t : Rˣ) (b : BraidGroup (n + 1)) (x : Fin n → R) :
    reducedBurau n t b x = Fin.tail
      ((burau (n + 1) t b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *ᵥ
        (reducedBurauSpaceEquiv n (t : R) x : Fin (n + 1) → R)) :=
  by simp [reducedBurau]

/-- On an elementary braid, the reduced action is the tail of the elementary Burau matrix acting
on the canonical kernel coordinates. -/
theorem reducedBurau_sigma (n : ℕ) (t : Rˣ) (i : Fin n) (x : Fin n → R) :
    reducedBurau n t (BraidGroup.sigma i) x = Fin.tail
      (burauMatrix (t : R) i *ᵥ
        (reducedBurauSpaceEquiv n (t : R) x : Fin (n + 1) → R)) := by
  rw [reducedBurau_apply, burau_sigma, coe_burauGL]

/-- The individual free coordinates of the reduced action of an elementary braid: the `j`-th
coordinate of the reduced action is the `j.succ`-th coordinate of the unreduced action. This is
`TauCeti.KnotTheory.reducedBurau_sigma` evaluated at a coordinate, using that `Fin.tail v j` is by
definition `v j.succ`; it is the form in which entrywise computations with the reduced matrices are
carried out. -/
theorem reducedBurau_sigma_apply (n : ℕ) (t : Rˣ) (i : Fin n) (x : Fin n → R) (j : Fin n) :
    reducedBurau n t (BraidGroup.sigma i) x j =
      (burauMatrix (n := n + 1) (t : R) i *ᵥ
        (reducedBurauSpaceEquiv n (t : R) x : Fin (n + 1) → R)) j.succ := by
  rw [reducedBurau_sigma]
  rfl

/-- On two strands the reduced Burau representation sends the elementary braid to multiplication
by `-t`. This is the first nonzero-dimensional case and fixes the normalization of the reduced
representation. -/
@[simp]
theorem reducedBurau_sigma_zero_apply (t : Rˣ) (x : Fin 1 → R) :
    reducedBurau 1 t (BraidGroup.sigma 0) x 0 = -(t : R) * x 0 := by
  rw [reducedBurau_sigma_apply, burauMatrix_mulVec, burauRow_dotProduct]
  have hstrand : BraidGroup.strand (n := 2) 0 = 0 := by simp [Fin.ext_iff]
  have hstrandSucc : BraidGroup.strandSucc (n := 2) 0 = 1 := by simp [Fin.ext_iff]
  simp [hstrand, hstrandSucc, burauCol_apply]

/-! ### The braid relations, the inverse and the Hecke relation -/

/-- The determinant of an elementary reduced Burau matrix is `-t`, as for the unreduced one. -/
@[simp]
theorem det_reducedBurauColMatrix (t : R) (i : Fin (n - 1)) :
    (reducedBurauColMatrix t i).det = -t := by
  rw [reducedBurauColMatrix_def, det_one_sub_vecMulVec, dotProduct_single_one,
    reducedBurauColRow_self]
  ring

/-- **The distant commutation relation** for the elementary reduced Burau matrices. -/
theorem reducedBurauColMatrix_mul_comm (t : R) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    reducedBurauColMatrix t i * reducedBurauColMatrix t j =
      reducedBurauColMatrix t j * reducedBurauColMatrix t i :=
  one_sub_vecMulVec_mul_comm
    (by simpa only [dotProduct_single_one] using reducedBurauColRow_of_not_adjacent t h)
    (by simpa only [dotProduct_single_one] using
      reducedBurauColRow_of_not_adjacent t h.symm)

/-- **The braid relation** for the elementary reduced Burau matrices. -/
theorem reducedBurauColMatrix_braid (t : R) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    reducedBurauColMatrix t i * reducedBurauColMatrix t j * reducedBurauColMatrix t i =
      reducedBurauColMatrix t j * reducedBurauColMatrix t i * reducedBurauColMatrix t j :=
  one_sub_vecMulVec_braid_of_adjacent t (fun i => Pi.single i (1 : R)) (reducedBurauColRow t)
    (fun i => by simpa only [dotProduct_single_one] using reducedBurauColRow_self t i)
    (fun h => by simpa only [dotProduct_single_one] using reducedBurauColRow_of_succ t h)
    (fun h => by
      simpa only [dotProduct_single_one] using reducedBurauColRow_of_succ_rev t h)
    h

/-- **The quadratic relation** for the elementary reduced Burau matrices, equivalently
`(x - 1) * (x + t) = 0`. This is the Iwahori-Hecke quadratic relation in the normalisation with
eigenvalues `1` and `-t`. -/
theorem reducedBurauColMatrix_mul_self (t : R) (i : Fin (n - 1)) :
    reducedBurauColMatrix t i * reducedBurauColMatrix t i =
      (1 - t) • reducedBurauColMatrix t i + t • 1 :=
  one_sub_vecMulVec_mul_self t
    (by simpa only [dotProduct_single_one] using reducedBurauColRow_self t i)

/-! ### The reduced Burau homomorphism in the Burau-column basis -/

/-- An elementary reduced Burau matrix as an element of the general linear group, with inverse
`1 - t⁻¹ • vecMulVec (Pi.single i 1) (reducedBurauColRow t i)`. -/
def reducedBurauColGL (t : Rˣ) (i : Fin (n - 1)) : GL (Fin (n - 1)) R :=
  oneSubVecMulVecGL t (Pi.single i 1) (reducedBurauColRow (t : R) i)
    (by simpa only [dotProduct_single_one] using reducedBurauColRow_self (t : R) i)

/-- The matrix underlying `TauCeti.KnotTheory.reducedBurauColGL`. -/
@[simp]
theorem coe_reducedBurauColGL (t : Rˣ) (i : Fin (n - 1)) :
    (reducedBurauColGL t i : Matrix (Fin (n - 1)) (Fin (n - 1)) R) =
      reducedBurauColMatrix (t : R) i :=
  by rw [reducedBurauColGL, coe_oneSubVecMulVecGL, reducedBurauColMatrix_def]

/-- The nonsingular inverse of an elementary reduced Burau matrix. -/
@[simp]
theorem inv_reducedBurauColMatrix (t : Rˣ) (i : Fin (n - 1)) :
    (reducedBurauColMatrix (t : R) i)⁻¹ =
      1 - ((t⁻¹ : Rˣ) : R) • vecMulVec (Pi.single i 1) (reducedBurauColRow (t : R) i) := by
  rw [reducedBurauColMatrix_def,
    inv_one_sub_vecMulVec t (by
      simpa only [dotProduct_single_one] using reducedBurauColRow_self (t : R) i)]

/-- The reduced Burau homomorphism in the basis of Burau columns. Its name records the basis to
distinguish it from `TauCeti.KnotTheory.reducedBurau`, which uses canonical tail coordinates. -/
def reducedBurauCol (n : ℕ) (t : Rˣ) : BraidGroup n →* GL (Fin (n - 1)) R :=
  braidHomOfOneSubVecMulVec n t (fun i => Pi.single i 1) (reducedBurauColRow (t : R))
    (fun i => by
      simpa only [dotProduct_single_one] using reducedBurauColRow_self (t : R) i)
    (fun h => by
      simpa only [dotProduct_single_one] using reducedBurauColRow_of_not_adjacent (t : R) h)
    (fun h => by
      simpa only [dotProduct_single_one] using reducedBurauColRow_of_succ (t : R) h)
    (fun h => by
      simpa only [dotProduct_single_one] using reducedBurauColRow_of_succ_rev (t : R) h)

/-- The Burau-column reduced homomorphism takes an elementary braid to its corresponding
elementary reduced matrix. -/
@[simp]
theorem reducedBurauCol_sigma (t : Rˣ) (i : Fin (n - 1)) :
    reducedBurauCol n t (BraidGroup.sigma i) = reducedBurauColGL t i := by
  unfold reducedBurauCol reducedBurauColGL
  exact braidHomOfOneSubVecMulVec_sigma n t (fun i => Pi.single i 1)
    (reducedBurauColRow (t : R))
    (fun i => by
      simpa only [dotProduct_single_one] using reducedBurauColRow_self (t : R) i)
    (fun h => by
      simpa only [dotProduct_single_one] using reducedBurauColRow_of_not_adjacent (t : R) h)
    (fun h => by
      simpa only [dotProduct_single_one] using reducedBurauColRow_of_succ (t : R) h)
    (fun h => by
      simpa only [dotProduct_single_one] using reducedBurauColRow_of_succ_rev (t : R) h)
    i

/-- The matrix of an elementary braid under the Burau-column reduced homomorphism. -/
theorem coe_reducedBurauCol_sigma (t : Rˣ) (i : Fin (n - 1)) :
    (reducedBurauCol n t (BraidGroup.sigma i) : Matrix (Fin (n - 1)) (Fin (n - 1)) R) =
      reducedBurauColMatrix (t : R) i := by
  rw [reducedBurauCol_sigma, coe_reducedBurauColGL]

/-- The determinant of the Burau-column reduced matrix of a braid is `-t` raised to its exponent
sum, as for the unreduced representation. -/
theorem det_reducedBurauCol (t : Rˣ) (b : BraidGroup n) :
    Matrix.GeneralLinearGroup.det (reducedBurauCol n t b) =
      (-t) ^ Multiplicative.toAdd (ArtinGroup.exponentSum (CoxeterMatrix.A (n - 1)) b) :=
  det_braidHomOfOneSubVecMulVec n t (fun i => Pi.single i 1) (reducedBurauColRow (t : R))
    (fun i => by
      simpa only [dotProduct_single_one] using reducedBurauColRow_self (t : R) i)
    (fun h => by
      simpa only [dotProduct_single_one] using reducedBurauColRow_of_not_adjacent (t : R) h)
    (fun h => by
      simpa only [dotProduct_single_one] using reducedBurauColRow_of_succ (t : R) h)
    (fun h => by
      simpa only [dotProduct_single_one] using reducedBurauColRow_of_succ_rev (t : R) h)
    b

/-- The reduced Burau homomorphism in the Burau-column basis is the restriction of the unreduced
one to the span of those columns. -/
theorem burau_mul_burauColMatrix (t : Rˣ) (b : BraidGroup n) :
    (burau n t b : Matrix (Fin n) (Fin n) R) * burauColMatrix n (t : R) =
      burauColMatrix n (t : R) *
        (reducedBurauCol n t b : Matrix (Fin (n - 1)) (Fin (n - 1)) R) := by
  apply burau_mul_of_forall (ρ := reducedBurauCol n t) _ b
  intro i
  rw [coe_reducedBurauCol_sigma]
  exact burauMatrix_mul_burauColMatrix (t : R) i

/-- The reduced Burau matrix of a braid in the Burau-column basis can be read off from the
unreduced matrix using the explicit left inverse of the column matrix. -/
theorem reducedBurauCol_eq (t : Rˣ) (b : BraidGroup n) :
    (reducedBurauCol n t b : Matrix (Fin (n - 1)) (Fin (n - 1)) R) =
      burauCoordMatrix n t * (burau n t b : Matrix (Fin n) (Fin n) R) *
        burauColMatrix n (t : R) := by
  rw [Matrix.mul_assoc, burau_mul_burauColMatrix, ← Matrix.mul_assoc,
    burauCoordMatrix_mul_burauColMatrix, Matrix.one_mul]

/-- The Burau-column and tail-coordinate constructions give the same reduced action after the
coordinate change that takes column coefficients to the tail of their linear combination. -/
theorem reducedBurau_apply_burauColMatrix_mulVec (n : ℕ) (t : Rˣ)
    (b : BraidGroup (n + 1)) (c : Fin (n + 1 - 1) → R) :
    reducedBurau n t b (Fin.tail (burauColMatrix (n + 1) (t : R) *ᵥ c)) =
      Fin.tail (burauColMatrix (n + 1) (t : R) *ᵥ
        ((reducedBurauCol (n + 1) t b :
          Matrix (Fin (n + 1 - 1)) (Fin (n + 1 - 1)) R) *ᵥ c)) := by
  rw [reducedBurau_apply]
  have hmem := burauColMatrix_mulVec_mem_reducedBurauSpace (n + 1) (t : R) c
  let x : ReducedBurauSpace (n + 1) (t : R) :=
    ⟨burauColMatrix (n + 1) (t : R) *ᵥ c, hmem⟩
  have hx := (reducedBurauSpaceEquiv n (t : R)).apply_symm_apply x
  rw [reducedBurauSpaceEquiv_symm_apply] at hx
  have hx' : ((reducedBurauSpaceEquiv n (t : R))
      (Fin.tail (burauColMatrix (n + 1) (t : R) *ᵥ c)) : Fin (n + 1) → R) =
      burauColMatrix (n + 1) (t : R) *ᵥ c := by
    simpa only [x] using congrArg Subtype.val hx
  rw [hx']
  apply congrArg Fin.tail
  rw [Matrix.mulVec_mulVec, burau_mul_burauColMatrix, ← Matrix.mulVec_mulVec]

end CommRing

end TauCeti.KnotTheory
