/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.RingTheory.Localization.Integer
import Mathlib.Data.Rat.Star

public section

/-!
# Positive definiteness over the rationals

`Matrix.PosDef` is stated relative to the coefficient ring, so for a matrix of integers it says
that the associated quadratic form is positive on nonzero *integer* vectors. That is formally
weaker than positivity on nonzero *rational* vectors, and it is the rational statement that later
arguments want, since a rational vector may be built from a construction that does not respect
denominators. This file records one implication: an integer matrix that is positive definite over
`ℤ` stays positive definite after casting its entries into `ℚ`.

The proof is the obvious one. A nonzero rational vector becomes a nonzero integer vector after
multiplying by a common denominator, and the quadratic form scales by the square of that
denominator, which is positive. The index type need not be finite: a test vector for
`Matrix.PosDef` is finitely supported, so the general case follows from the finite one applied to
the principal submatrix on the support of the vector.

The file also records the standard way of certifying a rational matrix as positive definite: write
it as `Bᴴ * B` for an explicit `B`, and check that it is invertible.

## Main results

* `TauCeti.Matrix.posDef_map_intCast`: an integer matrix that is positive definite over `ℤ` is
  positive definite over `ℚ`.
* `TauCeti.Matrix.posDef_conjTranspose_mul_self_of_isUnit`: an invertible rational matrix of the
  form `Bᴴ * B` is positive definite.
-/

open scoped Matrix

namespace TauCeti

namespace Matrix

variable {n : Type*}

/-- Clearing denominators: a nonzero rational vector on a finite index type is a nonzero integer
vector scaled by a common nonzero denominator. -/
private theorem exists_intCast_eq_mul_of_ne_zero [Finite n] {x : n → ℚ} (hx : x ≠ 0) :
    ∃ (c : ℤ) (z : n → ℤ), c ≠ 0 ∧ z ≠ 0 ∧ ∀ i, (z i : ℚ) = (c : ℚ) * x i := by
  classical
  have _i : Fintype n := Fintype.ofFinite n
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) x
  have hc' : ∀ i, ∃ y : ℤ, (y : ℚ) = ((c : ℤ) : ℚ) * x i := fun i => by
    obtain ⟨y, hy⟩ := hc i
    exact ⟨y, by simpa [Algebra.smul_def] using hy⟩
  choose z hz using hc'
  have hc0 : ((c : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (nonZeroDivisors.coe_ne_zero c)
  have hzne : z ≠ 0 := by
    intro h
    refine hx (funext fun i ↦ ?_)
    have hi := hz i
    rw [h] at hi
    simpa [hc0] using hi.symm
  exact ⟨(c : ℤ), z, nonZeroDivisors.coe_ne_zero c, hzne, hz⟩

/-- The finite case of `TauCeti.Matrix.posDef_map_intCast`, where positive definiteness can be
tested against ordinary vectors. -/
private theorem posDef_map_intCast_of_finite [Finite n] {A : Matrix n n ℤ} (hA : A.PosDef) :
    (A.map (Int.cast : ℤ → ℚ)).PosDef := by
  classical
  have _i : Fintype n := Fintype.ofFinite n
  refine _root_.Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx ↦ ?_
  · ext i j
    simpa using congrArg (fun m : ℤ ↦ (m : ℚ)) (hA.isHermitian.apply i j)
  -- Clear the denominators of `x`, producing a nonzero integer vector `z = c • x`.
  obtain ⟨c, z, hc0, hzne, hz⟩ := exists_intCast_eq_mul_of_ne_zero hx
  have hcQ : (c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc0
  -- The two quadratic forms differ by the square of the common denominator.
  have key : ((star z ⬝ᵥ (A *ᵥ z) : ℤ) : ℚ) =
      (c : ℚ) ^ 2 * (star x ⬝ᵥ ((A.map (Int.cast : ℤ → ℚ)) *ᵥ x)) := by
    simp only [_root_.Matrix.dot_mulVec_eq_sum_sum, star_trivial, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hz, hz, _root_.Matrix.map_apply]
    ring
  have hpos : (0 : ℚ) < ((star z ⬝ᵥ (A *ᵥ z) : ℤ) : ℚ) := by
    exact_mod_cast hA.dotProduct_mulVec_pos hzne
  rw [key] at hpos
  have hsq : (0 : ℚ) < (c : ℚ) ^ 2 := by positivity
  exact (mul_pos_iff_of_pos_left hsq).mp hpos

/-- **An integer matrix positive definite over `ℤ` is positive definite over `ℚ`.** -/
theorem posDef_map_intCast {A : Matrix n n ℤ} (hA : A.PosDef) :
    (A.map (Int.cast : ℤ → ℚ)).PosDef := by
  classical
  refine ⟨?_, fun x hx ↦ ?_⟩
  · ext i j
    simpa using congrArg (fun m : ℤ ↦ (m : ℚ)) (hA.isHermitian.apply i j)
  -- A test vector is supported on a finite set, so it is enough to know the finite case for the
  -- principal submatrix on the support of `x`.
  set e : {a // a ∈ x.support} → n := Subtype.val
  have hinj : Function.Injective e := Subtype.val_injective
  have hsupp : ↑x.support ⊆ Set.range e := fun a ha ↦ ⟨⟨a, ha⟩, rfl⟩
  have hmap : Finsupp.mapDomain e (Finsupp.comapDomain e x hinj.injOn) = x :=
    Finsupp.mapDomain_comapDomain _ hinj x hsupp
  have hsub : ((A.map (Int.cast : ℤ → ℚ)).submatrix e e).PosDef := by
    rw [_root_.Matrix.submatrix_map]
    exact posDef_map_intCast_of_finite (hA.submatrix hinj)
  have hne : Finsupp.comapDomain e x hinj.injOn ≠ 0 := fun h ↦ hx (by rw [← hmap, h]; simp)
  rw [← hmap]
  simpa [Finsupp.sum_mapDomain_index, add_mul, mul_add] using hsub.2 hne

/-- **An invertible rational matrix of the form `Bᴴ * B` is positive definite.** Being of that
form gives positive *semi*definiteness for free; invertibility upgrades it, by way of the
injectivity hypothesis of `Matrix.PosDef.conjTranspose_mul_self`.

Mathlib's `Matrix.PosSemidef.posDef_iff_isUnit` says the same thing in one step, but only over an
`RCLike` field, which `ℚ` is not; `Matrix.PosDef.conjTranspose_mul_self` is the criterion that does
apply here, needing only `StarOrderedRing` and `NoZeroDivisors`. -/
theorem posDef_conjTranspose_mul_self_of_isUnit {m : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (B : _root_.Matrix m n ℚ) (hunit : IsUnit (Bᴴ * B)) : (Bᴴ * B).PosDef := by
  refine _root_.Matrix.PosDef.conjTranspose_mul_self B fun x y hxy ↦ ?_
  apply _root_.Matrix.mulVec_injective_iff_isUnit.mpr hunit
  rw [← _root_.Matrix.mulVec_mulVec x Bᴴ B, ← _root_.Matrix.mulVec_mulVec y Bᴴ B, hxy]

end Matrix

end TauCeti
