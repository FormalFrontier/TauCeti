/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.RingTheory.Localization.Integer

public section

/-!
# Positive definiteness of an integer matrix, over the integers and over the rationals

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

## Main results

* `TauCeti.Matrix.posDef_map_intCast`: an integer matrix that is positive definite over `ℤ` is
  positive definite over `ℚ`.
-/

open scoped Matrix

namespace TauCeti

namespace Matrix

variable {n : Type*}

/-- The finite case of `TauCeti.Matrix.posDef_map_intCast`, where positive definiteness can be
tested against ordinary vectors. -/
private theorem posDef_map_intCast_of_finite [Finite n] {A : Matrix n n ℤ} (hA : A.PosDef) :
    (A.map (Int.cast : ℤ → ℚ)).PosDef := by
  classical
  have _i : Fintype n := Fintype.ofFinite n
  refine _root_.Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx ↦ ?_
  · ext i j
    simpa using congrArg (fun m : ℤ ↦ (m : ℚ)) (hA.isHermitian.apply i j)
  -- Expand both quadratic forms as double sums.
  have expandQ : ∀ y : n → ℚ, star y ⬝ᵥ ((A.map (Int.cast : ℤ → ℚ)) *ᵥ y) =
      ∑ i, ∑ j, y i * (A i j : ℚ) * y j := by
    intro y
    simp [_root_.dotProduct, _root_.Matrix.mulVec_apply_eq_sum, Finset.mul_sum, mul_assoc]
  have expandZ : ∀ y : n → ℤ, star y ⬝ᵥ (A *ᵥ y) = ∑ i, ∑ j, y i * A i j * y j := by
    intro y
    simp [_root_.dotProduct, _root_.Matrix.mulVec_apply_eq_sum, Finset.mul_sum, mul_assoc]
  -- Clear the denominators of `x`, producing an integer vector `z = c • x`.
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) x
  have hc' : ∀ i, ∃ y : ℤ, (y : ℚ) = ((c : ℤ) : ℚ) * x i := by
    intro i
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
  -- The two quadratic forms differ by the square of the common denominator.
  have key : ((star z ⬝ᵥ (A *ᵥ z) : ℤ) : ℚ) =
      ((c : ℤ) : ℚ) ^ 2 * (star x ⬝ᵥ ((A.map (Int.cast : ℤ → ℚ)) *ᵥ x)) := by
    rw [expandQ, expandZ, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hz, hz]
    ring
  have hpos : (0 : ℚ) < ((star z ⬝ᵥ (A *ᵥ z) : ℤ) : ℚ) := by
    exact_mod_cast hA.dotProduct_mulVec_pos hzne
  rw [key] at hpos
  have hsq : (0 : ℚ) < ((c : ℤ) : ℚ) ^ 2 := by positivity
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

end Matrix

end TauCeti
