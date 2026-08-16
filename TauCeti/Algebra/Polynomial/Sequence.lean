/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Polynomial.Sequence

/-!
# Linear independence of polynomial sequences

This file generalizes Mathlib's `Polynomial.Sequence.linearIndependent` from domains to arbitrary
rings where the sequence elements have right-regular leading coefficients, and constructs a basis
when those coefficients are units.

## Main statements

* `Polynomial.Sequence.linearIndependent_of_isRightRegular_leadingCoeff`: a polynomial sequence
  whose elements have right-regular leading coefficients is linearly independent over any ring.
* `Polynomial.Sequence.basisOfIsUnitLeadingCoeff`: the corresponding basis of `R[X]`.
-/

public section

namespace Polynomial.Sequence

open Module Submodule

variable {R : Type*} [Ring R] (S : Polynomial.Sequence R)

/-- Polynomials in a polynomial sequence whose leading coefficients are right-regular are linearly
independent. -/
theorem linearIndependent_of_isRightRegular_leadingCoeff
    (hCoeff : ∀ i, IsRightRegular (S i).leadingCoeff) :
    LinearIndependent R S := by
  classical
  refine linearIndependent_iff'.2 fun s g hsum i hi => ?_
  by_contra hgi
  have hne : (s.filter fun j => g j ≠ 0).Nonempty := ⟨i, Finset.mem_filter.2 ⟨hi, hgi⟩⟩
  let m := (s.filter fun j => g j ≠ 0).max' hne
  have hm : m ∈ s.filter fun j => g j ≠ 0 := Finset.max'_mem _ hne
  have hgm : g m ≠ 0 := (Finset.mem_filter.1 hm).2
  have hms : m ∈ s := (Finset.mem_filter.1 hm).1
  have hle (j : ℕ) (hj : j ∈ s) (hgj : g j ≠ 0) : j ≤ m :=
    Finset.le_max' _ j (Finset.mem_filter.2 ⟨hj, hgj⟩)
  have hzero (j : ℕ) (hj : j ∈ s) (hj_gt : m < j) : g j = 0 := by
    by_contra h; have := hle j hj h; omega
  have h_split : g m • S m + ∑ j ∈ s.erase m, g j • S j = 0 := by
    rw [Finset.add_sum_erase s (fun j => g j • S j) hms, hsum]
  have h_coeff := congrArg (Polynomial.coeff · m) h_split
  rw [Polynomial.coeff_add, Polynomial.coeff_smul, Polynomial.coeff_zero] at h_coeff
  have h_m_coeff : (S m).coeff m = (S m).leadingCoeff := by
    rw [Polynomial.leadingCoeff, S.natDegree_eq m]
  have h_erase_coeff : (∑ j ∈ s.erase m, g j • S j).coeff m = 0 := by
    rw [Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro j hj
    have hj_s := Finset.mem_of_mem_erase hj
    have hj_ne := Finset.ne_of_mem_erase hj
    by_cases hj_le : j ≤ m
    · have hj_lt : j < m := lt_of_le_of_ne hj_le hj_ne
      have hj_natDeg : (S j).natDegree = j := S.natDegree_eq j
      rw [Polynomial.coeff_smul, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), smul_zero]
    · have hj_gt : m < j := by omega
      rw [hzero j hj_s hj_gt, zero_smul, Polynomial.coeff_zero]
  rw [h_m_coeff, h_erase_coeff, add_zero, smul_eq_mul] at h_coeff
  exact hgm ((hCoeff m) (by simpa using h_coeff))

/-- Every polynomial sequence with unit leading coefficients is a basis of `R[X]`. -/
noncomputable def basisOfIsUnitLeadingCoeff
    (hCoeff : ∀ i, IsUnit (S i).leadingCoeff) :
    Basis ℕ R R[X] :=
  Basis.mk (S.linearIndependent_of_isRightRegular_leadingCoeff fun i =>
      (hCoeff i).isRegular.right)
    (eq_top_iff.mp (S.span hCoeff))

/-- The `i`-th basis vector is the `i`-th polynomial in the sequence. -/
@[simp]
theorem basisOfIsUnitLeadingCoeff_apply
    (hCoeff : ∀ i, IsUnit (S i).leadingCoeff) (i : ℕ) :
    S.basisOfIsUnitLeadingCoeff hCoeff i = S i :=
  Basis.mk_apply _ _ _

end Polynomial.Sequence
