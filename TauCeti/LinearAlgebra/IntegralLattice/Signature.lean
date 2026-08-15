/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# Signature and definiteness of integral lattices

This file defines the radical and signature `(n₊, n₀, n₋)` of an integral symmetric lattice and
the standard definiteness predicates.  The indices of inertia are Mathlib's `QuadraticForm.sigPos`
and `QuadraticForm.sigNeg`; the null index is the dimension of the kernel of the bilinear form.

Positive- and negative-semidefiniteness are expressed using Mathlib's bilinear-form predicates.
The characteristic theorems relate every predicate both to the signature and to the usual
elementwise inequalities.  In particular, an indefinite lattice has vectors of both signs, and a
degenerate lattice has a nonzero vector in its radical.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 1.

## Main definitions

* `TauCeti.IntegralLattice.radical`: the kernel of the rational bilinear form.
* `TauCeti.IntegralLattice.signature`: the positive, null, and negative indices.
* `TauCeti.IntegralLattice.IsPositiveSemidefinite` and related definiteness predicates.
-/

public section

namespace TauCeti

open QuadraticMap

universe u

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

/-- The radical of an integral lattice is the kernel of its rational bilinear form. -/
def radical : Submodule ℚ V := L.form.ker

/-- The radical of an integral lattice is the kernel of its rational bilinear form. -/
theorem radical_def : L.radical = L.form.ker := by
  rfl

/-- A vector lies in the radical of an integral lattice if and only if it annihilates all
vectors under the rational bilinear form. -/
@[simp]
theorem mem_radical_iff (x : V) : x ∈ L.radical ↔ ∀ y : V, L.form x y = 0 := by
  simp only [radical, LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply]

/-- The radical of the quadratic form associated to a lattice is its bilinear radical. -/
@[simp]
theorem radical_toQuadraticMap : L.form.toQuadraticMap.radical = L.radical := by
  let _ : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  rw [QuadraticMap.radical_eq_ker_associated,
    QuadraticMap.associated_left_inverse (S := ℚ) L.isSymm.eq]
  rfl

/-- The positive index of inertia of an integral lattice. -/
noncomputable abbrev sigPos : ℕ := _root_.sigPos L.form.toQuadraticMap

/-- The dimension of the radical of an integral lattice. -/
noncomputable abbrev sigNull : ℕ := Module.finrank ℚ L.radical

/-- The negative index of inertia of an integral lattice. -/
noncomputable abbrev sigNeg : ℕ := _root_.sigNeg L.form.toQuadraticMap

/-- The signature `(n₊, n₀, n₋)` of an integral lattice. -/
noncomputable abbrev signature : ℕ × ℕ × ℕ := (L.sigPos, L.sigNull, L.sigNeg)

/-- The positive, null, and negative indices exhaust the rank of the lattice. -/
theorem sigPos_add_sigNull_add_sigNeg :
    L.sigPos + L.sigNull + L.sigNeg = Module.finrank ℚ V := by
  let _ : FiniteDimensional ℚ V := Module.Finite.of_basis L.rationalBasis
  have h := _root_.QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := L.form.toQuadraticMap)
  rw [L.radical_toQuadraticMap] at h
  simpa only [sigPos, sigNull, sigNeg, add_comm, add_left_comm, add_assoc] using h

/-- An integral lattice is positive-definite when its quadratic form is positive on every nonzero
vector. -/
abbrev IsPositiveDefinite : Prop := L.form.toQuadraticMap.PosDef

/-- An integral lattice is positive-semidefinite when its symmetric bilinear form is nonnegative. -/
abbrev IsPositiveSemidefinite : Prop := L.form.IsPosSemidef

/-- An integral lattice is negative-definite when the negative of its quadratic form is
positive-definite. -/
abbrev IsNegativeDefinite : Prop := (-L.form.toQuadraticMap).PosDef

/-- An integral lattice is negative-semidefinite when the negative of its symmetric bilinear form
is positive-semidefinite. -/
abbrev IsNegativeSemidefinite : Prop := (-L.form).IsPosSemidef

/-- An integral lattice is degenerate when its radical is nontrivial. -/
def IsDegenerate : Prop := L.radical ≠ ⊥

/-- An integral lattice is indefinite when both its positive and negative indices are nonzero. -/
def IsIndefinite : Prop := 0 < L.sigPos ∧ 0 < L.sigNeg

/-- Positive-definiteness has its usual elementwise characterization. -/
@[grind =]
theorem isPositiveDefinite_iff :
    L.IsPositiveDefinite ↔ ∀ x : V, x ≠ 0 → 0 < L.form x x := by
  rfl

/-- Positive-semidefiniteness has its usual elementwise characterization. -/
@[grind =]
theorem isPositiveSemidefinite_iff :
    L.IsPositiveSemidefinite ↔ ∀ x : V, 0 ≤ L.form x x := by
  simp only [IsPositiveSemidefinite]
  rw [LinearMap.BilinForm.isPosSemidef_def, LinearMap.BilinForm.isNonneg_def]
  simp only [L.isSymm, true_and]

/-- Negative-definiteness has its usual elementwise characterization. -/
@[grind =]
theorem isNegativeDefinite_iff :
    L.IsNegativeDefinite ↔ ∀ x : V, x ≠ 0 → L.form x x < 0 := by
  simp only [IsNegativeDefinite, QuadraticMap.PosDef, neg_apply,
    LinearMap.BilinMap.toQuadraticMap_apply, neg_pos]

/-- Negative-semidefiniteness has its usual elementwise characterization. -/
@[grind =]
theorem isNegativeSemidefinite_iff :
    L.IsNegativeSemidefinite ↔ ∀ x : V, L.form x x ≤ 0 := by
  simp only [IsNegativeSemidefinite]
  rw [LinearMap.BilinForm.isPosSemidef_def, LinearMap.BilinForm.isNonneg_def]
  simp only [L.isSymm.neg, LinearMap.neg_apply, neg_nonneg, true_and]

/-- Positive-semidefiniteness is equivalent to the vanishing of the negative index. -/
@[grind =]
theorem isPositiveSemidefinite_iff_sigNeg_eq_zero :
    L.IsPositiveSemidefinite ↔ L.sigNeg = 0 := by
  let _ : FiniteDimensional ℚ V := Module.Finite.of_basis L.rationalBasis
  rw [L.isPositiveSemidefinite_iff]
  simpa only [LinearMap.BilinMap.toQuadraticMap_apply] using
    QuadraticForm.forall_nonneg_iff_sigNeg_eq_zero L.form.toQuadraticMap

/-- Negative-semidefiniteness is equivalent to the vanishing of the positive index. -/
@[grind =]
theorem isNegativeSemidefinite_iff_sigPos_eq_zero :
    L.IsNegativeSemidefinite ↔ L.sigPos = 0 := by
  let _ : FiniteDimensional ℚ V := Module.Finite.of_basis L.rationalBasis
  rw [L.isNegativeSemidefinite_iff]
  simpa only [LinearMap.BilinMap.toQuadraticMap_apply] using
    QuadraticForm.forall_nonpos_iff_sigPos_eq_zero L.form.toQuadraticMap

/-- Positive-definiteness is positive-semidefiniteness together with nondegeneracy. -/
@[grind =]
theorem isPositiveDefinite_iff_isPositiveSemidefinite_and_nondegenerate :
    L.IsPositiveDefinite ↔ L.IsPositiveSemidefinite ∧ L.form.Nondegenerate := by
  let _ : FiniteDimensional ℚ V := Module.Finite.of_basis L.rationalBasis
  simp only [IsPositiveDefinite]
  rw [L.isPositiveSemidefinite_iff_sigNeg_eq_zero,
    QuadraticForm.posDef_iff_sigNeg_eq_zero_and_radical_eq_bot,
    LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot, L.radical_toQuadraticMap]
  rfl

/-- Positive-definiteness is equivalent to zero null and negative indices. -/
@[grind =]
theorem isPositiveDefinite_iff_sigNull_eq_zero_and_sigNeg_eq_zero :
    L.IsPositiveDefinite ↔ L.sigNull = 0 ∧ L.sigNeg = 0 := by
  let _ : FiniteDimensional ℚ V := Module.Finite.of_basis L.rationalBasis
  rw [L.isPositiveDefinite_iff_isPositiveSemidefinite_and_nondegenerate,
    L.isPositiveSemidefinite_iff_sigNeg_eq_zero,
    LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot]
  simp only [sigNull, radical]
  rw [← Submodule.finrank_eq_zero]
  exact and_comm

/-- Negative-definiteness is negative-semidefiniteness together with nondegeneracy. -/
@[grind =]
theorem isNegativeDefinite_iff_isNegativeSemidefinite_and_nondegenerate :
    L.IsNegativeDefinite ↔ L.IsNegativeSemidefinite ∧ L.form.Nondegenerate := by
  let _ : FiniteDimensional ℚ V := Module.Finite.of_basis L.rationalBasis
  simp only [IsNegativeDefinite]
  rw [L.isNegativeSemidefinite_iff_sigPos_eq_zero,
    QuadraticForm.posDef_iff_sigNeg_eq_zero_and_radical_eq_bot]
  simp only [_root_.sigNeg_neg, QuadraticMap.radical_neg,
    LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot, L.radical_toQuadraticMap]
  rfl

/-- Negative-definiteness is equivalent to zero positive and null indices. -/
@[grind =]
theorem isNegativeDefinite_iff_sigPos_eq_zero_and_sigNull_eq_zero :
    L.IsNegativeDefinite ↔ L.sigPos = 0 ∧ L.sigNull = 0 := by
  let _ : FiniteDimensional ℚ V := Module.Finite.of_basis L.rationalBasis
  rw [L.isNegativeDefinite_iff_isNegativeSemidefinite_and_nondegenerate,
    L.isNegativeSemidefinite_iff_sigPos_eq_zero,
    LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot]
  simp only [sigNull, radical]
  rw [← Submodule.finrank_eq_zero]
  rfl

/-- Degeneracy is equivalent to a positive null index. -/
@[grind =]
theorem isDegenerate_iff_sigNull_pos : L.IsDegenerate ↔ 0 < L.sigNull := by
  let _ : FiniteDimensional ℚ V := Module.Finite.of_basis L.rationalBasis
  simp only [IsDegenerate, sigNull]
  rw [Nat.pos_iff_ne_zero]
  exact (Submodule.finrank_eq_zero (R := ℚ) (S := L.radical)).not.symm

/-- A lattice is degenerate exactly when its bilinear form is not nondegenerate. -/
@[grind =]
theorem isDegenerate_iff_not_nondegenerate : L.IsDegenerate ↔ ¬L.form.Nondegenerate := by
  let _ : FiniteDimensional ℚ V := Module.Finite.of_basis L.rationalBasis
  rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot]
  rfl

/-- A lattice is degenerate exactly when its radical contains a nonzero vector. -/
@[grind =]
theorem isDegenerate_iff_exists_mem_radical_ne_zero :
    L.IsDegenerate ↔ ∃ x : V, x ∈ L.radical ∧ x ≠ 0 := by
  simp only [IsDegenerate]
  exact L.radical.ne_bot_iff

/-- Indefiniteness is equivalent to the failure of both semidefiniteness conditions. -/
@[grind =]
theorem isIndefinite_iff_not_semidefinite :
    L.IsIndefinite ↔ ¬L.IsPositiveSemidefinite ∧ ¬L.IsNegativeSemidefinite := by
  rw [IsIndefinite, L.isPositiveSemidefinite_iff_sigNeg_eq_zero,
    L.isNegativeSemidefinite_iff_sigPos_eq_zero]
  omega

/-- An indefinite lattice has, and is characterized by, vectors of both signs. -/
@[grind =]
theorem isIndefinite_iff_exists_pos_and_exists_neg :
    L.IsIndefinite ↔ (∃ x : V, 0 < L.form x x) ∧ (∃ x : V, L.form x x < 0) := by
  rw [L.isIndefinite_iff_not_semidefinite, L.isPositiveSemidefinite_iff,
    L.isNegativeSemidefinite_iff]
  simp only [not_forall, not_le]
  exact and_comm

end IntegralLattice

end TauCeti
