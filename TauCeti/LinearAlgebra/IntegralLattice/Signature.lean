/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Norm
public import TauCeti.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# Signature and definiteness of integral lattices

This file defines the radical and signature `(n₊, n₀, n₋)` of an integral symmetric lattice and
the standard definiteness predicates. The indices of inertia are Mathlib's `sigPos`
and `sigNeg`; the null index is the dimension of the kernel of the bilinear form.

Positive- and negative-semidefiniteness are expressed using Mathlib's bilinear-form predicates.
The characteristic theorems relate every predicate both to the signature and to the usual
elementwise inequalities. In particular, an indefinite lattice has vectors of both signs, and a
degenerate lattice has a nonzero vector in its radical. The final section proves that an
integral-lattice isometry transports the radical and preserves all three inertia indices and every
definiteness predicate.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 1.

## Main definitions

* `TauCeti.IntegralLattice.radical`: the kernel of the rational bilinear form.
* `TauCeti.IntegralLattice.signature`: the positive, null, and negative indices.
* `TauCeti.IntegralLattice.IsPosSemidef` and related definiteness predicates.
* `TauCeti.IntegralLattice.Isometry.map_radical` and the `Isometry.sigPos_eq`, `sigNull_eq`, and
  `sigNeg_eq` theorems: isometry invariance of the signature.
-/

public section

namespace TauCeti

open QuadraticMap

universe u v

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)
variable {W : Type v} [AddCommGroup W] [Module ℚ W]

/-- The radical of an integral lattice is the kernel of its rational bilinear form. -/
def radical : Submodule ℚ V := L.form.ker

/-- A vector lies in the radical of an integral lattice if and only if it annihilates all
vectors under the rational bilinear form. -/
@[simp]
theorem mem_radical_iff (x : V) : x ∈ L.radical ↔ ∀ y : V, L.form x y = 0 := by
  simp only [radical, LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply]

/-- The radical of the quadratic form associated to a lattice is its bilinear radical. -/
@[simp]
theorem radical_toQuadraticMap : L.form.toQuadraticMap.radical = L.radical :=
  LinearMap.BilinForm.radical_toQuadraticMap L.form L.isSymm

/-- The positive index of inertia of an integral lattice. -/
noncomputable abbrev sigPos : ℕ := _root_.sigPos L.form.toQuadraticMap

/-- The dimension of the radical of an integral lattice. -/
noncomputable abbrev sigNull : ℕ := Module.finrank ℚ L.radical

/-- The negative index of inertia of an integral lattice. -/
noncomputable abbrev sigNeg : ℕ := _root_.sigNeg L.form.toQuadraticMap

/-- The signature `(n₊, n₀, n₋)` of an integral lattice. -/
noncomputable abbrev signature : ℕ × ℕ × ℕ := (L.sigPos, L.sigNull, L.sigNeg)

/-- The positive, null, and negative indices exhaust the rank of the lattice. -/
theorem signature_sum_eq_finrank :
    L.sigPos + L.sigNull + L.sigNeg = Module.finrank ℚ V := by
  have := L.finiteDimensional
  have h := _root_.QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := L.form.toQuadraticMap)
  rw [L.radical_toQuadraticMap] at h
  simpa only [sigPos, sigNull, sigNeg, add_comm, add_left_comm, add_assoc] using h

/-- An integral lattice is positive-definite when its quadratic form is positive on every nonzero
vector. -/
abbrev IsPosDef : Prop := L.form.toQuadraticMap.PosDef

/-- An integral lattice is positive-semidefinite when its symmetric bilinear form is nonnegative. -/
abbrev IsPosSemidef : Prop := L.form.IsPosSemidef

/-- An integral lattice is negative-definite when the negative of its quadratic form is
positive-definite. -/
abbrev IsNegDef : Prop := (-L.form.toQuadraticMap).PosDef

/-- An integral lattice is negative-semidefinite when the negative of its symmetric bilinear form
is positive-semidefinite. -/
abbrev IsNegSemidef : Prop := (-L.form).IsPosSemidef

/-- An integral lattice is degenerate when its radical is nontrivial. -/
def IsDegenerate : Prop := L.radical ≠ ⊥

/-- An integral lattice is indefinite when both its positive and negative indices are nonzero. -/
def IsIndefinite : Prop := 0 < L.sigPos ∧ 0 < L.sigNeg

/-- The radical of an integral lattice is trivial if and only if its null index vanishes. -/
theorem radical_eq_bot_iff_sigNull_eq_zero : L.radical = ⊥ ↔ L.sigNull = 0 := by
  have := L.finiteDimensional
  exact Submodule.finrank_eq_zero.symm

/-- Positive-definiteness has its usual elementwise characterization. -/
@[grind =]
theorem isPosDef_iff :
    L.IsPosDef ↔ ∀ x : V, x ≠ 0 → 0 < L.form x x := by
  simp only [IsPosDef, QuadraticMap.PosDef, LinearMap.BilinMap.toQuadraticMap_apply]

/-- Positive-semidefiniteness has its usual elementwise characterization. -/
@[grind =]
theorem isPosSemidef_iff :
    L.IsPosSemidef ↔ ∀ x : V, 0 ≤ L.form x x :=
  LinearMap.BilinForm.isPosSemidef_iff_forall_nonneg L.form L.isSymm

/-- Negative-definiteness has its usual elementwise characterization. -/
@[grind =]
theorem isNegDef_iff :
    L.IsNegDef ↔ ∀ x : V, x ≠ 0 → L.form x x < 0 := by
  simp only [IsNegDef, QuadraticMap.PosDef, neg_apply,
    LinearMap.BilinMap.toQuadraticMap_apply, neg_pos]

/-- Negative-semidefiniteness has its usual elementwise characterization. -/
@[grind =]
theorem isNegSemidef_iff :
    L.IsNegSemidef ↔ ∀ x : V, L.form x x ≤ 0 := by
  rw [IsNegSemidef, LinearMap.BilinForm.isPosSemidef_iff_forall_nonneg (-L.form) L.isSymm.neg]
  simp only [LinearMap.neg_apply, neg_nonneg]

/-- Positive-semidefiniteness is equivalent to the vanishing of the negative index. -/
@[grind =]
theorem isPosSemidef_iff_sigNeg_eq_zero :
    L.IsPosSemidef ↔ L.sigNeg = 0 := by
  have := L.finiteDimensional
  exact LinearMap.BilinForm.isPosSemidef_iff_sigNeg_eq_zero L.form L.isSymm

/-- Negative-semidefiniteness is equivalent to the vanishing of the positive index. -/
@[grind =]
theorem isNegSemidef_iff_sigPos_eq_zero :
    L.IsNegSemidef ↔ L.sigPos = 0 := by
  have := L.finiteDimensional
  rw [IsNegSemidef,
    LinearMap.BilinForm.isPosSemidef_iff_sigNeg_eq_zero (-L.form) L.isSymm.neg]
  simp only [LinearMap.BilinMap.toQuadraticMap_neg, sigNeg_neg, sigPos]

/-- Positive-definiteness is positive-semidefiniteness together with nondegeneracy. -/
@[grind =]
theorem isPosDef_iff_isPosSemidef_and_nondegenerate :
    L.IsPosDef ↔ L.IsPosSemidef ∧ L.form.Nondegenerate := by
  have := L.finiteDimensional
  exact LinearMap.BilinForm.posDef_toQuadraticMap_iff_isPosSemidef_and_nondegenerate
    L.form L.isSymm

/-- Positive-definiteness is equivalent to zero null and negative indices. -/
@[grind =]
theorem isPosDef_iff_sigNull_eq_zero_and_sigNeg_eq_zero :
    L.IsPosDef ↔ L.sigNull = 0 ∧ L.sigNeg = 0 := by
  have := L.finiteDimensional
  exact LinearMap.BilinForm.posDef_toQuadraticMap_iff_finrank_ker_eq_zero_and_sigNeg_eq_zero
    L.form L.isSymm

/-- Negative-definiteness is negative-semidefiniteness together with nondegeneracy. -/
@[grind =]
theorem isNegDef_iff_isNegSemidef_and_nondegenerate :
    L.IsNegDef ↔ L.IsNegSemidef ∧ L.form.Nondegenerate := by
  have := L.finiteDimensional
  rw [IsNegDef, IsNegSemidef, ← LinearMap.BilinMap.toQuadraticMap_neg]
  have h := LinearMap.BilinForm.posDef_toQuadraticMap_iff_isPosSemidef_and_nondegenerate
    (-L.form) L.isSymm.neg
  rw [h, LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot,
    LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot, LinearMap.ker_neg]

/-- Negative-definiteness is equivalent to zero positive and null indices. -/
@[grind =]
theorem isNegDef_iff_sigPos_eq_zero_and_sigNull_eq_zero :
    L.IsNegDef ↔ L.sigPos = 0 ∧ L.sigNull = 0 := by
  have := L.finiteDimensional
  have h := LinearMap.BilinForm.posDef_toQuadraticMap_iff_finrank_ker_eq_zero_and_sigNeg_eq_zero
    (-L.form) L.isSymm.neg
  rw [LinearMap.ker_neg, LinearMap.BilinMap.toQuadraticMap_neg, sigNeg_neg] at h
  rw [IsNegDef, h, and_comm, sigNull, radical]

/-- Degeneracy is equivalent to a positive null index. -/
@[grind =]
theorem isDegenerate_iff_sigNull_pos : L.IsDegenerate ↔ 0 < L.sigNull := by
  have := L.finiteDimensional
  simp only [IsDegenerate, ne_eq, L.radical_eq_bot_iff_sigNull_eq_zero]
  exact Nat.pos_iff_ne_zero.symm

/-- A lattice is degenerate exactly when its bilinear form is not nondegenerate. -/
@[grind =]
theorem isDegenerate_iff_not_nondegenerate : L.IsDegenerate ↔ ¬L.form.Nondegenerate := by
  have := L.finiteDimensional
  simp only [IsDegenerate, radical, LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot]

/-- A lattice is degenerate exactly when its radical contains a nonzero vector. -/
@[grind =]
theorem isDegenerate_iff_exists_mem_radical_ne_zero :
    L.IsDegenerate ↔ ∃ x : V, x ∈ L.radical ∧ x ≠ 0 := by
  simp only [IsDegenerate]
  exact L.radical.ne_bot_iff

/-- Indefiniteness is equivalent to the failure of both semidefiniteness conditions. -/
@[grind =]
theorem isIndefinite_iff_not_semidef :
    L.IsIndefinite ↔ ¬L.IsPosSemidef ∧ ¬L.IsNegSemidef := by
  rw [IsIndefinite, L.isPosSemidef_iff_sigNeg_eq_zero,
    L.isNegSemidef_iff_sigPos_eq_zero]
  omega

/-- An indefinite lattice has, and is characterized by, vectors of both signs. -/
@[grind =]
theorem isIndefinite_iff_exists_pos_and_exists_neg :
    L.IsIndefinite ↔ (∃ x : V, 0 < L.form x x) ∧ (∃ x : V, L.form x x < 0) := by
  rw [L.isIndefinite_iff_not_semidef, L.isPosSemidef_iff,
    L.isNegSemidef_iff]
  simp only [not_forall, not_le]
  exact and_comm

namespace Isometry

variable {L : IntegralLattice V} {M : IntegralLattice W}

/-- An integral-lattice isometry maps the source radical onto the target radical. -/
@[simp]
theorem map_radical (e : Isometry L M) :
    L.radical.map (e : V ≃ₗ[ℚ] W).toLinearMap = M.radical := by
  rw [← L.radical_toQuadraticMap, ← M.radical_toQuadraticMap,
    ← L.norm_def, ← M.norm_def]
  simpa only [e.normIsometryEquiv_toLinearEquiv] using e.normIsometryEquiv.map_radical

/-- Isometric integral lattices have the same positive index. -/
theorem sigPos_eq (e : Isometry L M) : L.sigPos = M.sigPos := by
  have := L.finiteDimensional
  have := M.finiteDimensional
  rw [sigPos, sigPos, ← L.norm_def, ← M.norm_def]
  exact QuadraticMap.Equivalent.sigPos_eq ⟨e.normIsometryEquiv⟩

/-- Isometric integral lattices have the same null index. -/
theorem sigNull_eq (e : Isometry L M) : L.sigNull = M.sigNull := by
  have := L.finiteDimensional
  have := M.finiteDimensional
  rw [sigNull, sigNull, ← e.map_radical]
  exact (LinearEquiv.finrank_map_eq (e : V ≃ₗ[ℚ] W) L.radical).symm

/-- Isometric integral lattices have the same negative index. -/
theorem sigNeg_eq (e : Isometry L M) : L.sigNeg = M.sigNeg := by
  have := L.finiteDimensional
  have := M.finiteDimensional
  rw [sigNeg, sigNeg, ← L.norm_def, ← M.norm_def]
  exact QuadraticMap.Equivalent.sigNeg_eq ⟨e.normIsometryEquiv⟩

/-- Isometric integral lattices have the same signature. -/
theorem signature_eq (e : Isometry L M) : L.signature = M.signature := by
  rw [signature, signature, e.sigPos_eq, e.sigNull_eq, e.sigNeg_eq]

/-- Nondegeneracy of the ambient form is invariant under integral-lattice isometry. -/
theorem form_nondegenerate_iff (e : Isometry L M) :
    L.form.Nondegenerate ↔ M.form.Nondegenerate := by
  have := L.finiteDimensional
  have := M.finiteDimensional
  have hL : L.form.ker = L.radical :=
    (LinearMap.BilinForm.radical_toQuadraticMap L.form L.isSymm).symm.trans
      L.radical_toQuadraticMap
  have hM : M.form.ker = M.radical :=
    (LinearMap.BilinForm.radical_toQuadraticMap M.form M.isSymm).symm.trans
      M.radical_toQuadraticMap
  rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot,
    LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot, hL, hM, ← e.map_radical]
  exact Submodule.map_eq_bot_iff.symm

/-- Transport the nondegeneracy mixin along an integral-lattice isometry. -/
theorem isNondegenerate (e : Isometry L M) [L.IsNondegenerate] : M.IsNondegenerate :=
  ⟨e.form_nondegenerate_iff.mp L.form_nondegenerate⟩

/-- The nondegeneracy mixin is invariant under integral-lattice isometry. -/
theorem isNondegenerate_iff (e : Isometry L M) : L.IsNondegenerate ↔ M.IsNondegenerate := by
  constructor <;> rintro ⟨h⟩
  · exact ⟨e.form_nondegenerate_iff.mp h⟩
  · exact ⟨e.form_nondegenerate_iff.mpr h⟩

/-- Positive-definiteness is invariant under integral-lattice isometry. -/
theorem isPosDef_iff (e : Isometry L M) : L.IsPosDef ↔ M.IsPosDef := by
  rw [M.isPosDef_iff_sigNull_eq_zero_and_sigNeg_eq_zero,
    L.isPosDef_iff_sigNull_eq_zero_and_sigNeg_eq_zero, ← e.sigNull_eq, ← e.sigNeg_eq]

/-- Positive-semidefiniteness is invariant under integral-lattice isometry. -/
theorem isPosSemidef_iff (e : Isometry L M) : L.IsPosSemidef ↔ M.IsPosSemidef := by
  rw [M.isPosSemidef_iff_sigNeg_eq_zero, L.isPosSemidef_iff_sigNeg_eq_zero, ← e.sigNeg_eq]

/-- Negative-definiteness is invariant under integral-lattice isometry. -/
theorem isNegDef_iff (e : Isometry L M) : L.IsNegDef ↔ M.IsNegDef := by
  rw [M.isNegDef_iff_sigPos_eq_zero_and_sigNull_eq_zero,
    L.isNegDef_iff_sigPos_eq_zero_and_sigNull_eq_zero, ← e.sigPos_eq, ← e.sigNull_eq]

/-- Negative-semidefiniteness is invariant under integral-lattice isometry. -/
theorem isNegSemidef_iff (e : Isometry L M) : L.IsNegSemidef ↔ M.IsNegSemidef := by
  rw [M.isNegSemidef_iff_sigPos_eq_zero, L.isNegSemidef_iff_sigPos_eq_zero, ← e.sigPos_eq]

/-- Degeneracy is invariant under integral-lattice isometry. -/
theorem isDegenerate_iff (e : Isometry L M) : L.IsDegenerate ↔ M.IsDegenerate := by
  rw [M.isDegenerate_iff_sigNull_pos, L.isDegenerate_iff_sigNull_pos, ← e.sigNull_eq]

/-- Indefiniteness is invariant under integral-lattice isometry. -/
theorem isIndefinite_iff (e : Isometry L M) : L.IsIndefinite ↔ M.IsIndefinite := by
  rw [IsIndefinite, IsIndefinite, ← e.sigPos_eq, ← e.sigNeg_eq]

end Isometry

end IntegralLattice

end TauCeti
