/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import TauCeti.Algebra.Lie.Weights.Central

/-!
# Restricting representations between `gl n` and `sl n`

Over a characteristic-zero field, `gl n` is the sum of `sl n` and the scalar matrices. This file
uses that decomposition in both directions needed by highest-weight theory: an irreducible `gl n`
module stays irreducible on restriction to `sl n`, and an equivalence of `sl n`-modules upgrades to
an equivalence of `gl n`-modules when the identity matrix acts by the same scalar on both modules.

The empty-rank case is included. For positive rank the decomposition is supplied by
`TauCeti.isCompl_center_derivedSeries_one_matrix`; in rank zero every matrix is zero.

## Main results

* `TauCeti.isIrreducible_restrict_sl`: restriction of a finite-dimensional irreducible `gl n`
  module to `sl n` is irreducible over an algebraically closed characteristic-zero field.
* `TauCeti.gl_equiv_of_sl_equiv_of_central_scalar`: an `sl n`-module equivalence between two
  modules with the same scalar action of the identity matrix is a `gl n`-module equivalence.

## References

These are the two pinned `sl ↔ gl` transfer statements in Layer 9 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`.
The exact suggested signature for the upgrade theorem is in
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/Suggested.lean`.
-/

public section

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

section Decomposition

variable {K : Type*} [Field K] [CharZero K]

/-- Every square matrix is the sum of a trace-zero matrix and a scalar matrix. This is the
elementwise form of the existing centre/derived-ideal complement; the separate rank-zero branch
avoids imposing invertibility of the cardinality of an empty index type. -/
private theorem exists_sl_add_smul_one_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    ∃ (X : LieAlgebra.SpecialLinear.sl (Fin n) K) (r : K),
      (X : Matrix (Fin n) (Fin n) K) + r • 1 = A := by
  cases n with
  | zero =>
      exact ⟨0, 0, Subsingleton.elim _ _⟩
  | succ n =>
      have hcard : (Fintype.card (Fin (n + 1)) : K) ≠ 0 := by
        rw [Fintype.card_fin]
        exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
      let _ : Invertible (Fintype.card (Fin (n + 1)) : K) :=
        invertibleOfNonzero hcard
      obtain ⟨Z, X, hZ, hX, hZX⟩ := Submodule.codisjoint_iff_exists_add_eq.mp
        (isCompl_center_derivedSeries_one_matrix K (Fin (n + 1))).codisjoint A
      obtain ⟨r, rfl⟩ := mem_center_matrix_iff.mp hZ
      have hXsl : X ∈ LieAlgebra.SpecialLinear.sl (Fin (n + 1)) K := by
        rw [← derivedSeries_one_toLieSubalgebra_eq_sl K (Fin (n + 1))]
        exact hX
      exact ⟨⟨X, hXsl⟩, r, (add_comm X (r • 1)).trans hZX⟩

end Decomposition

section Restriction

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
variable {n : ℕ} {M : Type u} [AddCommGroup M] [Module K M]
variable [LieRingModule (Matrix (Fin n) (Fin n) K) M]
  [LieModule K (Matrix (Fin n) (Fin n) K) M]
  [FiniteDimensional K M]
  [LieModule.IsIrreducible K (Matrix (Fin n) (Fin n) K) M]

/-- A finite-dimensional irreducible representation of `gl n` over an algebraically closed
characteristic-zero field stays irreducible after restriction to `sl n`. -/
theorem isIrreducible_restrict_sl :
    LieModule.IsIrreducible K (LieAlgebra.SpecialLinear.sl (Fin n) K) M := by
  apply isIrreducible_of_sup_center_eq_top K (Matrix (Fin n) (Fin n) K) M
  apply top_unique
  intro A _
  obtain ⟨X, r, hA⟩ := exists_sl_add_smul_one_eq A
  refine Submodule.mem_sup.mpr ⟨X, X.property, r • 1, ?_, hA⟩
  rw [LieSubmodule.mem_toSubmodule]
  exact mem_center_matrix_iff.mpr ⟨r, rfl⟩

end Restriction

section Upgrade

variable {K : Type*} [Field K] [CharZero K]
variable {n : ℕ} {M M' : Type u}
variable [AddCommGroup M] [Module K M]
  [LieRingModule (Matrix (Fin n) (Fin n) K) M]
  [LieModule K (Matrix (Fin n) (Fin n) K) M]
variable [AddCommGroup M'] [Module K M']
  [LieRingModule (Matrix (Fin n) (Fin n) K) M']
  [LieModule K (Matrix (Fin n) (Fin n) K) M']

/-- An equivalence of `sl n`-modules upgrades to an equivalence of `gl n`-modules when the identity
matrix acts by the same scalar on both modules. No irreducibility or finite-dimensionality is
needed. -/
theorem gl_equiv_of_sl_equiv_of_central_scalar (c : K)
    (hM : ∀ m : M, ⁅(1 : Matrix (Fin n) (Fin n) K), m⁆ = c • m)
    (hM' : ∀ m : M', ⁅(1 : Matrix (Fin n) (Fin n) K), m⁆ = c • m)
    (e : Nonempty (M ≃ₗ⁅K, LieAlgebra.SpecialLinear.sl (Fin n) K⁆ M')) :
    Nonempty (M ≃ₗ⁅K, Matrix (Fin n) (Fin n) K⁆ M') := by
  obtain ⟨e⟩ := e
  refine ⟨{ e.toLinearEquiv with map_lie' := ?_ }⟩
  intro A m
  -- The anonymous constructor exposes its `toFun` only after the bundled linear equivalence is
  -- unfolded; the restricted `sl n` action is then definitionally the ambient matrix action.
  change e ⁅A, m⁆ = ⁅A, e m⁆
  obtain ⟨X, r, hA⟩ := exists_sl_add_smul_one_eq A
  have hXaction :
      e ⁅(X : Matrix (Fin n) (Fin n) K), m⁆ = ⁅(X : Matrix (Fin n) (Fin n) K), e m⁆ := by
    simpa only [LieSubalgebra.coe_bracket_of_module, LieModuleEquiv.coe_toLieModuleHom]
      using e.map_lie X m
  simp only [← hA, add_lie, map_add, hXaction, smul_lie, hM, hM', map_smul]

end Upgrade

end TauCeti
