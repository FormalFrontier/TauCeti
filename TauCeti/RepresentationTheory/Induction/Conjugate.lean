/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RepresentationTheory.Character

/-!
# Conjugate representations

For a subgroup `H` of a group `G` and `s : G`, this file defines the conjugate of an
`H`-representation as a representation of `sHs⁻¹`.  The action is transported along the canonical
isomorphism

`sHs⁻¹ → H, x ↦ s⁻¹xs`.

This is the representation occurring in the summands of the Mackey decomposition.

## Main definitions

* `TauCeti.conjSubgroupEquiv`: the canonical isomorphism from `sHs⁻¹` to `H`.
* `TauCeti.conjRepFunctor`: conjugation as a functor between representation categories.
* `TauCeti.conjRep`: the conjugate of a representation.
* `TauCeti.conjFDRep`: the finite-dimensional version.

## References

The convention and implementation plan follow
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md` and its accompanying
`Suggested.lean`.
-/

public section

open CategoryTheory
open scoped Pointwise

universe u v w

namespace TauCeti

variable {k : Type u} {G : Type v} [Group G]

/-- Membership in `sHs⁻¹`, expressed using the conjugation convention used by `conjRep`. -/
theorem mem_conj_smul (s : G) (H : Subgroup G) (x : G) :
    x ∈ (MulAut.conj s • H : Subgroup G) ↔ s⁻¹ * x * s ∈ H := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp

/-- The canonical multiplicative equivalence `sHs⁻¹ ≃* H`, given by `x ↦ s⁻¹xs`. -/
def conjSubgroupEquiv (s : G) (H : Subgroup G) :
    (MulAut.conj s • H : Subgroup G) ≃* H :=
  (Subgroup.equivSMul (MulAut.conj s) H).symm

@[simp]
theorem coe_conjSubgroupEquiv_apply (s : G) (H : Subgroup G)
    (x : (MulAut.conj s • H : Subgroup G)) :
    (conjSubgroupEquiv s H x : G) = s⁻¹ * (x : G) * s := by
  simp [conjSubgroupEquiv]

@[simp]
theorem coe_conjSubgroupEquiv_symm_apply (s : G) (H : Subgroup G) (x : H) :
    ((conjSubgroupEquiv s H).symm x : G) = s * (x : G) * s⁻¹ := by
  simp [conjSubgroupEquiv]

/-- Conjugating representations by `s` is restriction along the isomorphism
`sHs⁻¹ ≃* H`. -/
def conjRepFunctor [Semiring k] (s : G) (H : Subgroup G) :
    Rep k H ⥤ Rep k (MulAut.conj s • H : Subgroup G) :=
  Rep.resFunctor (conjSubgroupEquiv s H).toMonoidHom

/-- The conjugate representation `{}^s A` of `sHs⁻¹`. -/
def conjRep [Semiring k] (s : G) {H : Subgroup G} (A : Rep k H) :
    Rep k (MulAut.conj s • H : Subgroup G) :=
  (conjRepFunctor s H).obj A

@[simp]
theorem conjRep_ρ [Semiring k] (s : G) {H : Subgroup G} (A : Rep k H)
    (x : (MulAut.conj s • H : Subgroup G)) :
    HEq ((conjRep s A).ρ x) (A.ρ (conjSubgroupEquiv s H x)) := by
  unfold conjRep conjRepFunctor
  rfl

/-- The action of the conjugate representation, written directly in the ambient group. -/
theorem conjRep_ρ_eq [Semiring k] (s : G) {H : Subgroup G} (A : Rep k H)
    (x : (MulAut.conj s • H : Subgroup G)) :
    HEq ((conjRep s A).ρ x)
      (A.ρ ⟨s⁻¹ * (x : G) * s, (mem_conj_smul s H x).mp x.2⟩) := by
  apply (conjRep_ρ s A x).trans
  congr 1

section FDRep

variable [CommRing k]

/-- The conjugate of a finite-dimensional representation. -/
noncomputable def conjFDRep (s : G) {H : Subgroup G} (A : FDRep k H) :
    FDRep k (MulAut.conj s • H : Subgroup G) :=
  FDRep.of (A.ρ.comp (conjSubgroupEquiv s H).toMonoidHom)

@[simp]
theorem conjFDRep_ρ (s : G) {H : Subgroup G} (A : FDRep k H)
    (x : (MulAut.conj s • H : Subgroup G)) :
    HEq ((conjFDRep s A).ρ x) (A.ρ (conjSubgroupEquiv s H x)) := by
  unfold conjFDRep
  rfl

end FDRep

section Character

variable [Field k]

@[simp]
theorem conjFDRep_character (s : G) {H : Subgroup G} (A : FDRep k H)
    (x : (MulAut.conj s • H : Subgroup G)) :
    (conjFDRep s A).character x = A.character (conjSubgroupEquiv s H x) := by
  unfold conjFDRep
  rfl

/-- The conjugate-character formula `({}^s χ)(x) = χ(s⁻¹xs)`. -/
theorem conjFDRep_character_eq (s : G) {H : Subgroup G} (A : FDRep k H)
    (x : (MulAut.conj s • H : Subgroup G)) :
    (conjFDRep s A).character x =
      A.character ⟨s⁻¹ * (x : G) * s, (mem_conj_smul s H x).mp x.2⟩ := by
  rw [conjFDRep_character]
  congr 1

/-- Conjugation preserves the dimension (finrank) of a finite-dimensional representation. -/
@[simp]
theorem finrank_conjFDRep (s : G) {H : Subgroup G} (A : FDRep k H) :
    Module.finrank k (conjFDRep s A) = Module.finrank k A := by
  unfold conjFDRep
  rfl

end Character

end TauCeti
