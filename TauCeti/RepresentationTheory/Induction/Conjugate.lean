/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RepresentationTheory.Character
public import TauCeti.RepresentationTheory.Restriction

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
* `TauCeti.conjRepEquivalence`: conjugation as an equivalence of representation categories.
* `TauCeti.conjRepSubrepresentationOrderIso`: the invariant-subspace correspondence under
  conjugation.
* `TauCeti.isIrreducible_conjRep_iff`: conjugation preserves irreducibility.
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
@[simp]
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

/-- Conjugation by a group element is an equivalence of representation categories. -/
noncomputable def conjRepEquivalence [Semiring k] (s : G) (H : Subgroup G) :
    Rep k H ≌ Rep k (MulAut.conj s • H : Subgroup G) :=
  Rep.resEquivalence (conjSubgroupEquiv s H)

/-- The forward functor of the conjugation equivalence is restriction along conjugation. -/
@[simp]
theorem conjRepEquivalence_functor [Semiring k] (s : G) (H : Subgroup G) :
    (conjRepEquivalence (k := k) s H).functor = conjRepFunctor s H := by
  rw [conjRepEquivalence, Rep.resEquivalence_functor]
  rfl

/-- The inverse functor of the conjugation equivalence restricts along inverse conjugation. -/
@[simp]
theorem conjRepEquivalence_inverse [Semiring k] (s : G) (H : Subgroup G) :
    (conjRepEquivalence (k := k) s H).inverse =
      Rep.resFunctor (conjSubgroupEquiv s H).symm.toMonoidHom := by
  rw [conjRepEquivalence, Rep.resEquivalence_inverse]

/-- The unit of the conjugation equivalence has the identity underlying linear map. -/
@[simp]
theorem conjRepEquivalence_unitIso_hom_app_toLinearMap [Semiring k] (s : G) (H : Subgroup G)
    (A : Rep k H) :
    HEq ((conjRepEquivalence (k := k) s H).unitIso.hom.app A).hom.toLinearMap
      (LinearMap.id : A.V →ₗ[k] A.V) := by
  exact Rep.resEquivalence_unitIso_hom_app_toLinearMap (conjSubgroupEquiv s H) A

/-- The inverse of the unit of the conjugation equivalence has the identity underlying
linear map. -/
@[simp]
theorem conjRepEquivalence_unitIso_inv_app_toLinearMap [Semiring k] (s : G) (H : Subgroup G)
    (A : Rep k H) :
    HEq ((conjRepEquivalence (k := k) s H).unitIso.inv.app A).hom.toLinearMap
      (LinearMap.id : A.V →ₗ[k] A.V) := by
  exact Rep.resEquivalence_unitIso_inv_app_toLinearMap (conjSubgroupEquiv s H) A

/-- The counit of the conjugation equivalence has the identity underlying linear map. -/
@[simp]
theorem conjRepEquivalence_counitIso_hom_app_toLinearMap [Semiring k] (s : G) (H : Subgroup G)
    (A : Rep k (MulAut.conj s • H : Subgroup G)) :
    HEq ((conjRepEquivalence (k := k) s H).counitIso.hom.app A).hom.toLinearMap
      (LinearMap.id : A.V →ₗ[k] A.V) := by
  exact Rep.resEquivalence_counitIso_hom_app_toLinearMap (conjSubgroupEquiv s H) A

/-- The inverse of the counit of the conjugation equivalence has the identity underlying
linear map. -/
@[simp]
theorem conjRepEquivalence_counitIso_inv_app_toLinearMap [Semiring k] (s : G) (H : Subgroup G)
    (A : Rep k (MulAut.conj s • H : Subgroup G)) :
    HEq ((conjRepEquivalence (k := k) s H).counitIso.inv.app A).hom.toLinearMap
      (LinearMap.id : A.V →ₗ[k] A.V) := by
  exact Rep.resEquivalence_counitIso_inv_app_toLinearMap (conjSubgroupEquiv s H) A

/-- Conjugation preserves the underlying module of a representation. -/
@[simp]
theorem conjRep_V [Semiring k] (s : G) {H : Subgroup G} (A : Rep k H) :
    (conjRep s A).V = A.V := by
  -- Unfold the local wrappers to expose Mathlib's restriction carrier.
  change (Rep.res (conjSubgroupEquiv s H).toMonoidHom A).V = A.V
  exact Rep.res_obj_V _ _

/-- Conjugation preserves the underlying linear map of a representation morphism. -/
theorem conjRepFunctor_map_hom_toLinearMap [Semiring k] (s : G) {H : Subgroup G}
    {A B : Rep k H} (f : A ⟶ B) :
    HEq ((conjRepFunctor s H).map f).hom.toLinearMap f.hom.toLinearMap := by
  -- Unfold the local functor wrapper to expose Mathlib's restriction map.
  change HEq (Rep.resMap (conjSubgroupEquiv s H).toMonoidHom f).hom.toLinearMap _
  exact heq_of_eq (Rep.resMap_hom_toLinearMap _ _)

/-- The conjugate action, as a heterogeneous equality: `conjRep` is opaque, so
`(conjRep s A).V` and `A.V` are equal only via `conjRep_V`, not definitionally. -/
theorem conjRep_ρ [Semiring k] (s : G) {H : Subgroup G} (A : Rep k H)
    (x : (MulAut.conj s • H : Subgroup G)) :
    HEq ((conjRep s A).ρ x) (A.ρ (conjSubgroupEquiv s H x)) := by
  -- Unfold the local wrappers to expose Mathlib's restricted action.
  change HEq ((Rep.res (conjSubgroupEquiv s H).toMonoidHom A).ρ x) _
  exact heq_of_eq (Rep.coe_res_obj_ρ' _ _ _)

/-- The conjugate action on elements, transported along `conjRep_V`. -/
theorem conjRep_ρ_apply [Semiring k] (s : G) {H : Subgroup G} (A : Rep k H)
    (x : (MulAut.conj s • H : Subgroup G)) (v : A.V) :
    cast (conjRep_V s A) ((conjRep s A).ρ x (cast (conjRep_V s A).symm v)) =
      A.ρ (conjSubgroupEquiv s H x) v := by
  -- Unfold the local wrapper to expose Mathlib's restricted action; both casts are along the
  -- definitional carrier equality `Rep.res_obj_V`.
  change (Rep.res (conjSubgroupEquiv s H).toMonoidHom A).ρ x v = _
  exact LinearMap.congr_fun (Rep.coe_res_obj_ρ' _ _ x) v

/-- The action of the conjugate representation, written directly in the ambient group. -/
theorem conjRep_ρ_mk [Semiring k] (s : G) {H : Subgroup G} (A : Rep k H)
    (x : (MulAut.conj s • H : Subgroup G)) :
    HEq ((conjRep s A).ρ x)
      (A.ρ ⟨s⁻¹ * (x : G) * s, (mem_conj_smul s H x).mp x.2⟩) := by
  apply (conjRep_ρ s A x).trans
  congr 1

/-- Conjugation identifies the invariant subspaces of a representation with those of its
conjugate. -/
def conjRepSubrepresentationOrderIso [Semiring k] (s : G) {H : Subgroup G} (A : Rep.{w} k H) :
    Subrepresentation (conjRep s A).ρ ≃o Subrepresentation A.ρ := by
  change Subrepresentation (A.ρ.comp (conjSubgroupEquiv s H).toMonoidHom) ≃o
    Subrepresentation A.ρ
  exact Rep.resSubrepresentationOrderIso (conjSubgroupEquiv s H) A

/-- The forward invariant-subspace correspondence preserves the underlying submodule. -/
@[simp]
theorem conjRepSubrepresentationOrderIso_apply_toSubmodule [Semiring k] (s : G)
    {H : Subgroup G} (A : Rep.{w} k H) (S : Subrepresentation (conjRep s A).ρ) :
    HEq (conjRepSubrepresentationOrderIso s A S).toSubmodule S.toSubmodule := by
  unfold conjRepSubrepresentationOrderIso
  exact heq_of_eq (Rep.resSubrepresentationOrderIso_apply_toSubmodule
    (conjSubgroupEquiv s H) A S)

/-- The inverse invariant-subspace correspondence preserves the underlying submodule. -/
@[simp]
theorem conjRepSubrepresentationOrderIso_symm_apply_toSubmodule [Semiring k] (s : G)
    {H : Subgroup G} (A : Rep.{w} k H) (S : Subrepresentation A.ρ) :
    HEq ((conjRepSubrepresentationOrderIso s A).symm S).toSubmodule S.toSubmodule := by
  unfold conjRepSubrepresentationOrderIso
  exact heq_of_eq (Rep.resSubrepresentationOrderIso_symm_apply_toSubmodule
    (conjSubgroupEquiv s H) A S)

/-- A conjugate representation is irreducible exactly when the original representation is. -/
@[simp]
theorem isIrreducible_conjRep_iff [Field k] (s : G) {H : Subgroup G} (A : Rep.{w} k H) :
    Representation.IsIrreducible (conjRep s A).ρ ↔
      Representation.IsIrreducible A.ρ :=
  Rep.isIrreducible_comp_equiv_iff (conjSubgroupEquiv s H) A

section FDRep

variable [CommRing k]

/-- The conjugate of a finite-dimensional representation. -/
noncomputable def conjFDRep (s : G) {H : Subgroup G} (A : FDRep k H) :
    FDRep k (MulAut.conj s • H : Subgroup G) :=
  FDRep.of (A.ρ.comp (conjSubgroupEquiv s H).toMonoidHom)

/-- Conjugation preserves the underlying module of a finite-dimensional representation. -/
@[simp]
theorem conjFDRep_V (s : G) {H : Subgroup G} (A : FDRep k H) :
    (conjFDRep s A).V = A.V := by
  rfl

/-- The conjugate finite-dimensional action, as a heterogeneous equality. -/
theorem conjFDRep_ρ (s : G) {H : Subgroup G} (A : FDRep k H)
    (x : (MulAut.conj s • H : Subgroup G)) :
    HEq ((conjFDRep s A).ρ x) (A.ρ (conjSubgroupEquiv s H x)) := by
  -- Unfold the local wrapper to expose the action of Mathlib's `FDRep.of`.
  change HEq ((FDRep.of (A.ρ.comp (conjSubgroupEquiv s H).toMonoidHom)).ρ x) _
  rw [FDRep.of_ρ']
  rfl

/-- The conjugate action, transported along `conjFDRep_V`. -/
theorem conjFDRep_ρ_cast (s : G) {H : Subgroup G} (A : FDRep k H)
    (x : (MulAut.conj s • H : Subgroup G)) :
    cast (congrArg (fun V : FGModuleCat k => V →ₗ[k] V) (conjFDRep_V s A))
      ((conjFDRep s A).ρ x) = A.ρ (conjSubgroupEquiv s H x) := by
  -- Unfold the local wrapper to expose the action of Mathlib's `FDRep.of`.
  change (FDRep.of (A.ρ.comp (conjSubgroupEquiv s H).toMonoidHom)).ρ x = _
  rw [FDRep.of_ρ']
  rfl

/-- Conjugation preserves the dimension (finrank) of a finite-dimensional representation. -/
@[simp]
theorem finrank_conjFDRep (s : G) {H : Subgroup G} (A : FDRep k H) :
    Module.finrank k (conjFDRep s A) = Module.finrank k A := by
  exact congrArg (fun V : FGModuleCat k => Module.finrank k V) (conjFDRep_V s A)

end FDRep

section Character

variable [Field k]

/-- The character of a conjugate representation is evaluated through `conjSubgroupEquiv`. -/
@[simp]
theorem char_conjFDRep (s : G) {H : Subgroup G} (A : FDRep k H)
    (x : (MulAut.conj s • H : Subgroup G)) :
    (conjFDRep s A).character x = A.character (conjSubgroupEquiv s H x) := by
  rw [FDRep.character, FDRep.character]
  congr 1

/-- The conjugate-character formula `({}^s χ)(x) = χ(s⁻¹xs)`. -/
theorem char_conjFDRep_mk (s : G) {H : Subgroup G} (A : FDRep k H)
    (x : (MulAut.conj s • H : Subgroup G)) :
    (conjFDRep s A).character x =
      A.character ⟨s⁻¹ * (x : G) * s, (mem_conj_smul s H x).mp x.2⟩ := by
  rw [char_conjFDRep]
  congr 1

end Character

end TauCeti
