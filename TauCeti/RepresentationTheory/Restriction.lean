/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Rep.Res

/-!
# Restriction of representations

This file records the functoriality of restriction along composable monoid homomorphisms and
shows that restriction along a multiplicative equivalence is an equivalence of representation
categories. It also identifies the invariant subspaces, and hence irreducibility, of a
representation restricted along a multiplicative equivalence.

## Main definitions

* `TauCeti.Rep.resFunctorCompIso`: restriction along a composite agrees with restriction in stages.
* `TauCeti.Rep.resEquivalence`: restriction along a multiplicative equivalence is a categorical
  equivalence.
* `TauCeti.Rep.resSubrepresentationOrderIso`: restriction along a multiplicative equivalence
  preserves the lattice of invariant subspaces.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w x

namespace Rep

variable {k : Type u} {G : Type v} {H : Type w} {K : Type x}

section Semiring

variable [Semiring k] [Monoid G] [Monoid H] [Monoid K]

/-- Restriction along two composable monoid homomorphisms is naturally isomorphic to restriction
along their composite. -/
noncomputable def resFunctorCompIso (φ : G →* H) (ψ : H →* K) :
    _root_.Rep.resFunctor.{max u v w x} (k := k) ψ ⋙
      _root_.Rep.resFunctor.{max u v w x} (k := k) φ ≅
        _root_.Rep.resFunctor.{max u v w x} (k := k) (ψ.comp φ) :=
  NatIso.ofComponents
    (fun A ↦ _root_.Rep.mkIso <|
      Representation.Equiv.mk (LinearEquiv.refl k A.V) fun _ ↦ by rfl)
    (by
      intro _ _ f
      ext
      rfl)

/-- The forward component of `resFunctorCompIso` acts as the identity on vectors. -/
@[simp↓]
lemma resFunctorCompIso_hom_app_apply (φ : G →* H) (ψ : H →* K) (A : _root_.Rep k K) (x : A.V) :
    ((resFunctorCompIso φ ψ).hom.app A) x = x := by
  unfold resFunctorCompIso
  rfl

/-- The inverse component of `resFunctorCompIso` acts as the identity on vectors. -/
@[simp↓]
lemma resFunctorCompIso_inv_app_apply (φ : G →* H) (ψ : H →* K) (A : _root_.Rep k K) (x : A.V) :
    ((resFunctorCompIso φ ψ).inv.app A) x = x := by
  unfold resFunctorCompIso
  rfl

/-- Restriction along a multiplicative equivalence is an equivalence of representation
categories. -/
noncomputable def resEquivalence (e : G ≃* H) :
    _root_.Rep k H ≌ _root_.Rep k G := by
  let unitIso :
      𝟭 (_root_.Rep k H) ≅
        _root_.Rep.resFunctor e.toMonoidHom ⋙
          _root_.Rep.resFunctor e.symm.toMonoidHom :=
    (NatIso.ofComponents
      (fun A ↦ _root_.Rep.mkIso <|
        Representation.Equiv.mk (LinearEquiv.refl k A.V) fun _ ↦ by
          -- Unfold the two restricted actions so the unit component reduces to cancellation
          -- by `e.apply_symm_apply`; both underlying linear maps are definitionally identities.
          change LinearMap.id.comp (A.ρ (e (e.symm _))) =
            (A.ρ _).comp LinearMap.id
          rw [LinearMap.id_comp, LinearMap.comp_id]
          rw [e.apply_symm_apply])
      (by
        intro A B f
        ext
        rfl)).symm.trans
      (resFunctorCompIso e.symm.toMonoidHom e.toMonoidHom).symm
  let counitIso :
      _root_.Rep.resFunctor e.symm.toMonoidHom ⋙
          _root_.Rep.resFunctor e.toMonoidHom ≅
        𝟭 (_root_.Rep k G) :=
    (resFunctorCompIso e.toMonoidHom e.symm.toMonoidHom).trans
      (NatIso.ofComponents
        (fun A ↦ _root_.Rep.mkIso <|
          Representation.Equiv.mk (LinearEquiv.refl k A.V) fun _ ↦ by
            -- Unfold the two restricted actions so the counit component reduces to cancellation
            -- by `e.symm_apply_apply`; both underlying linear maps are definitionally identities.
            change LinearMap.id.comp (A.ρ (e.symm (e _))) =
              (A.ρ _).comp LinearMap.id
            rw [LinearMap.id_comp, LinearMap.comp_id]
            rw [e.symm_apply_apply])
        (by
          intro A B f
          ext
          rfl))
  exact CategoryTheory.Equivalence.mk
    (_root_.Rep.resFunctor e.toMonoidHom)
    (_root_.Rep.resFunctor e.symm.toMonoidHom)
    unitIso counitIso

/-- The forward functor of restriction along an equivalence is restriction along its
underlying homomorphism. -/
@[simp]
theorem resEquivalence_functor (e : G ≃* H) :
    (resEquivalence (k := k) e).functor = _root_.Rep.resFunctor e.toMonoidHom := by
  rfl

/-- The inverse functor of restriction along an equivalence is restriction along the inverse
homomorphism. -/
@[simp]
theorem resEquivalence_inverse (e : G ≃* H) :
    (resEquivalence (k := k) e).inverse = _root_.Rep.resFunctor e.symm.toMonoidHom := by
  rfl

/-- The unit of restriction along an equivalence has the identity underlying linear map. -/
@[simp]
theorem resEquivalence_unitIso_hom_app_toLinearMap (e : G ≃* H) (A : _root_.Rep k H) :
    HEq ((resEquivalence (k := k) e).unitIso.hom.app A).hom.toLinearMap
      (LinearMap.id : A.V →ₗ[k] A.V) := by
  unfold resEquivalence
  rfl

/-- The inverse of the unit of restriction along an equivalence has the identity underlying
linear map. -/
@[simp]
theorem resEquivalence_unitIso_inv_app_toLinearMap (e : G ≃* H) (A : _root_.Rep k H) :
    HEq ((resEquivalence (k := k) e).unitIso.inv.app A).hom.toLinearMap
      (LinearMap.id : A.V →ₗ[k] A.V) := by
  unfold resEquivalence
  rfl

/-- The counit of restriction along an equivalence has the identity underlying linear map. -/
@[simp]
theorem resEquivalence_counitIso_hom_app_toLinearMap (e : G ≃* H) (A : _root_.Rep k G) :
    HEq ((resEquivalence (k := k) e).counitIso.hom.app A).hom.toLinearMap
      (LinearMap.id : A.V →ₗ[k] A.V) := by
  unfold resEquivalence
  rfl

/-- The inverse of the counit of restriction along an equivalence has the identity underlying
linear map. -/
@[simp]
theorem resEquivalence_counitIso_inv_app_toLinearMap (e : G ≃* H) (A : _root_.Rep k G) :
    HEq ((resEquivalence (k := k) e).counitIso.inv.app A).hom.toLinearMap
      (LinearMap.id : A.V →ₗ[k] A.V) := by
  unfold resEquivalence
  rfl

/-- Restriction along a multiplicative equivalence identifies invariant subspaces. -/
def resSubrepresentationOrderIso (e : G ≃* H) (A : _root_.Rep k H) :
    Subrepresentation (A.ρ.comp (e : G →* H)) ≃o Subrepresentation A.ρ :=
  { toFun := fun S ↦
      { toSubmodule := S.toSubmodule
        apply_mem_toSubmodule := fun h v hv ↦ by
          simpa using S.apply_mem_toSubmodule (e.symm h) hv }
    invFun := fun S ↦
      { toSubmodule := S.toSubmodule
        apply_mem_toSubmodule := fun g v hv ↦ S.apply_mem_toSubmodule (e g) hv }
    left_inv := fun S ↦ by ext; rfl
    right_inv := fun S ↦ by ext; rfl
    map_rel_iff' := by rfl }

/-- The forward invariant-subspace correspondence preserves the underlying submodule. -/
@[simp]
theorem resSubrepresentationOrderIso_apply_toSubmodule (e : G ≃* H) (A : _root_.Rep k H)
    (S : Subrepresentation (A.ρ.comp (e : G →* H))) :
    (resSubrepresentationOrderIso e A S).toSubmodule = S.toSubmodule := by
  rfl

/-- The inverse invariant-subspace correspondence preserves the underlying submodule. -/
@[simp]
theorem resSubrepresentationOrderIso_symm_apply_toSubmodule (e : G ≃* H) (A : _root_.Rep k H)
    (S : Subrepresentation A.ρ) :
    ((resSubrepresentationOrderIso e A).symm S).toSubmodule = S.toSubmodule := by
  rfl

end Semiring

section Field

variable [Field k] [Monoid G] [Monoid H]

/-- Restriction along a multiplicative equivalence preserves irreducibility. -/
@[simp]
theorem isIrreducible_comp_equiv_iff (e : G ≃* H) (A : _root_.Rep k H) :
    Representation.IsIrreducible (A.ρ.comp (e : G →* H)) ↔
      Representation.IsIrreducible A.ρ :=
  (resSubrepresentationOrderIso e A).isSimpleOrder_iff

end Field

end Rep

end TauCeti
