/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Rep.Res

/-!
# Restriction of representations

This file collects restriction infrastructure shared by the induction files: how the restriction
functors `Rep.resFunctor` and `Action.res` behave under composing and inverting the homomorphism
restricted along, and, for a subgroup `S` of a group `G`, the restriction of a finite-dimensional
representation of `G` to `S` together with its character.  Restricting along a surjective
homomorphism changes nothing essential: it identifies the lattices of invariant subspaces, and
hence preserves irreducibility.

`FDRep k G` is by definition `Action (FGModuleCat k) G`, so Mathlib's `Action.res` along
`S.subtype` *is* the restriction functor `FDRep k G ⥤ FDRep k S`; nothing has to be built.
Accordingly `resFDRep` is a reducible abbreviation for that functor on objects, exactly as
Mathlib's `Rep.res` is one for `Rep.resFunctor` on objects, and everything functorial —
restriction of an intertwiner, the functor laws, naturality — is used straight from
`Action.res (FGModuleCat k) S.subtype` and its `@[simps]` lemmas (`Action.res_obj_V`,
`Action.res_obj_ρ`, `Action.res_map_hom`) rather than restated here.

## Main definitions

* `TauCeti.resFunctorEquiv`: restriction along a monoid isomorphism, as an equivalence of
  categories.
* `TauCeti.resSubrepresentationOrderIso`: restriction along a surjective monoid homomorphism
  identifies the lattices of invariant subspaces.
* `TauCeti.resFDRep`: restriction of a finite-dimensional representation to a subgroup.

## Main statements

* `TauCeti.resFunctor_comp`, `TauCeti.actionRes_comp`: restriction along a composite is
  restriction twice over.
* `TauCeti.isIrreducible_comp_surjective_iff`: restriction along a surjective monoid homomorphism
  preserves irreducibility, with `TauCeti.isIrreducible_comp_equiv_iff` as the isomorphism case.

## Implementation notes

The abbreviation is over a commutative ring, matching Mathlib's `Action.res`; `Field k` enters
only with `FDRep.character`.

## References

This is restriction infrastructure for Layer 2 of
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

variable {k G : Type u} [Group G]

section Functor

variable [Semiring k] {H K L : Type*} [Monoid H] [Monoid K] [Monoid L]

/-- Restricting representations along a composite homomorphism is restricting twice over.
Mathlib has no equality of this shape (`Action.resComp` is the natural isomorphism for `Action`),
so we record the equality form, which keeps the reduction out of proofs that state equalities of
restriction functors. -/
theorem resFunctor_comp (φ : K →* L) (ψ : H →* K) :
    Rep.resFunctor (k := k) (φ.comp ψ) = Rep.resFunctor φ ⋙ Rep.resFunctor ψ :=
  rfl

/-- The `Action` form of `resFunctor_comp`, which is the one that applies to `FDRep`; the equality
strengthens Mathlib's natural isomorphism `Action.resComp`. -/
theorem actionRes_comp {V : Type*} [Category V] (φ : K →* L) (ψ : H →* K) :
    Action.res V (φ.comp ψ) = Action.res V φ ⋙ Action.res V ψ :=
  rfl

/-- Restricting along the identity is the identity functor. -/
theorem resFunctor_id : Rep.resFunctor (k := k) (MonoidHom.id H) = 𝟭 (Rep k H) :=
  rfl

/-- Restriction along a monoid isomorphism is an equivalence of categories, with inverse
restriction along the inverse isomorphism.  This is the `Rep` analogue of Mathlib's
`Action.resEquiv`, which does not apply because `Rep` is a structure rather than an `Action`.

The body is sealed; `resFunctorEquiv_functor` and `resFunctorEquiv_inverse` are the interface
identifying its two functors with restriction. -/
def resFunctorEquiv (e : H ≃* K) : Rep k K ≌ Rep k H :=
  -- Mathlib's `MulEquiv.coe_monoidHom_comp_coe_monoidHom_symm` and its mirror, restated for
  -- `MulEquiv.toMonoidHom`: the coercion in those lemmas is `toMonoidHom` definitionally but not
  -- syntactically, so `rw` needs this form.
  have comp_symm : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id K :=
    MulEquiv.coe_monoidHom_comp_coe_monoidHom_symm e
  have symm_comp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id H :=
    MulEquiv.coe_monoidHom_symm_comp_coe_monoidHom e
  CategoryTheory.Equivalence.mk (Rep.resFunctor e.toMonoidHom) (Rep.resFunctor e.symm.toMonoidHom)
    (eqToIso (by rw [← resFunctor_comp, comp_symm, resFunctor_id]))
    (eqToIso (by rw [← resFunctor_comp, symm_comp, resFunctor_id]))

@[simp]
theorem resFunctorEquiv_functor (e : H ≃* K) :
    (resFunctorEquiv (k := k) e).functor = Rep.resFunctor e.toMonoidHom :=
  (rfl)

@[simp]
theorem resFunctorEquiv_inverse (e : H ≃* K) :
    (resFunctorEquiv (k := k) e).inverse = Rep.resFunctor e.symm.toMonoidHom :=
  (rfl)

end Functor

section Subrepresentation

variable [Semiring k] {H K : Type*} [Monoid H] [Monoid K] {V : Type*} [AddCommMonoid V] [Module k V]

/-- Restriction along a surjective monoid homomorphism identifies invariant subspaces: a subspace
invariant under `ρ ∘ f` is invariant under `ρ`, because `f` is onto.  Both directions keep the
underlying submodule. -/
def resSubrepresentationOrderIso (f : H →* K) (hf : Function.Surjective f)
    (ρ : Representation k K V) :
    Subrepresentation (ρ.comp f) ≃o Subrepresentation ρ where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun h v hv ↦ by
        obtain ⟨g, rfl⟩ := hf h
        exact S.apply_mem_toSubmodule g hv }
  invFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun h v hv ↦ S.apply_mem_toSubmodule (f h) hv }
  left_inv S := by ext; rfl
  right_inv S := by ext; rfl
  map_rel_iff' := by rfl

/-- The forward invariant-subspace correspondence preserves the underlying submodule. -/
@[simp]
theorem resSubrepresentationOrderIso_apply_toSubmodule (f : H →* K) (hf : Function.Surjective f)
    (ρ : Representation k K V) (S : Subrepresentation (ρ.comp f)) :
    (resSubrepresentationOrderIso f hf ρ S).toSubmodule = S.toSubmodule :=
  (rfl)

/-- The inverse invariant-subspace correspondence preserves the underlying submodule. -/
@[simp]
theorem resSubrepresentationOrderIso_symm_apply_toSubmodule (f : H →* K)
    (hf : Function.Surjective f) (ρ : Representation k K V) (S : Subrepresentation ρ) :
    ((resSubrepresentationOrderIso f hf ρ).symm S).toSubmodule = S.toSubmodule :=
  (rfl)

end Subrepresentation

section Irreducible

variable [Field k] {H K : Type*} [Monoid H] [Monoid K]

/-- Restriction along a surjective monoid homomorphism preserves irreducibility: irreducibility is
simplicity of the lattice of invariant subspaces, and `resSubrepresentationOrderIso` identifies
the two lattices. -/
@[simp]
theorem isIrreducible_comp_surjective_iff {V : Type*} [AddCommGroup V] [Module k V]
    (f : H →* K) (hf : Function.Surjective f) (ρ : Representation k K V) :
    Representation.IsIrreducible (ρ.comp f) ↔ Representation.IsIrreducible ρ :=
  (resSubrepresentationOrderIso f hf ρ).isSimpleOrder_iff

/-- Restriction along a monoid isomorphism preserves irreducibility. -/
@[simp]
theorem isIrreducible_comp_equiv_iff {V : Type*} [AddCommGroup V] [Module k V] (e : H ≃* K)
    (ρ : Representation k K V) :
    Representation.IsIrreducible (ρ.comp (e : H →* K)) ↔ Representation.IsIrreducible ρ :=
  isIrreducible_comp_surjective_iff e.toMonoidHom e.surjective ρ

end Irreducible

section Representation

variable [CommRing k]

/-- Restriction of a finite-dimensional representation of `G` to a subgroup `S`: Mathlib's
`Action.res` along `S.subtype`, under the definitional identification
`FDRep k G = Action (FGModuleCat k) G`.

This is a reducible abbreviation, so Mathlib's `Action.res` API applies to it unchanged; in
particular `(Action.res (FGModuleCat k) S.subtype).map f : resFDRep S B ⟶ resFDRep S B'`
restricts an intertwiner, and is functorial by `Functor.map_id` and `Functor.map_comp`. -/
abbrev resFDRep (S : Subgroup G) (B : FDRep k G) : FDRep k S :=
  (Action.res (FGModuleCat k) S.subtype).obj B

/-- Restriction commutes with forgetting finite-dimensionality: after forgetting, `resFDRep` is
Mathlib's `Rep.res`, on the nose rather than up to isomorphism. -/
@[simp]
theorem forget₂_obj_resFDRep (S : Subgroup G) (B : FDRep k G) :
    (forget₂ (FDRep k S) (Rep k S)).obj (resFDRep S B) =
      Rep.res S.subtype ((forget₂ (FDRep k G) (Rep k G)).obj B) :=
  rfl

end Representation

section Character

variable [Field k]

/-- The character of a restriction is the restriction of the character. -/
@[simp]
theorem character_resFDRep (S : Subgroup G) (B : FDRep k G) (s : S) :
    (resFDRep S B).character s = B.character (s : G) :=
  rfl

end Character

end TauCeti
