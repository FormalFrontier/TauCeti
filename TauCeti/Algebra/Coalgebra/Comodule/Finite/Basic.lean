/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import TauCeti.Algebra.Coalgebra.Comodule.Zero

/-!
# Finitely generated comodules

This file packages finitely generated right comodules over a coalgebra as a full subcategory
of `ComoduleCat`. An object of `FGComoduleCat R C` is a right `C`-comodule whose underlying
`R`-module is finitely generated; over a field this is the finite-dimensional comodule
category requested by the reductive-groups roadmap.

This is a small Layer 1 prerequisite for the finite-dimensional representation category of an
affine group scheme: later tensor products, duals, matrix coefficients, and Tannakian
reconstruction should be built on this full subcategory rather than on all comodules.

## Main definitions

* `TauCeti.ComoduleCat.isFG`: the finite-generation object property on `ComoduleCat`.
* `TauCeti.FGComoduleCat`: finitely generated right comodules as a full subcategory.
* `TauCeti.FGComoduleCat.incl`: the inclusion into all comodules.
* `forget₂ (FGComoduleCat R C) (ComoduleCat R C)`: the forgetful functor to all comodules.
* `forget₂ (FGComoduleCat R C) (SemimoduleCat R)`: the forgetful functor to semimodules.
* `TauCeti.FGComoduleCat.of`: build a finitely generated bundled comodule from unbundled data.
* `TauCeti.FGComoduleCat.ofHom`: lift an unbundled comodule morphism between finitely generated
  comodules.
* `TauCeti.FGComoduleCat.isoOfLinearEquiv`: build an isomorphism from a coaction-compatible
  linear equivalence.
* `TauCeti.FGComoduleCat.isZero_zero`: `FGComoduleCat.zero` is a zero object.
* `HasZeroObject (FGComoduleCat R C)`.

## References

This supplies the finite-dimensional-category part of
`ReductiveGroups/README.md` in TauCetiRoadmap, Layer 1 target "Comodules over a coalgebra/Hopf
algebra". The construction follows Mathlib's `FGModuleCat` pattern: finite objects are a full
subcategory defined by the object property `Module.Finite`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

universe u v w

section Semiring

variable (R : Type u) [CommSemiring R]
variable (C : Type v) [AddCommMonoid C] [Module R C] [Coalgebra R C]

namespace ComoduleCat

/-- Finite-generation as an object property on the category of right comodules. -/
def isFG : ObjectProperty (ComoduleCat.{u, v, w} R C) :=
  fun M => Module.Finite R M

/-- The finitely generated comodule property is exactly finite generation of the underlying
module. -/
theorem isFG_iff (M : ComoduleCat.{u, v, w} R C) :
    isFG (R := R) (C := C) M ↔ Module.Finite R M :=
  Iff.rfl

/-- The zero comodule is finitely generated. -/
theorem finite_zero : Module.Finite R (zero R C : ComoduleCat.{u, v, w} R C) := by
  rw [zero]
  infer_instance

/-- The finite-generation property contains the zero comodule. -/
instance isFG_containsZero : (isFG (R := R) (C := C)).ContainsZero where
  exists_zero := ⟨zero R C, isZero_zero R C, finite_zero R C⟩

end ComoduleCat

/-- The category of finitely generated right comodules over a fixed coalgebra.

For a field base, this is the category of finite-dimensional right comodules. -/
abbrev FGComoduleCat :=
  (ComoduleCat.isFG.{u, v, w} R C).FullSubcategory

namespace FGComoduleCat

variable {R C}

/-- The underlying type of a finitely generated comodule. -/
@[reducible]
def carrier (M : FGComoduleCat.{u, v, w} R C) : Type w :=
  M.obj

instance : CoeSort (FGComoduleCat.{u, v, w} R C) (Type w) :=
  ⟨carrier⟩

attribute [coe] carrier

instance (M : FGComoduleCat.{u, v, w} R C) : AddCommMonoid M :=
  inferInstanceAs (AddCommMonoid M.obj)

instance (M : FGComoduleCat.{u, v, w} R C) : Module R M :=
  inferInstanceAs (Module R M.obj)

instance (M : FGComoduleCat.{u, v, w} R C) : Comodule R C M :=
  inferInstanceAs (Comodule R C M.obj)

/-- The underlying module of a finitely generated comodule is finitely generated. -/
instance (M : FGComoduleCat.{u, v, w} R C) : Module.Finite R M :=
  M.property

/-- The inclusion from finitely generated comodules to all comodules. -/
abbrev incl : FGComoduleCat.{u, v, w} R C ⥤ ComoduleCat.{u, v, w} R C :=
  (ComoduleCat.isFG (R := R) (C := C)).ι

/-- Forget a finitely generated comodule to its underlying semimodule. -/
instance hasForgetToSemimoduleCat :
    HasForget₂ (FGComoduleCat.{u, v, w} R C) (SemimoduleCat.{w} R) :=
  HasForget₂.trans (FGComoduleCat.{u, v, w} R C) (ComoduleCat.{u, v, w} R C)
    (SemimoduleCat.{w} R)

/-- Forgetting a finitely generated comodule to semimodules agrees with forgetting its ambient
comodule. -/
@[simp]
theorem forget₂_semimoduleCat_obj (M : FGComoduleCat.{u, v, w} R C) :
    (forget₂ (FGComoduleCat.{u, v, w} R C) (SemimoduleCat.{w} R)).obj M =
      (forget₂ (ComoduleCat.{u, v, w} R C) (SemimoduleCat.{w} R)).obj M.obj :=
  rfl

/-- Forgetting a finitely generated comodule morphism to semimodules agrees with forgetting its
ambient comodule morphism. -/
@[simp]
theorem forget₂_semimoduleCat_map {M N : FGComoduleCat.{u, v, w} R C} (f : M ⟶ N) :
    (forget₂ (FGComoduleCat.{u, v, w} R C) (SemimoduleCat.{w} R)).map f =
      (forget₂ (ComoduleCat.{u, v, w} R C) (SemimoduleCat.{w} R)).map f.hom :=
  rfl

/-- Lift an unbundled finitely generated right comodule to `FGComoduleCat`. -/
abbrev of (M : Type w) [AddCommMonoid M] [Module R M] [Comodule R C M]
    [Module.Finite R M] : FGComoduleCat.{u, v, w} R C :=
  ⟨ComoduleCat.of R C M, inferInstanceAs (Module.Finite R M)⟩

/-- The object of `ComoduleCat` underlying `FGComoduleCat.of` is `ComoduleCat.of`. -/
@[simp]
theorem of_obj (M : Type w) [AddCommMonoid M] [Module R M] [Comodule R C M]
    [Module.Finite R M] :
    (of (R := R) (C := C) M).obj = ComoduleCat.of R C M :=
  rfl

/-- The coaction on `FGComoduleCat.of` is the original unbundled coaction. -/
@[simp]
theorem of_coact {M : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
    [Module.Finite R M] :
    Comodule.coact (R := R) (C := C) (M := of (R := R) (C := C) M) =
      Comodule.coact (R := R) (C := C) (M := M) :=
  rfl

/-- Typecheck an unbundled comodule morphism between finitely generated comodules as a
categorical morphism in `FGComoduleCat`. -/
abbrev ofHom {M N : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
    [Module.Finite R M] [AddCommMonoid N] [Module R N] [Comodule R C N]
    [Module.Finite R N] (f : Comodule.Hom R C M N) :
    of (R := R) (C := C) M ⟶ of (R := R) (C := C) N :=
  ObjectProperty.homMk (ComoduleCat.ofHom (R := R) (C := C) f)

/-- Turning an unbundled comodule morphism into an `FGComoduleCat` morphism and projecting to
the ambient comodule category recovers the original bundled morphism. -/
@[simp]
theorem ofHom_hom {M N : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
    [Module.Finite R M] [AddCommMonoid N] [Module R N] [Comodule R C N]
    [Module.Finite R N] (f : Comodule.Hom R C M N) :
    (ofHom (R := R) (C := C) f).hom = ComoduleCat.ofHom (R := R) (C := C) f :=
  rfl

/-- The categorical identity on a finitely generated bundled comodule is the bundled form of
the identity comodule morphism. -/
@[simp]
theorem ofHom_id {M : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
    [Module.Finite R M] :
    ofHom (R := R) (C := C) (Comodule.Hom.id R C M) = 𝟙 (of (R := R) (C := C) M) :=
  rfl

/-- Categorical composition of finitely generated bundled comodule morphisms is the bundled
form of composition of comodule morphisms. -/
@[simp]
theorem ofHom_comp {M N P : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
    [Module.Finite R M] [AddCommMonoid N] [Module R N] [Comodule R C N]
    [Module.Finite R N] [AddCommMonoid P] [Module R P] [Comodule R C P]
    [Module.Finite R P] (f : Comodule.Hom R C M N) (g : Comodule.Hom R C N P) :
    ofHom (R := R) (C := C) (Comodule.Hom.comp g f) =
      ofHom (R := R) (C := C) f ≫ ofHom (R := R) (C := C) g :=
  rfl

/-- The `FGComoduleCat` morphism induced by an unbundled morphism applies as that morphism. -/
@[simp]
theorem ofHom_apply {M N : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
    [Module.Finite R M] [AddCommMonoid N] [Module R N] [Comodule R C N]
    [Module.Finite R N] (f : Comodule.Hom R C M N) (m : M) :
    ofHom (R := R) (C := C) f m = f m :=
  rfl

/-- Build an isomorphism of finitely generated comodules from a linear equivalence of the
underlying modules whose *forward* map respects the coactions.

Compatibility of the inverse is automatic, and is supplied by
`TauCeti.ComoduleCat.isoOfLinearEquiv`; being a full subcategory, `FGComoduleCat` then inherits
the isomorphism from `ComoduleCat`. -/
def isoOfLinearEquiv {M N : FGComoduleCat.{u, v, w} R C} (e : M ≃ₗ[R] N)
    (h : TensorProduct.map e.toLinearMap LinearMap.id ∘ₗ
        Comodule.coact (R := R) (C := C) (M := M) =
      Comodule.coact (R := R) (C := C) (M := N) ∘ₗ e.toLinearMap) :
    M ≅ N :=
  (ComoduleCat.isFG (R := R) (C := C)).isoMk
    (ComoduleCat.isoOfLinearEquiv (R := R) (C := C) e h)

/-- The forward morphism of `FGComoduleCat.isoOfLinearEquiv` has the original linear equivalence
underneath. -/
@[simp]
theorem isoOfLinearEquiv_hom_toLinearMap {M N : FGComoduleCat.{u, v, w} R C} (e : M ≃ₗ[R] N)
    (h : TensorProduct.map e.toLinearMap LinearMap.id ∘ₗ
        Comodule.coact (R := R) (C := C) (M := M) =
      Comodule.coact (R := R) (C := C) (M := N) ∘ₗ e.toLinearMap) :
    (isoOfLinearEquiv e h).hom.hom.toLinearMap = e.toLinearMap :=
  rfl

/-- The inverse morphism of `FGComoduleCat.isoOfLinearEquiv` has the inverse linear equivalence
underneath. -/
@[simp]
theorem isoOfLinearEquiv_inv_toLinearMap {M N : FGComoduleCat.{u, v, w} R C} (e : M ≃ₗ[R] N)
    (h : TensorProduct.map e.toLinearMap LinearMap.id ∘ₗ
        Comodule.coact (R := R) (C := C) (M := M) =
      Comodule.coact (R := R) (C := C) (M := N) ∘ₗ e.toLinearMap) :
    (isoOfLinearEquiv e h).inv.hom.toLinearMap = e.symm.toLinearMap :=
  rfl

/-- The forward map of `FGComoduleCat.isoOfLinearEquiv` is the given linear equivalence. -/
@[simp]
theorem isoOfLinearEquiv_hom_apply {M N : FGComoduleCat.{u, v, w} R C} (e : M ≃ₗ[R] N)
    (h : TensorProduct.map e.toLinearMap LinearMap.id ∘ₗ
        Comodule.coact (R := R) (C := C) (M := M) =
      Comodule.coact (R := R) (C := C) (M := N) ∘ₗ e.toLinearMap) (m : M) :
    (isoOfLinearEquiv e h).hom m = e m :=
  rfl

/-- The inverse map of `FGComoduleCat.isoOfLinearEquiv` is the inverse linear equivalence. -/
@[simp]
theorem isoOfLinearEquiv_inv_apply {M N : FGComoduleCat.{u, v, w} R C} (e : M ≃ₗ[R] N)
    (h : TensorProduct.map e.toLinearMap LinearMap.id ∘ₗ
        Comodule.coact (R := R) (C := C) (M := M) =
      Comodule.coact (R := R) (C := C) (M := N) ∘ₗ e.toLinearMap) (n : N) :
    (isoOfLinearEquiv e h).inv n = e.symm n :=
  rfl

variable (R C)

/-- The bundled finitely generated zero right comodule. -/
def zero : FGComoduleCat.{u, v, w} R C :=
  ⟨ComoduleCat.zero R C, ComoduleCat.finite_zero R C⟩

/-- The ambient comodule underlying the finitely generated zero comodule is the zero comodule. -/
@[simp]
theorem zero_obj :
    (zero R C : FGComoduleCat.{u, v, w} R C).obj = ComoduleCat.zero R C :=
  rfl

/-- The named finitely generated zero comodule is a zero object. -/
theorem isZero_zero : IsZero (zero R C : FGComoduleCat.{u, v, w} R C) :=
  IsZero.of_full_of_faithful_of_isZero (ComoduleCat.isFG (R := R) (C := C)).ι (zero R C)
    (ComoduleCat.isZero_zero R C)

/-- Any morphism from the named finitely generated zero comodule is zero. -/
theorem zero_hom_eq_zero (M : FGComoduleCat.{u, v, w} R C) (f : zero R C ⟶ M) : f = 0 :=
  (isZero_zero (R := R) (C := C)).eq_of_src f 0

/-- Any morphism to the named finitely generated zero comodule is zero. -/
theorem hom_zero_eq_zero (M : FGComoduleCat.{u, v, w} R C) (f : M ⟶ zero R C) : f = 0 :=
  (isZero_zero (R := R) (C := C)).eq_of_tgt f 0

/-- The canonical morphism out of the named finitely generated zero comodule is the zero
morphism. -/
@[simp]
theorem isZero_zero_to (M : FGComoduleCat.{u, v, w} R C) :
    (isZero_zero (R := R) (C := C)).to_ M = 0 :=
  zero_hom_eq_zero (R := R) (C := C) M _

/-- The canonical morphism into the named finitely generated zero comodule is the zero morphism. -/
@[simp]
theorem isZero_zero_from (M : FGComoduleCat.{u, v, w} R C) :
    (isZero_zero (R := R) (C := C)).from_ M = 0 :=
  hom_zero_eq_zero (R := R) (C := C) M _

/-- Morphisms from the named finitely generated zero comodule are unique. -/
@[ext]
theorem zero_hom_ext {M : FGComoduleCat.{u, v, w} R C} (f g : zero R C ⟶ M) : f = g :=
  (isZero_zero (R := R) (C := C)).eq_of_src f g

/-- Morphisms to the named finitely generated zero comodule are unique. -/
@[ext]
theorem hom_zero_ext {M : FGComoduleCat.{u, v, w} R C} (f g : M ⟶ zero R C) : f = g :=
  (isZero_zero (R := R) (C := C)).eq_of_tgt f g

end FGComoduleCat

end Semiring

section Ring

variable (R : Type u) [CommRing R]
variable (C : Type v) [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {R C}

namespace FGComoduleCat

instance (M : FGComoduleCat.{u, v, w} R C) : AddCommGroup M :=
  Module.addCommMonoidToAddCommGroup R

end FGComoduleCat

end Ring

end TauCeti
