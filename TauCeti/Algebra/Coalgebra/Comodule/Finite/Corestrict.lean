/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Corestrict
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Basic

/-!
# Corestriction of finitely generated comodules

This file lifts corestriction along a coalgebra morphism from all right comodules to the full
subcategory of finitely generated right comodules. Since corestriction changes only the target
coalgebra of the coaction and leaves the underlying module unchanged, finite generation is
preserved automatically.

This is Layer 1 infrastructure for the reductive-groups roadmap target "Comodules over a
coalgebra/Hopf algebra": the finitely generated comodule category must remain available when
the coordinate coalgebra is changed along a coalgebra morphism.

## Main definitions

* `TauCeti.FGComoduleCat.corestrict`: corestriction as a functor on finitely generated
  comodules.
* Compatibility lemmas with `ComoduleCat.corestrict`, the inclusion into all comodules, and
  the forgetful functor to semimodules.

## References

This is the standard corestriction of comodules along a coalgebra morphism; see Sweedler,
*Hopf Algebras*, Chapter 2. The categorical lift reuses Mathlib's
`ObjectProperty.FullSubcategory` API.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v w x y

namespace FGComoduleCat

variable {R : Type u} [CommSemiring R]
variable {C : Type v} {D : Type w}
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]

/-- Corestriction of finitely generated right comodules along a coalgebra morphism.

The underlying module is unchanged, so the finite-generation proof is inherited from the
source object. -/
@[expose]
def corestrict (f : C →ₗc[R] D) : FGComoduleCat.{u, v, x} R C ⥤ FGComoduleCat.{u, w, x} R D where
  __ := (ComoduleCat.isFG (R := R) (C := D)).lift
    ((incl (R := R) (C := C)) ⋙ ComoduleCat.corestrict (R := R) (C := C) (D := D) f)
    (fun M => M.property)

/-- Corestriction on finitely generated comodules is corestriction on the ambient comodule. -/
@[simp]
theorem corestrict_obj_obj (f : C →ₗc[R] D) (M : FGComoduleCat.{u, v, x} R C) :
    ((corestrict (R := R) (C := C) (D := D) f).obj M).obj =
      (ComoduleCat.corestrict (R := R) (C := C) (D := D) f).obj M.obj :=
  rfl

/-- Corestriction leaves the underlying type of a finitely generated comodule unchanged. -/
@[simp]
theorem corestrict_obj_coe (f : C →ₗc[R] D) (M : FGComoduleCat.{u, v, x} R C) :
    ((corestrict (R := R) (C := C) (D := D) f).obj M : Type x) = M :=
  rfl

/-- The coaction after corestricting a finitely generated comodule is `(id ⊗ f) ∘ ρ`. -/
@[simp]
theorem corestrict_obj_coact (f : C →ₗc[R] D) (M : FGComoduleCat.{u, v, x} R C) :
    Comodule.coact (R := R) (C := D)
        (M := (corestrict (R := R) (C := C) (D := D) f).obj M) =
      Comodule.corestrictCoact (R := R) (C := C) (D := D) (M := M) f :=
  rfl

/-- The coaction after corestricting a finitely generated comodule evaluates as
`(id ⊗ f) (ρ m)`. -/
@[simp]
theorem corestrict_obj_coact_apply (f : C →ₗc[R] D) (M : FGComoduleCat.{u, v, x} R C) (m : M) :
    Comodule.coact (R := R) (C := D)
        (M := (corestrict (R := R) (C := C) (D := D) f).obj M) m =
      TensorProduct.map LinearMap.id f.toLinearMap
        (Comodule.coact (R := R) (C := C) (M := M) m) :=
  rfl

/-- Corestriction on finitely generated morphisms is corestriction on ambient comodule
morphisms. -/
@[simp]
theorem corestrict_map_hom (f : C →ₗc[R] D) {M N : FGComoduleCat.{u, v, x} R C} (g : M ⟶ N) :
    ((corestrict (R := R) (C := C) (D := D) f).map g).hom =
      (ComoduleCat.corestrict (R := R) (C := C) (D := D) f).map g.hom :=
  rfl

/-- Corestriction leaves the underlying linear map of a finitely generated comodule morphism
unchanged. -/
@[simp]
theorem corestrict_map_toLinearMap (f : C →ₗc[R] D) {M N : FGComoduleCat.{u, v, x} R C}
    (g : M ⟶ N) : (((corestrict (R := R) (C := C) (D := D) f).map g).hom).toLinearMap =
      g.hom.toLinearMap :=
  rfl

/-- Corestriction leaves the underlying function of a finitely generated comodule morphism
unchanged. -/
@[simp]
theorem corestrict_map_apply (f : C →ₗc[R] D) {M N : FGComoduleCat.{u, v, x} R C}
    (g : M ⟶ N) (m : M) : (corestrict (R := R) (C := C) (D := D) f).map g m = g m :=
  rfl

/-- Corestriction of finitely generated comodules commutes with the inclusion into all
comodules on objects. -/
@[simp]
theorem incl_corestrict_obj (f : C →ₗc[R] D) (M : FGComoduleCat.{u, v, x} R C) :
    (incl (R := R) (C := D)).obj
        ((corestrict (R := R) (C := C) (D := D) f).obj M) =
      (ComoduleCat.corestrict (R := R) (C := C) (D := D) f).obj
        ((incl (R := R) (C := C)).obj M) :=
  rfl

/-- Corestriction of finitely generated comodules commutes with the inclusion into all
comodules on morphisms. -/
@[simp]
theorem incl_corestrict_map (f : C →ₗc[R] D) {M N : FGComoduleCat.{u, v, x} R C} (g : M ⟶ N) :
    (incl (R := R) (C := D)).map
        ((corestrict (R := R) (C := C) (D := D) f).map g) =
      (ComoduleCat.corestrict (R := R) (C := C) (D := D) f).map
        ((incl (R := R) (C := C)).map g) :=
  rfl

/-- Corestriction leaves the underlying semimodule object unchanged. -/
@[simp]
theorem forget₂_semimoduleCat_corestrict_obj (f : C →ₗc[R] D) (M : FGComoduleCat.{u, v, x} R C) :
    (forget₂ (FGComoduleCat.{u, w, x} R D) (SemimoduleCat.{x} R)).obj
        ((corestrict (R := R) (C := C) (D := D) f).obj M) =
      (forget₂ (FGComoduleCat.{u, v, x} R C) (SemimoduleCat.{x} R)).obj M :=
  rfl

/-- Corestriction leaves the underlying semimodule morphism unchanged. -/
theorem forget₂_semimoduleCat_corestrict_map (f : C →ₗc[R] D)
    {M N : FGComoduleCat.{u, v, x} R C} (g : M ⟶ N) :
    (forget₂ (FGComoduleCat.{u, w, x} R D) (SemimoduleCat.{x} R)).map
        ((corestrict (R := R) (C := C) (D := D) f).map g) =
      (forget₂ (FGComoduleCat.{u, v, x} R C) (SemimoduleCat.{x} R)).map g :=
  rfl

variable {E : Type y} [AddCommMonoid E] [Module R E] [Coalgebra R E]

/-- Corestricting finitely generated comodules along the identity coalgebra morphism leaves the
coaction unchanged. -/
theorem corestrict_obj_coact_id (M : FGComoduleCat.{u, v, x} R C) :
    Comodule.coact (R := R) (C := C)
        (M := (corestrict (R := R) (C := C) (D := C) (CoalgHom.id R C)).obj M) =
      Comodule.coact (R := R) (C := C) (M := M) :=
  Comodule.corestrictCoact_id (R := R) (C := C) (M := M)

/-- Corestriction functors compose in the coalgebra morphism on underlying linear maps. -/
theorem corestrict_map_comp_coalg_toLinearMap (f : C →ₗc[R] D) (g : D →ₗc[R] E)
    {M N : FGComoduleCat.{u, v, x} R C} (h : M ⟶ N) :
    (((corestrict (R := R) (C := C) (D := E) (g.comp f)).map h).hom).toLinearMap =
      (((corestrict (R := R) (C := D) (D := E) g).map
        ((corestrict (R := R) (C := C) (D := D) f).map h)).hom).toLinearMap :=
  rfl

/-- Corestriction functors compose in the coalgebra morphism on elements. -/
@[simp]
theorem corestrict_map_comp_coalg_apply (f : C →ₗc[R] D) (g : D →ₗc[R] E)
    {M N : FGComoduleCat.{u, v, x} R C} (h : M ⟶ N) (m : M) :
    (corestrict (R := R) (C := C) (D := E) (g.comp f)).map h m =
      (corestrict (R := R) (C := D) (D := E) g).map
        ((corestrict (R := R) (C := C) (D := D) f).map h) m :=
  rfl

end FGComoduleCat

end TauCeti
