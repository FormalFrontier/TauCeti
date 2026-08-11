/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Comodules over a coalgebra

This file defines right comodules over an `R`-coalgebra `C` and their morphisms. A right
comodule is an `R`-module `M` equipped with a coaction `ρ : M →ₗ[R] M ⊗[R] C` satisfying
the usual coassociativity and counit identities.

This is a first Layer 1 prerequisite for the reductive-groups roadmap: representations of an
affine group scheme represented by a Hopf algebra are comodules over its coordinate Hopf
algebra, and the roadmap explicitly calls for comodules, comodule morphisms, tensor products,
duals, and the regular representation. The file starts with the core definition, the regular
right comodule of a coalgebra over itself, and the basic morphism API.

## Main definitions

* `TauCeti.Comodule`: a right comodule over a coalgebra.
* `TauCeti.Comodule.Hom`: morphisms of comodules.
* `TauCeti.Comodule.instSelf`: the regular right comodule of a coalgebra over itself.

## References

This follows the standard definition of a right comodule over a coalgebra; see for example
Sweedler, *Hopf Algebras*, Chapter 2. It is added for the "Comodules over a coalgebra/Hopf
algebra" target in Layer 1 of the Tau Ceti reductive-groups roadmap.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w x

/-- A right comodule over an `R`-coalgebra `C`.

The coaction is written as a linear map `coact : M →ₗ[R] M ⊗[R] C`. The coassociativity law
says that coacting twice on the `M` component agrees with coacting once and then
comultiplying the `C` component. The counit law says that applying the coalgebra counit to
the `C` component recovers the original vector, under the canonical `M ⊗ R` presentation. -/
class Comodule (R : Type u) (C : Type v) (M : Type w) [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C] [AddCommMonoid M] [Module R M] where
  /-- The coaction of a right comodule. -/
  coact : M →ₗ[R] M ⊗[R] C
  /-- Coassociativity of the right coaction. -/
  coassoc :
    TensorProduct.assoc R M C C ∘ₗ coact.rTensor C ∘ₗ coact =
      Coalgebra.comul.lTensor M ∘ₗ coact
  /-- The right counit law for the coaction. -/
  lTensor_counit_comp_coact :
    Coalgebra.counit.lTensor M ∘ₗ coact = (TensorProduct.mk R M R).flip 1

namespace Comodule

attribute [simp] Comodule.lTensor_counit_comp_coact

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M]

/-- Two right-comodule structures are equal when their coactions are equal. -/
@[ext]
theorem ext {rho sigma : Comodule R C M} (h : rho.coact = sigma.coact) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl

variable [Comodule R C M]
variable [AddCommMonoid N] [Module R N] [Comodule R C N]

/-- Coassociativity of the coaction, as an equality of linear maps. -/
@[simp]
theorem coact_coassoc :
    TensorProduct.assoc R M C C ∘ₗ (coact (R := R) (C := C) (M := M)).rTensor C ∘ₗ
        coact (R := R) (C := C) (M := M) =
      Coalgebra.comul.lTensor M ∘ₗ coact (R := R) (C := C) (M := M) :=
  Comodule.coassoc

/-- Coassociativity of the coaction, evaluated at a vector. -/
@[simp]
theorem coassoc_apply (m : M) :
    TensorProduct.assoc R M C C
        ((coact (R := R) (C := C) (M := M)).rTensor C (coact m)) =
      Coalgebra.comul.lTensor M (coact m) :=
  LinearMap.congr_fun (coact_coassoc (R := R) (C := C) (M := M)) m

/-- The counit law of the coaction, evaluated at a vector. -/
@[simp]
theorem lTensor_counit_coact (m : M) :
    Coalgebra.counit.lTensor M (coact (R := R) (C := C) (M := M) m) = m ⊗ₜ[R] 1 :=
  LinearMap.congr_fun (Comodule.lTensor_counit_comp_coact (R := R) (C := C) (M := M)) m

variable (R C) in
/-- The regular right comodule of a coalgebra over itself, with coaction given by the
coalgebra comultiplication. -/
instance instSelf : Comodule R C C where
  coact := Coalgebra.comul
  coassoc := Coalgebra.coassoc
  lTensor_counit_comp_coact := Coalgebra.lTensor_counit_comp_comul

/-- The coaction of the regular right comodule is the coalgebra comultiplication. -/
@[simp]
theorem instSelf_coact :
    coact (R := R) (C := C) (M := C) = Coalgebra.comul :=
  rfl

/-- A morphism of right comodules over a fixed coalgebra. -/
structure Hom (R : Type u) (C : Type v) (M : Type w) (N : Type x) [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C] [AddCommMonoid M] [Module R M]
    [Comodule R C M] [AddCommMonoid N] [Module R N] [Comodule R C N]
    extends M →ₗ[R] N where
  /-- A comodule morphism commutes with the two coactions. -/
  map_coact :
    TensorProduct.map toLinearMap LinearMap.id ∘ₗ coact (R := R) (C := C) (M := M) =
      coact (R := R) (C := C) (M := N) ∘ₗ toLinearMap

namespace Hom

variable {P Q : Type*}
variable [AddCommMonoid P] [Module R P] [Comodule R C P]
variable [AddCommMonoid Q] [Module R Q] [Comodule R C Q]

instance funLike : FunLike (Hom R C M N) M N where
  coe f := f.toLinearMap
  coe_injective f g h := by
    have hlin : f.toLinearMap = g.toLinearMap := LinearMap.ext fun m => congr_fun h m
    cases f
    cases g
    cases hlin
    rfl

/-- See Note [custom simps projection]. -/
def Simps.apply (f : Hom R C M N) : M → N :=
  f

initialize_simps_projections Hom (toFun → apply)

@[simp]
theorem coe_mk {f : M →ₗ[R] N} (h) : ((⟨f, h⟩ : Hom R C M N) : M → N) = f :=
  rfl

@[simp]
theorem coe_toLinearMap (f : Hom R C M N) : ⇑f.toLinearMap = f :=
  rfl

/-- Two comodule morphisms are equal when their underlying functions are equal. -/
@[ext]
theorem ext {f g : Hom R C M N} (h : ∀ m, f m = g m) : f = g := by
  have hlin : f.toLinearMap = g.toLinearMap := LinearMap.ext fun m => h m
  cases f
  cases g
  cases hlin
  rfl

/-- A comodule morphism commutes with coactions, as an equality of linear maps. -/
@[simp]
theorem map_coact_eq (f : Hom R C M N) :
    TensorProduct.map f.toLinearMap LinearMap.id ∘ₗ coact (R := R) (C := C) (M := M) =
      coact (R := R) (C := C) (M := N) ∘ₗ f.toLinearMap :=
  f.map_coact

/-- A comodule morphism commutes with coactions, evaluated at a vector. -/
@[simp]
theorem map_coact_apply (f : Hom R C M N) (m : M) :
    TensorProduct.map f.toLinearMap LinearMap.id (coact (R := R) (C := C) (M := M) m) =
      coact (R := R) (C := C) (M := N) (f m) :=
  LinearMap.congr_fun (map_coact_eq f) m

variable (R C M) in
/-- The identity morphism of a right comodule. -/
@[expose, simps!] def id : Hom R C M M where
  toLinearMap := LinearMap.id
  map_coact := by
    ext m
    simp

/-- Composition of right-comodule morphisms. -/
@[expose, simps!] def comp (g : Hom R C N P) (f : Hom R C M N) : Hom R C M P where
  toLinearMap := g.toLinearMap ∘ₗ f.toLinearMap
  map_coact := by
    ext m
    calc
      TensorProduct.map (g.toLinearMap ∘ₗ f.toLinearMap) LinearMap.id
          (coact (R := R) (C := C) (M := M) m)
        = TensorProduct.map g.toLinearMap LinearMap.id
            (TensorProduct.map f.toLinearMap LinearMap.id
              (coact (R := R) (C := C) (M := M) m)) := by
          simpa using (TensorProduct.map_map g.toLinearMap LinearMap.id f.toLinearMap
            LinearMap.id (coact (R := R) (C := C) (M := M) m)).symm
      _ = coact (R := R) (C := C) (M := P) (g (f m)) := by
          rw [map_coact_apply f, map_coact_apply g]

/-- The underlying linear map of the identity morphism is the identity linear map. -/
@[simp]
theorem id_toLinearMap : (id R C M).toLinearMap = LinearMap.id := rfl

/-- The underlying linear map of a composition is the composition of the underlying linear
maps. -/
@[simp]
theorem comp_toLinearMap (g : Hom R C N P) (f : Hom R C M N) :
    (g.comp f).toLinearMap = g.toLinearMap ∘ₗ f.toLinearMap := rfl

@[simp]
theorem id_comp (f : Hom R C M N) : comp (id R C N) f = f := by
  ext m
  simp

@[simp]
theorem comp_id (f : Hom R C M N) : comp f (id R C M) = f := by
  ext m
  simp

@[simp]
theorem comp_assoc (h : Hom R C P Q) (g : Hom R C N P) (f : Hom R C M N) :
    comp (comp h g) f = comp h (comp g f) := by
  ext m
  rfl

end Hom

end Comodule

end TauCeti
