/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Coalgebra.Hom
public import TauCeti.Algebra.Coalgebra.Comodule.Cat

/-!
# Corestriction of comodules along a coalgebra morphism

This file proves the basic functoriality of right comodules in the coalgebra. A coalgebra
morphism `f : C →ₗc[R] D` turns every right `C`-comodule into a right `D`-comodule by
postcomposing the coaction with `id ⊗ f`.

This is Layer 1 infrastructure for the reductive-groups roadmap target "Comodules over a
coalgebra/Hopf algebra": representations of affine group schemes are comodules over their
coordinate coalgebras, and changing the coordinate coalgebra along a morphism needs this
corestriction functor.

## Main definitions

* `TauCeti.Comodule.Corestrict`: the induced right `D`-comodule structure.
* `TauCeti.Comodule.corestrictHom`: a comodule morphism after corestricting both sides.
* `TauCeti.ComoduleCat.corestrict`: the corresponding functor between bundled comodule
  categories.

## References

This is the standard corestriction of comodules along a coalgebra morphism; see for example
Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v w x

namespace Comodule

variable {R : Type u} [CommSemiring R]
variable {C : Type v} {D : Type w}
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]
variable {M : Type x} [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- The coaction obtained from a right `C`-comodule by corestricting along a coalgebra
morphism `f : C →ₗc[R] D`. -/
@[expose] def corestrictCoact (f : C →ₗc[R] D) : M →ₗ[R] M ⊗[R] D :=
  TensorProduct.map LinearMap.id f.toLinearMap ∘ₗ coact (R := R) (C := C) (M := M)

private theorem assoc_rTensor_corestrictCoact (f : C →ₗc[R] D) (t : M ⊗[R] C) :
    TensorProduct.assoc R M D D
        ((corestrictCoact (R := R) (C := C) (D := D) (M := M) f).rTensor D
          (TensorProduct.map LinearMap.id f.toLinearMap t)) =
      TensorProduct.map LinearMap.id (TensorProduct.map f.toLinearMap f.toLinearMap)
        (TensorProduct.assoc R M C C
          ((coact (R := R) (C := C) (M := M)).rTensor C t)) := by
  calc
    TensorProduct.assoc R M D D
        ((corestrictCoact (R := R) (C := C) (D := D) (M := M) f).rTensor D
          (TensorProduct.map LinearMap.id f.toLinearMap t))
      =
        TensorProduct.assoc R M D D
          (TensorProduct.map (TensorProduct.map LinearMap.id f.toLinearMap) f.toLinearMap
            ((coact (R := R) (C := C) (M := M)).rTensor C t)) := by
          simp [corestrictCoact, LinearMap.rTensor, TensorProduct.map_map]
    _ =
        TensorProduct.map LinearMap.id (TensorProduct.map f.toLinearMap f.toLinearMap)
          (TensorProduct.assoc R M C C
            ((coact (R := R) (C := C) (M := M)).rTensor C t)) := by
          exact (TensorProduct.map_map_assoc LinearMap.id f.toLinearMap f.toLinearMap
            ((coact (R := R) (C := C) (M := M)).rTensor C t)).symm

omit [Comodule R C M] in
private theorem comul_lTensor_corestrict_map (f : C →ₗc[R] D) (t : M ⊗[R] C) :
    Coalgebra.comul.lTensor M (TensorProduct.map LinearMap.id f.toLinearMap t) =
      TensorProduct.map LinearMap.id (TensorProduct.map f.toLinearMap f.toLinearMap)
        (Coalgebra.comul.lTensor M t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul m c =>
      simp [CoalgHomClass.map_comp_comul_apply]
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy

omit [Comodule R C M] in
private theorem counit_lTensor_corestrict_map (f : C →ₗc[R] D) (t : M ⊗[R] C) :
    Coalgebra.counit.lTensor M (TensorProduct.map LinearMap.id f.toLinearMap t) =
      Coalgebra.counit.lTensor M t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul m c => simp
  | add x y hx hy =>
      simpa using congrArg₂ (· + ·) hx hy

/-- Corestrict a right comodule along a coalgebra morphism.

If `M` is a right `C`-comodule and `f : C →ₗc[R] D`, the new right `D`-coaction is
`(id ⊗ f) ∘ ρ`. -/
@[expose, implicit_reducible]
def Corestrict (f : C →ₗc[R] D) : Comodule R D M where
  coact := corestrictCoact (R := R) (C := C) (D := D) (M := M) f
  coassoc := by
    ext m
    calc
      TensorProduct.assoc R M D D
          (((corestrictCoact (R := R) (C := C) (D := D) (M := M) f).rTensor D)
            (corestrictCoact (R := R) (C := C) (D := D) (M := M) f m))
        =
          TensorProduct.map LinearMap.id (TensorProduct.map f.toLinearMap f.toLinearMap)
            (TensorProduct.assoc R M C C
              ((coact (R := R) (C := C) (M := M)).rTensor C
                (coact (R := R) (C := C) (M := M) m))) := by
          exact assoc_rTensor_corestrictCoact (R := R) (C := C) (D := D) (M := M) f
            (coact (R := R) (C := C) (M := M) m)
      _ =
          TensorProduct.map LinearMap.id (TensorProduct.map f.toLinearMap f.toLinearMap)
            (Coalgebra.comul.lTensor M (coact (R := R) (C := C) (M := M) m)) := by
          rw [coassoc_apply (R := R) (C := C) (M := M) m]
      _ =
          Coalgebra.comul.lTensor M
            (corestrictCoact (R := R) (C := C) (D := D) (M := M) f m) := by
          exact (comul_lTensor_corestrict_map (R := R) (C := C) (D := D) (M := M) f
            (coact (R := R) (C := C) (M := M) m)).symm
  lTensor_counit_comp_coact := by
    ext m
    calc
      Coalgebra.counit.lTensor M
          (corestrictCoact (R := R) (C := C) (D := D) (M := M) f m)
        = Coalgebra.counit.lTensor M (coact (R := R) (C := C) (M := M) m) := by
          exact counit_lTensor_corestrict_map (R := R) (C := C) (D := D) (M := M) f
            (coact (R := R) (C := C) (M := M) m)
      _ = m ⊗ₜ[R] 1 := by
          exact lTensor_counit_coact (R := R) (C := C) (M := M) m

/-- The corestricted coaction is `(id ⊗ f) ∘ ρ`. -/
@[simp]
theorem corestrict_coact (f : C →ₗc[R] D) :
    letI : Comodule R D M := Corestrict (R := R) (C := C) (D := D) (M := M) f
    coact (R := R) (C := D) (M := M) =
      corestrictCoact (R := R) (C := C) (D := D) (M := M) f :=
  rfl

/-- The corestricted coaction evaluates as `(id ⊗ f) (ρ m)`. -/
@[simp]
theorem corestrictCoact_apply (f : C →ₗc[R] D) (m : M) :
    corestrictCoact (R := R) (C := C) (D := D) (M := M) f m =
      TensorProduct.map LinearMap.id f.toLinearMap (coact (R := R) (C := C) (M := M) m) :=
  rfl

/-- The coaction of `Corestrict f` evaluates as `(id ⊗ f) (ρ m)`. -/
@[simp]
theorem corestrict_coact_apply (f : C →ₗc[R] D) (m : M) :
    letI : Comodule R D M := Corestrict (R := R) (C := C) (D := D) (M := M) f
    coact (R := R) (C := D) (M := M) m =
      TensorProduct.map LinearMap.id f.toLinearMap (coact (R := R) (C := C) (M := M) m) :=
  rfl

/-- Corestricting along the identity coalgebra morphism leaves the coaction unchanged. -/
@[simp]
theorem corestrictCoact_id :
    corestrictCoact (R := R) (C := C) (D := C) (M := M) (CoalgHom.id R C) =
      coact (R := R) (C := C) (M := M) := by
  ext m
  simp [corestrictCoact]

variable {E : Type*} [AddCommMonoid E] [Module R E] [Coalgebra R E]

/-- Corestricted coactions compose in the coalgebra morphism. -/
@[simp]
theorem corestrictCoact_comp (f : C →ₗc[R] D) (g : D →ₗc[R] E) :
    corestrictCoact (R := R) (C := C) (D := E) (M := M) (g.comp f) =
      letI : Comodule R D M := Corestrict (R := R) (C := C) (D := D) (M := M) f
      corestrictCoact (R := R) (C := D) (D := E) (M := M) g :=
  by
    ext m
    simp [corestrictCoact, TensorProduct.map_map]

variable {N : Type*} [AddCommMonoid N] [Module R N] [Comodule R C N]

/-- A morphism of `C`-comodules is also a morphism after corestricting both comodules along
the same coalgebra morphism. -/
@[expose] def corestrictHom (f : C →ₗc[R] D) (g : Hom R C M N) :
    letI : Comodule R D M := Corestrict (R := R) (C := C) (D := D) (M := M) f
    letI : Comodule R D N := Corestrict (R := R) (C := C) (D := D) (M := N) f
    Hom R D M N :=
  letI : Comodule R D M := Corestrict (R := R) (C := C) (D := D) (M := M) f
  letI : Comodule R D N := Corestrict (R := R) (C := C) (D := D) (M := N) f
  { toLinearMap := g.toLinearMap
    map_coact := by
      ext m
      dsimp [Corestrict, corestrictCoact]
      rw [← Hom.map_coact_apply (R := R) (C := C) (M := M) (N := N) g m]
      calc
        TensorProduct.map g.toLinearMap LinearMap.id
            (TensorProduct.map LinearMap.id f.toLinearMap
              (coact (R := R) (C := C) (M := M) m))
          =
            TensorProduct.map (g.toLinearMap.comp LinearMap.id)
              (LinearMap.id.comp f.toLinearMap) (coact (R := R) (C := C) (M := M) m) := by
            exact TensorProduct.map_map g.toLinearMap LinearMap.id LinearMap.id f.toLinearMap
              (coact (R := R) (C := C) (M := M) m)
        _ =
            TensorProduct.map LinearMap.id f.toLinearMap
              (TensorProduct.map g.toLinearMap LinearMap.id
                (coact (R := R) (C := C) (M := M) m)) := by
            exact (TensorProduct.map_map LinearMap.id f.toLinearMap g.toLinearMap LinearMap.id
              (coact (R := R) (C := C) (M := M) m)).symm }

/-- Corestricting a comodule morphism does not change its underlying linear map. -/
@[simp]
theorem corestrictHom_toLinearMap (f : C →ₗc[R] D) (g : Hom R C M N) :
    letI : Comodule R D M := Corestrict (R := R) (C := C) (D := D) (M := M) f
    letI : Comodule R D N := Corestrict (R := R) (C := C) (D := D) (M := N) f
    (corestrictHom (R := R) (C := C) (D := D) (M := M) (N := N) f g).toLinearMap =
      g.toLinearMap :=
  rfl

/-- Corestricting a comodule morphism does not change its underlying function. -/
@[simp]
theorem corestrictHom_apply (f : C →ₗc[R] D) (g : Hom R C M N) (m : M) :
    letI : Comodule R D M := Corestrict (R := R) (C := C) (D := D) (M := M) f
    letI : Comodule R D N := Corestrict (R := R) (C := C) (D := D) (M := N) f
    corestrictHom (R := R) (C := C) (D := D) (M := M) (N := N) f g m = g m :=
  rfl

/-- Corestriction of morphisms is unchanged on underlying linear maps under composition of
coalgebra morphisms. -/
@[simp]
theorem corestrictHom_comp_coalg_toLinearMap (f : C →ₗc[R] D) (g : D →ₗc[R] E)
    (h : Hom R C M N) :
    (letI : Comodule R E M := Corestrict (R := R) (C := C) (D := E) (M := M) (g.comp f)
     letI : Comodule R E N := Corestrict (R := R) (C := C) (D := E) (M := N) (g.comp f)
     (corestrictHom (R := R) (C := C) (D := E) (M := M) (N := N) (g.comp f) h).toLinearMap) =
      (letI : Comodule R D M := Corestrict (R := R) (C := C) (D := D) (M := M) f
       letI : Comodule R D N := Corestrict (R := R) (C := C) (D := D) (M := N) f
       letI : Comodule R E M := Corestrict (R := R) (C := D) (D := E) (M := M) g
       letI : Comodule R E N := Corestrict (R := R) (C := D) (D := E) (M := N) g
       (corestrictHom (R := R) (C := D) (D := E) (M := M) (N := N) g
          (corestrictHom (R := R) (C := C) (D := D) (M := M) (N := N) f h)).toLinearMap) :=
  rfl

/-- Corestriction of morphisms is unchanged on elements under composition of coalgebra
morphisms. -/
@[simp]
theorem corestrictHom_comp_coalg_apply (f : C →ₗc[R] D) (g : D →ₗc[R] E) (h : Hom R C M N)
    (m : M) :
    (letI : Comodule R E M := Corestrict (R := R) (C := C) (D := E) (M := M) (g.comp f)
     letI : Comodule R E N := Corestrict (R := R) (C := C) (D := E) (M := N) (g.comp f)
     corestrictHom (R := R) (C := C) (D := E) (M := M) (N := N) (g.comp f) h m) =
      (letI : Comodule R D M := Corestrict (R := R) (C := C) (D := D) (M := M) f
       letI : Comodule R D N := Corestrict (R := R) (C := C) (D := D) (M := N) f
       letI : Comodule R E M := Corestrict (R := R) (C := D) (D := E) (M := M) g
       letI : Comodule R E N := Corestrict (R := R) (C := D) (D := E) (M := N) g
       corestrictHom (R := R) (C := D) (D := E) (M := M) (N := N) g
          (corestrictHom (R := R) (C := C) (D := D) (M := M) (N := N) f h) m) :=
  rfl

/-- Corestriction sends identity morphisms to identity morphisms. -/
@[simp]
theorem corestrictHom_id (f : C →ₗc[R] D) :
    letI : Comodule R D M := Corestrict (R := R) (C := C) (D := D) (M := M) f
    corestrictHom (R := R) (C := C) (D := D) (M := M) (N := M) f (Hom.id R C M) =
      Hom.id R D M :=
  by
    letI : Comodule R D M := Corestrict (R := R) (C := C) (D := D) (M := M) f
    exact Hom.ext fun _ => rfl

/-- Corestriction preserves composition of comodule morphisms. -/
@[simp]
theorem corestrictHom_comp {P : Type*} [AddCommMonoid P] [Module R P] [Comodule R C P]
    (f : C →ₗc[R] D) (g : Hom R C M N) (h : Hom R C N P) :
    letI : Comodule R D M := Corestrict (R := R) (C := C) (D := D) (M := M) f
    letI : Comodule R D N := Corestrict (R := R) (C := C) (D := D) (M := N) f
    letI : Comodule R D P := Corestrict (R := R) (C := C) (D := D) (M := P) f
    corestrictHom (R := R) (C := C) (D := D) (M := M) (N := P) f (Hom.comp h g) =
      Hom.comp
        (corestrictHom (R := R) (C := C) (D := D) (M := N) (N := P) f h)
        (corestrictHom (R := R) (C := C) (D := D) (M := M) (N := N) f g) :=
  by
    letI : Comodule R D M := Corestrict (R := R) (C := C) (D := D) (M := M) f
    letI : Comodule R D N := Corestrict (R := R) (C := C) (D := D) (M := N) f
    letI : Comodule R D P := Corestrict (R := R) (C := C) (D := D) (M := P) f
    exact Hom.ext fun _ => rfl

end Comodule

namespace ComoduleCat

variable {R : Type u} [CommSemiring R]
variable {C : Type v} {D : Type w}
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]

/-- Corestriction of bundled right comodules along a coalgebra morphism. -/
@[expose]
def corestrict (f : C →ₗc[R] D) : ComoduleCat.{u, v, x} R C ⥤ ComoduleCat.{u, w, x} R D where
  obj M :=
    letI : Comodule R D M := Comodule.Corestrict (R := R) (C := C) (D := D) (M := M) f
    of R D M
  map {M N} g :=
    Comodule.corestrictHom (R := R) (C := C) (D := D) (M := M) (N := N) f g
  map_id M := by
    exact Comodule.corestrictHom_id (R := R) (C := C) (D := D) (M := M) f
  map_comp g h := by
    exact Comodule.corestrictHom_comp (R := R) (C := C) (D := D) (M := _) (N := _) f g h

/-- The corestriction functor leaves the underlying type of an object unchanged. -/
@[simp]
theorem corestrict_obj (f : C →ₗc[R] D) (M : ComoduleCat.{u, v, x} R C) :
    (corestrict (R := R) (C := C) (D := D) f).obj M =
      (letI : Comodule R D M :=
        Comodule.Corestrict (R := R) (C := C) (D := D) (M := M) f
       of R D M) :=
  rfl

/-- The corestriction functor leaves the underlying linear map of a morphism unchanged. -/
@[simp]
theorem corestrict_map_toLinearMap (f : C →ₗc[R] D) {M N : ComoduleCat.{u, v, x} R C}
    (g : M ⟶ N) :
    ((corestrict (R := R) (C := C) (D := D) f).map g).toLinearMap = g.toLinearMap :=
  rfl

/-- The corestriction functor leaves the underlying function of a morphism unchanged. -/
@[simp]
theorem corestrict_map_apply (f : C →ₗc[R] D) {M N : ComoduleCat.{u, v, x} R C}
    (g : M ⟶ N) (m : M) :
    (corestrict (R := R) (C := C) (D := D) f).map g m = g m :=
  rfl

variable {E : Type*} [AddCommMonoid E] [Module R E] [Coalgebra R E]

/-- Corestriction functors compose in the coalgebra morphism on underlying linear maps. -/
theorem corestrict_map_comp_coalg_toLinearMap (f : C →ₗc[R] D) (g : D →ₗc[R] E)
    {M N : ComoduleCat.{u, v, x} R C} (h : M ⟶ N) :
    ((corestrict (R := R) (C := C) (D := E) (g.comp f)).map h).toLinearMap =
      ((corestrict (R := R) (C := D) (D := E) g).map
        ((corestrict (R := R) (C := C) (D := D) f).map h)).toLinearMap :=
  rfl

/-- Corestriction functors compose in the coalgebra morphism on elements. -/
@[simp]
theorem corestrict_map_comp_coalg_apply (f : C →ₗc[R] D) (g : D →ₗc[R] E)
    {M N : ComoduleCat.{u, v, x} R C} (h : M ⟶ N) (m : M) :
    (corestrict (R := R) (C := C) (D := E) (g.comp f)).map h m =
      (corestrict (R := R) (C := D) (D := E) g).map
        ((corestrict (R := R) (C := C) (D := D) f).map h) m :=
  rfl

end ComoduleCat

end TauCeti
