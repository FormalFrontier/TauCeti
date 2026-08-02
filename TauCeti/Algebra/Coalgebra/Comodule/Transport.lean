/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Cat

/-!
# Transporting comodules across linear equivalences

This file records that a right comodule structure can be transported along an `R`-linear
equivalence. This is a small but useful structural prerequisite for the reductive-groups
roadmap's Layer 1 representation-category work: tensor products, unitors, associators, and
duals of comodules all require moving coactions across canonical linear equivalences without
unfolding the definition of a comodule.

## Main declarations

* `TauCeti.Comodule.Transport`: the transported right-comodule structure on the target of a
  linear equivalence.
* `TauCeti.Comodule.transportHom`: transport a comodule morphism across linear equivalences on
  source and target.
* `TauCeti.ComoduleCat.transport`: the bundled comodule obtained by transport.
* `TauCeti.ComoduleCat.transportIso`: the bundled isomorphism from the original comodule to
  its transport.

## References

This supplies infrastructure for `ReductiveGroups/README.md` in TauCetiRoadmap, Layer 1 target
"Comodules over a coalgebra/Hopf algebra", specifically the categorical API needed before
tensor products and duals of comodules.
-/

@[expose] public section

open scoped TensorProduct

namespace TauCeti

universe u v w x y z

namespace Comodule

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [AddCommMonoid N] [Module R N]

/-- The coaction obtained by transporting a right-comodule structure across a linear
equivalence `e : M ≃ₗ[R] N`.

It sends `n` to `(e ⊗ id) (ρ (e.symm n))`. -/
def transportCoact (e : M ≃ₗ[R] N) : N →ₗ[R] N ⊗[R] C :=
  TensorProduct.map e.toLinearMap LinearMap.id ∘ₗ coact (R := R) (C := C) (M := M) ∘ₗ
    e.symm.toLinearMap

/-- The transported coaction evaluates as `(e ⊗ id) (ρ (e.symm n))`. -/
@[simp]
theorem transportCoact_apply (e : M ≃ₗ[R] N) (n : N) :
    transportCoact (R := R) (C := C) (M := M) (N := N) e n =
      TensorProduct.map e.toLinearMap LinearMap.id
        (coact (R := R) (C := C) (M := M) (e.symm n)) :=
  rfl

/-- Transporting along the identity linear equivalence leaves the coaction unchanged. -/
@[simp]
theorem transportCoact_refl :
    transportCoact (R := R) (C := C) (M := M) (N := M) (LinearEquiv.refl R M) =
      coact (R := R) (C := C) (M := M) := by
  ext m
  simp [transportCoact]

private theorem assoc_rTensor_transportCoact (e : M ≃ₗ[R] N) (t : M ⊗[R] C) :
    TensorProduct.assoc R N C C
        ((transportCoact (R := R) (C := C) (M := M) (N := N) e).rTensor C
          (TensorProduct.map e.toLinearMap LinearMap.id t)) =
      TensorProduct.map e.toLinearMap (TensorProduct.map LinearMap.id LinearMap.id)
        (TensorProduct.assoc R M C C
          ((coact (R := R) (C := C) (M := M)).rTensor C t)) := by
  calc
    TensorProduct.assoc R N C C
        ((transportCoact (R := R) (C := C) (M := M) (N := N) e).rTensor C
          (TensorProduct.map e.toLinearMap LinearMap.id t))
      = TensorProduct.assoc R N C C
          (TensorProduct.map (TensorProduct.map e.toLinearMap LinearMap.id) LinearMap.id
            ((coact (R := R) (C := C) (M := M)).rTensor C t)) := by
          induction t using TensorProduct.induction_on with
          | zero => simp [transportCoact, LinearMap.rTensor]
          | tmul m c => simp [transportCoact, LinearMap.rTensor]
          | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
    _ = TensorProduct.map e.toLinearMap (TensorProduct.map LinearMap.id LinearMap.id)
          (TensorProduct.assoc R M C C
            ((coact (R := R) (C := C) (M := M)).rTensor C t)) := by
          exact (TensorProduct.map_map_assoc e.toLinearMap LinearMap.id LinearMap.id
            ((coact (R := R) (C := C) (M := M)).rTensor C t)).symm

omit [Comodule R C M] in
private theorem comul_lTensor_transport_map (e : M ≃ₗ[R] N) (t : M ⊗[R] C) :
    Coalgebra.comul.lTensor N (TensorProduct.map e.toLinearMap LinearMap.id t) =
      TensorProduct.map e.toLinearMap (TensorProduct.map LinearMap.id LinearMap.id)
        (Coalgebra.comul.lTensor M t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul m c => simp
  | add x y hx hy => simp [hx, hy]

omit [Comodule R C M] in
private theorem counit_lTensor_transport_map (e : M ≃ₗ[R] N) (t : M ⊗[R] C) :
    Coalgebra.counit.lTensor N (TensorProduct.map e.toLinearMap LinearMap.id t) =
      TensorProduct.map e.toLinearMap LinearMap.id (Coalgebra.counit.lTensor M t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul m c => simp
  | add x y hx hy => simp [hx, hy]

/-- Transport a right-comodule structure across a linear equivalence.

If `M` is a right `C`-comodule and `e : M ≃ₗ[R] N`, then `N` becomes a right `C`-comodule by
the coaction `(e ⊗ id) ∘ ρ ∘ e.symm`. This definition is intentionally not a global
instance: the target module may carry several different coactions. -/
@[implicit_reducible]
def Transport (e : M ≃ₗ[R] N) : Comodule R C N where
  coact := transportCoact (R := R) (C := C) (M := M) (N := N) e
  coassoc := by
    ext n
    calc
      TensorProduct.assoc R N C C
          (((transportCoact (R := R) (C := C) (M := M) (N := N) e).rTensor C)
            (transportCoact (R := R) (C := C) (M := M) (N := N) e n))
        = TensorProduct.map e.toLinearMap (TensorProduct.map LinearMap.id LinearMap.id)
            (TensorProduct.assoc R M C C
              ((coact (R := R) (C := C) (M := M)).rTensor C
                (coact (R := R) (C := C) (M := M) (e.symm n)))) := by
          exact assoc_rTensor_transportCoact (R := R) (C := C) (M := M) (N := N) e
            (coact (R := R) (C := C) (M := M) (e.symm n))
      _ = TensorProduct.map e.toLinearMap (TensorProduct.map LinearMap.id LinearMap.id)
            (Coalgebra.comul.lTensor M
              (coact (R := R) (C := C) (M := M) (e.symm n))) := by
          rw [coassoc_apply (R := R) (C := C) (M := M)]
      _ = Coalgebra.comul.lTensor N
            (transportCoact (R := R) (C := C) (M := M) (N := N) e n) := by
          exact (comul_lTensor_transport_map (R := R) (C := C) (M := M) (N := N) e
            (coact (R := R) (C := C) (M := M) (e.symm n))).symm
  lTensor_counit_comp_coact := by
    ext n
    calc
      Coalgebra.counit.lTensor N
          (transportCoact (R := R) (C := C) (M := M) (N := N) e n)
        = TensorProduct.map e.toLinearMap LinearMap.id
            (Coalgebra.counit.lTensor M
              (coact (R := R) (C := C) (M := M) (e.symm n))) := by
          exact counit_lTensor_transport_map (R := R) (C := C) (M := M) (N := N) e
            (coact (R := R) (C := C) (M := M) (e.symm n))
      _ = n ⊗ₜ[R] 1 := by simp

/-- The transported coaction is `(e ⊗ id) ∘ ρ ∘ e.symm`. -/
@[simp]
theorem transport_coact (e : M ≃ₗ[R] N) :
    letI : Comodule R C N := Transport (R := R) (C := C) (M := M) (N := N) e
    coact (R := R) (C := C) (M := N) =
      transportCoact (R := R) (C := C) (M := M) (N := N) e :=
  rfl

/-- Pointwise form of `transport_coact`. -/
@[simp]
theorem transport_coact_apply (e : M ≃ₗ[R] N) (n : N) :
    letI : Comodule R C N := Transport (R := R) (C := C) (M := M) (N := N) e
    coact (R := R) (C := C) (M := N) n =
      TensorProduct.map e.toLinearMap LinearMap.id
        (coact (R := R) (C := C) (M := M) (e.symm n)) :=
  rfl

variable {P : Type y} [AddCommMonoid P] [Module R P]

/-- Transported coactions compose in the linear equivalence. -/
@[simp]
theorem transportCoact_trans (e : M ≃ₗ[R] N) (f : N ≃ₗ[R] P) :
    transportCoact (R := R) (C := C) (M := M) (N := P) (e.trans f) =
      letI : Comodule R C N := Transport (R := R) (C := C) (M := M) (N := N) e
      transportCoact (R := R) (C := C) (M := N) (N := P) f :=
  by
    ext p
    dsimp [transportCoact]
    rw [TensorProduct.map_map]
    congr

variable {M' : Type y} {N' : Type z}
variable [AddCommMonoid M'] [Module R M'] [Comodule R C M']
variable [AddCommMonoid N'] [Module R N']

omit [Coalgebra R C] [Comodule R C M] [Comodule R C M'] in
private theorem tensor_map_transport_conj (eM : M ≃ₗ[R] N) (eN : M' ≃ₗ[R] N')
    (f : M →ₗ[R] M') (t : M ⊗[R] C) :
    TensorProduct.map (eN.toLinearMap.comp (f.comp eM.symm.toLinearMap)) LinearMap.id
        (TensorProduct.map eM.toLinearMap LinearMap.id t) =
      TensorProduct.map eN.toLinearMap LinearMap.id (TensorProduct.map f LinearMap.id t) := by
  rw [TensorProduct.map_map, TensorProduct.map_map]
  congr
  ext m
  simp

/-- Transport a comodule morphism across linear equivalences on source and target. -/
def transportHom (eM : M ≃ₗ[R] N) (eN : M' ≃ₗ[R] N') (f : Hom R C M M') :
    letI : Comodule R C N := Transport (R := R) (C := C) (M := M) (N := N) eM
    letI : Comodule R C N' := Transport (R := R) (C := C) (M := M') (N := N') eN
    Hom R C N N' := by
  letI : Comodule R C N := Transport (R := R) (C := C) (M := M) (N := N) eM
  letI : Comodule R C N' := Transport (R := R) (C := C) (M := M') (N := N') eN
  exact
    { toLinearMap := eN.toLinearMap ∘ₗ f.toLinearMap ∘ₗ eM.symm.toLinearMap
      map_coact := by
        ext n
        dsimp [Transport, transportCoact]
        simp only [LinearEquiv.symm_apply_apply]
        rw [← Hom.map_coact_apply f (eM.symm n)]
        exact tensor_map_transport_conj (R := R) (C := C) (M := M) (N := N) (M' := M')
          (N' := N') eM eN f.toLinearMap (coact (R := R) (C := C) (M := M) (eM.symm n)) }

/-- Transporting a morphism has the conjugated underlying linear map. -/
@[simp]
theorem transportHom_toLinearMap (eM : M ≃ₗ[R] N) (eN : M' ≃ₗ[R] N') (f : Hom R C M M') :
    letI : Comodule R C N := Transport (R := R) (C := C) (M := M) (N := N) eM
    letI : Comodule R C N' := Transport (R := R) (C := C) (M := M') (N := N') eN
    (transportHom (R := R) (C := C) (M := M) (M' := M') (N := N) (N' := N') eM eN f).toLinearMap =
      eN.toLinearMap ∘ₗ f.toLinearMap ∘ₗ eM.symm.toLinearMap :=
  rfl

/-- Pointwise form of `transportHom_toLinearMap`. -/
@[simp]
theorem transportHom_apply (eM : M ≃ₗ[R] N) (eN : M' ≃ₗ[R] N') (f : Hom R C M M') (n : N) :
    letI : Comodule R C N := Transport (R := R) (C := C) (M := M) (N := N) eM
    letI : Comodule R C N' := Transport (R := R) (C := C) (M := M') (N := N') eN
    transportHom (R := R) (C := C) (M := M) (M' := M') (N := N) (N' := N') eM eN f n =
      eN (f (eM.symm n)) :=
  rfl

/-- Transporting the identity morphism gives the identity morphism. -/
@[simp]
theorem transportHom_id (e : M ≃ₗ[R] N) :
    letI : Comodule R C N := Transport (R := R) (C := C) (M := M) (N := N) e
    transportHom (R := R) (C := C) (M := M) (M' := M) (N := N) (N' := N) e e
        (Comodule.Hom.id R C M) =
      Comodule.Hom.id R C N :=
  by
    letI : Comodule R C N := Transport (R := R) (C := C) (M := M) (N := N) e
    ext n
    rw [transportHom_apply, Comodule.Hom.id_apply, Comodule.Hom.id_apply]
    exact e.apply_symm_apply n

variable {P : Type*} {P' : Type*}
variable [AddCommMonoid P] [Module R P] [Comodule R C P]
variable [AddCommMonoid P'] [Module R P']

/-- Transporting morphisms preserves composition. -/
@[simp]
theorem transportHom_comp (eM : M ≃ₗ[R] N) (eM' : M' ≃ₗ[R] N') (eP : P ≃ₗ[R] P')
    (f : Hom R C M M') (g : Hom R C M' P) :
    letI : Comodule R C N := Transport (R := R) (C := C) (M := M) (N := N) eM
    letI : Comodule R C N' := Transport (R := R) (C := C) (M := M') (N := N') eM'
    letI : Comodule R C P' := Transport (R := R) (C := C) (M := P) (N := P') eP
    transportHom (R := R) (C := C) (M := M) (M' := P) (N := N) (N' := P') eM eP
        (Comodule.Hom.comp g f) =
      Comodule.Hom.comp
        (transportHom (R := R) (C := C) (M := M') (M' := P) (N := N') (N' := P')
          eM' eP g)
        (transportHom (R := R) (C := C) (M := M) (M' := M') (N := N) (N' := N')
          eM eM' f) :=
  by
    letI : Comodule R C N := Transport (R := R) (C := C) (M := M) (N := N) eM
    letI : Comodule R C N' := Transport (R := R) (C := C) (M := M') (N := N') eM'
    letI : Comodule R C P' := Transport (R := R) (C := C) (M := P) (N := P') eP
    ext n
    simp [transportHom_apply, Comodule.Hom.comp_apply]

/-- The forward morphism from a comodule to its transport along a linear equivalence. -/
def transportToHom (e : M ≃ₗ[R] N) :
    letI : Comodule R C N := Transport (R := R) (C := C) (M := M) (N := N) e
    Hom R C M N :=
  letI : Comodule R C N := Transport (R := R) (C := C) (M := M) (N := N) e
  { toLinearMap := e.toLinearMap
    map_coact := by
      ext m
      simp [transportCoact] }

/-- The inverse morphism from a transported comodule back to the original comodule. -/
def transportInvHom (e : M ≃ₗ[R] N) :
    letI : Comodule R C N := Transport (R := R) (C := C) (M := M) (N := N) e
    Hom R C N M :=
  letI : Comodule R C N := Transport (R := R) (C := C) (M := M) (N := N) e
  { toLinearMap := e.symm.toLinearMap
    map_coact := by
      ext n
      dsimp [transportCoact]
      simpa using tensor_map_transport_conj (R := R) (C := C) (M := M) (N := N) (M' := M)
        (N' := M) e (LinearEquiv.refl R M) (LinearMap.id (R := R) (M := M))
        (coact (R := R) (C := C) (M := M) (e.symm n)) }

/-- The forward transport morphism has the original linear equivalence underneath. -/
@[simp]
theorem transportToHom_toLinearMap (e : M ≃ₗ[R] N) :
    letI : Comodule R C N := Transport (R := R) (C := C) (M := M) (N := N) e
    (transportToHom (R := R) (C := C) (M := M) (N := N) e).toLinearMap =
      e.toLinearMap := by
  rfl

/-- The inverse transport morphism has the inverse linear equivalence underneath. -/
@[simp]
theorem transportInvHom_toLinearMap (e : M ≃ₗ[R] N) :
    letI : Comodule R C N := Transport (R := R) (C := C) (M := M) (N := N) e
    (transportInvHom (R := R) (C := C) (M := M) (N := N) e).toLinearMap =
      e.symm.toLinearMap := by
  rfl

/-- Pointwise form of `transportToHom_toLinearMap`. -/
@[simp]
theorem transportToHom_apply (e : M ≃ₗ[R] N) (m : M) :
    letI : Comodule R C N := Transport (R := R) (C := C) (M := M) (N := N) e
    transportToHom (R := R) (C := C) (M := M) (N := N) e m = e m := by
  rfl

/-- Pointwise form of `transportInvHom_toLinearMap`. -/
@[simp]
theorem transportInvHom_apply (e : M ≃ₗ[R] N) (n : N) :
    letI : Comodule R C N := Transport (R := R) (C := C) (M := M) (N := N) e
    transportInvHom (R := R) (C := C) (M := M) (N := N) e n = e.symm n := by
  rfl

end Comodule

namespace ComoduleCat

variable (R : Type u) [CommSemiring R]
variable (C : Type v) [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
variable {N : Type x} [AddCommMonoid N] [Module R N]

/-- Bundle the transport of a comodule structure across a linear equivalence. -/
def transport (e : M ≃ₗ[R] N) : ComoduleCat.{u, v, x} R C where
  carrier := N
  instComodule := Comodule.Transport (R := R) (C := C) (M := M) (N := N) e

/-- The coaction on `ComoduleCat.transport` is the transported coaction. -/
@[simp]
theorem transport_coact (e : M ≃ₗ[R] N) :
    Comodule.coact (R := R) (C := C) (M := transport R C e) =
      Comodule.transportCoact (R := R) (C := C) (M := M) (N := N) e :=
  rfl

variable {N₀ : Type w} [AddCommMonoid N₀] [Module R N₀]

/-- The categorical isomorphism from a comodule to its transport along a linear equivalence. -/
def transportIso (e : M ≃ₗ[R] N₀) : of R C M ≅ transport R C e where
  hom := Comodule.transportToHom (R := R) (C := C) (M := M) (N := N₀) e
  inv := Comodule.transportInvHom (R := R) (C := C) (M := M) (N := N₀) e
  hom_inv_id := Comodule.Hom.ext fun m => e.symm_apply_apply m
  inv_hom_id := Comodule.Hom.ext fun n => e.apply_symm_apply n

/-- The transport isomorphism has the original linear equivalence as its forward map. -/
@[simp]
theorem transportIso_hom_toLinearMap (e : M ≃ₗ[R] N₀) :
    ((transportIso (R := R) (C := C) e).hom).toLinearMap = e.toLinearMap :=
  Comodule.transportToHom_toLinearMap (R := R) (C := C) (M := M) (N := N₀) e

/-- The transport isomorphism has the inverse linear equivalence as its inverse map. -/
@[simp]
theorem transportIso_inv_toLinearMap (e : M ≃ₗ[R] N₀) :
    ((transportIso (R := R) (C := C) e).inv).toLinearMap = e.symm.toLinearMap :=
  Comodule.transportInvHom_toLinearMap (R := R) (C := C) (M := M) (N := N₀) e

/-- The forward map of the transport isomorphism applies as the original linear equivalence. -/
@[simp]
theorem transportIso_hom_apply (e : M ≃ₗ[R] N₀) (m : M) :
    (transportIso (R := R) (C := C) e).hom m = e m :=
  rfl

/-- The inverse map of the transport isomorphism applies as the inverse linear equivalence. -/
@[simp]
theorem transportIso_inv_apply (e : M ≃ₗ[R] N₀) (n : N₀) :
    (transportIso (R := R) (C := C) e).inv n = e.symm n :=
  rfl

end ComoduleCat

end TauCeti
