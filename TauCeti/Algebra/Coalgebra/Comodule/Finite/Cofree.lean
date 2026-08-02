/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Cofree
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Basic

/-!
# Finitely generated cofree comodules

This file lifts the cofree right comodule `M ⊗[R] C` to the finitely generated comodule
category when the tensor-product carrier is finitely generated over `R`. It is the
finite-category version of `ComoduleCat.cofree`.

This is Layer 1 infrastructure for the Tau Ceti reductive-groups roadmap target
"Comodules over a coalgebra/Hopf algebra": the finite-dimensional representation category
needs finite versions of the regular and cofree comodules before tensor products, duals, and
the embedding theorem can be developed.

## Main definitions

* `TauCeti.FGComoduleCat.cofree`: the cofree comodule as a finitely generated object.
* `TauCeti.FGComoduleCat.cofreeMap`: functoriality between finite cofree objects.
* `TauCeti.FGComoduleCat.cofreeLift`: the finite-category form of the cofree lifting map.
* `TauCeti.FGComoduleCat.cofreeEquiv`: the cofree universal property in `FGComoduleCat`.
* `TauCeti.FGComoduleCat.incl_cofree`: forgetting the finite cofree comodule gives the
  ambient cofree comodule.

## References

The cofree-comodule construction follows Sweedler, *Hopf Algebras*, Chapter 2, as in
`TauCeti.Algebra.Coalgebra.Comodule.Cofree`.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v w

namespace FGComoduleCat

variable (R : Type u) (C : Type v)
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M : Type w} [AddCommMonoid M] [Module R M] [Module.Finite R (M ⊗[R] C)]
variable {N : Type w} [AddCommMonoid N] [Module R N] [Module.Finite R (N ⊗[R] C)]

-- Resolve the cofree comodule structure on `· ⊗[R] C` automatically, rather than threading it
-- through every statement with `letI`. As in `Comodule.Cofree`, this is a local (not global)
-- instance because an `R`-module can carry many coactions. The bundled `FGComoduleCat` objects
-- carry their own comodule instance, so this does not clash with their coactions.
attribute [local instance] Comodule.cofree

/-- The cofree right `C`-comodule with finitely generated tensor-product carrier, bundled as an
object of `FGComoduleCat`.

The underlying module is `M ⊗[R] C`, with coaction `id ⊗ Δ` followed by reassociation. -/
noncomputable abbrev cofree (M : Type w) [AddCommMonoid M] [Module R M]
    [Module.Finite R (M ⊗[R] C)] : FGComoduleCat.{u, v, max w v} R C :=
  of (R := R) (C := C) (M ⊗[R] C)

/-- Forgetting the finitely generated cofree comodule to all comodules gives the ambient
cofree comodule. -/
@[simp]
theorem cofree_obj : (cofree (R := R) (C := C) M).obj = ComoduleCat.cofree R C M :=
  rfl

/-- The underlying type of the finitely generated cofree comodule is `M ⊗[R] C`. -/
@[simp]
theorem cofree_coe : (cofree (R := R) (C := C) M : Type (max w v)) = M ⊗[R] C :=
  rfl

/-- The coaction on the finitely generated cofree comodule is `id ⊗ Δ` followed by
reassociation. -/
@[simp]
theorem cofree_coact :
    Comodule.coact (R := R) (C := C) (M := cofree (R := R) (C := C) M)
      = (TensorProduct.assoc R M C C).symm.toLinearMap ∘ₗ Coalgebra.comul.lTensor M :=
  rfl

/-- The coaction on the finitely generated cofree comodule sends a simple tensor
`m ⊗ c` to `∑ (m ⊗ c₁) ⊗ c₂`. -/
@[simp]
theorem cofree_coact_tmul (m : M) (c : C) :
    Comodule.coact (R := R) (C := C) (M := cofree (R := R) (C := C) M) (m ⊗ₜ[R] c)
      = (TensorProduct.assoc R M C C).symm (m ⊗ₜ Coalgebra.comul c) :=
  Comodule.cofree_coact_tmul m c

/-- The inclusion of finitely generated comodules sends `FGComoduleCat.cofree` to
`ComoduleCat.cofree`. -/
@[simp]
theorem incl_cofree : (incl (R := R) (C := C)).obj (cofree (R := R) (C := C) M) =
      ComoduleCat.cofree R C M :=
  rfl

/-- The finite cofree comodule forgets to the tensor product module `M ⊗[R] C`. -/
@[simp]
theorem forget₂_semimoduleCat_cofree_obj :
    (forget₂ (FGComoduleCat.{u, v, max w v} R C) (SemimoduleCat.{max w v} R)).obj
        (cofree (R := R) (C := C) M) =
      SemimoduleCat.of R (M ⊗[R] C) :=
  rfl

/-- Functoriality of finite cofree comodules in the coefficient module.

An `R`-linear map `f : M → N` induces the comodule morphism `f ⊗ id`. -/
noncomputable abbrev cofreeMap (f : M →ₗ[R] N) :
    cofree (R := R) (C := C) M ⟶ cofree (R := R) (C := C) N :=
  ofHom (R := R) (C := C) (Comodule.Hom.cofreeMap (C := C) f)

/-- `cofreeMap f` acts as `f ⊗ id`. -/
@[simp]
theorem cofreeMap_apply (f : M →ₗ[R] N) (x : M ⊗[R] C) :
    cofreeMap (R := R) (C := C) f x = f.rTensor C x :=
  rfl

/-- On simple tensors, `cofreeMap f` applies `f` to the coefficient factor. -/
@[simp]
theorem cofreeMap_tmul (f : M →ₗ[R] N) (m : M) (c : C) :
    cofreeMap (R := R) (C := C) f (m ⊗ₜ[R] c) = f m ⊗ₜ[R] c :=
  rfl

/-- The finite cofree construction sends the identity linear map to the identity morphism. -/
@[simp]
theorem cofreeMap_id :
    cofreeMap (R := R) (C := C) (LinearMap.id : M →ₗ[R] M) =
      𝟙 (cofree (R := R) (C := C) M) :=
  by
    ext x
    simp

/-- The finite cofree construction preserves composition of coefficient-module maps. -/
@[simp]
theorem cofreeMap_comp {P : Type w} [AddCommMonoid P] [Module R P]
    [Module.Finite R (P ⊗[R] C)] (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    cofreeMap (R := R) (C := C) (g.comp f) =
      cofreeMap (R := R) (C := C) f ≫ cofreeMap (R := R) (C := C) g := by
  ext x
  simp

variable {P : FGComoduleCat.{u, v, max w v} R C}

/-- The finite-category cofree lift of an `R`-linear map from a finite comodule to the
coefficient module. -/
noncomputable abbrev cofreeLift (P : FGComoduleCat.{u, v, max w v} R C) (g : P →ₗ[R] M) :
    P ⟶ cofree (R := R) (C := C) M :=
  ObjectProperty.homMk
    (ComoduleCat.ofHom (R := R) (C := C) (Comodule.Hom.cofreeLift (C := C) g))

/-- `cofreeLift g` acts as `(g ⊗ id) ∘ ρ_P`. -/
@[simp]
theorem cofreeLift_apply (g : P →ₗ[R] M) (p : P) :
    cofreeLift (R := R) (C := C) P g p =
      g.rTensor C (Comodule.coact (R := R) (C := C) (M := P) p) :=
  rfl

/-- The finite-category cofree universal property. -/
@[expose] noncomputable def cofreeEquiv (P : FGComoduleCat.{u, v, max w v} R C) :
    (P ⟶ cofree (R := R) (C := C) M) ≃ (P →ₗ[R] M) := by
  exact
    { toFun φ := Comodule.Hom.cofreeEquiv (R := R) (C := C) (M := M) (P := P) φ.hom
      invFun g := cofreeLift (R := R) (C := C) P g
      left_inv φ := by
        apply ObjectProperty.hom_ext
        exact (Comodule.Hom.cofreeEquiv (R := R) (C := C) (M := M) (P := P)).left_inv φ.hom
      right_inv g :=
        (Comodule.Hom.cofreeEquiv (R := R) (C := C) (M := M) (P := P)).right_inv g }

/-- The forward direction of the finite cofree adjunction sends a comodule morphism to the
`R`-linear map obtained by applying the counit to the `C` factor. -/
@[simp]
theorem cofreeEquiv_apply (φ : P ⟶ cofree (R := R) (C := C) M) :
    cofreeEquiv (R := R) (C := C) (M := M) P φ =
      Comodule.Hom.cofreeEquiv (R := R) (C := C) (M := M) (P := P) φ.hom := by
  rfl

/-- The inverse direction of the finite cofree adjunction is `cofreeLift`. -/
@[simp]
theorem cofreeEquiv_symm_apply (g : P →ₗ[R] M) : (cofreeEquiv (R := R) (C := C) (M := M) P).symm g =
      cofreeLift (R := R) (C := C) P g :=
  rfl

end FGComoduleCat

end TauCeti
