/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Semi
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import TauCeti.Algebra.Coalgebra.Comodule.Hom

/-!
# The category of comodules over a coalgebra

This file bundles the right comodules defined in `TauCeti.Algebra.Coalgebra.Comodule.Basic` into a
category. For a fixed coalgebra `C` over a commutative semiring `R`, objects are
`R`-semimodules with a right `C`-coaction and morphisms are the comodule morphisms already
defined by `Comodule.Hom`.

The reductive-groups roadmap asks for the category of finite-dimensional comodules over a
Hopf algebra as the representation category of an affine group scheme. This file supplies the
underlying bundled category and its forgetful functor to `SemimoduleCat`; finiteness, tensor
products, duals, and the Hopf-algebra specialization can be added on top.

## Main definitions

* `TauCeti.ComoduleCat`: bundled right comodules over a fixed coalgebra.
* `TauCeti.ComoduleCat.of`: build a bundled comodule from an unbundled one.
* `TauCeti.ComoduleCat.ofHom`: view an unbundled comodule morphism as a categorical morphism.
* `forget₂ (ComoduleCat R C) (SemimoduleCat R)`: the forgetful functor to semimodules.

## References

This is the categorical packaging of the standard right-comodule definition, added for
Layer 1 of the Tau Ceti reductive-groups roadmap: "Comodules over a coalgebra/Hopf algebra".
The bundled-category API follows the pattern of `Mathlib.Algebra.Category.CoalgCat.Basic` and
`Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat`.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v w

variable (R : Type u) [CommSemiring R]
variable (C : Type v) [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The category of right comodules over a fixed `R`-coalgebra `C`. -/
structure ComoduleCat extends SemimoduleCat.{w} R where
  /-- The right `C`-comodule structure on the underlying module. -/
  instComodule : Comodule R C carrier

attribute [instance] ComoduleCat.instComodule

namespace ComoduleCat

instance : CoeSort (ComoduleCat.{u, v, w} R C) (Type w) :=
  ⟨fun M => M.toSemimoduleCat⟩

instance (M : ComoduleCat.{u, v, w} R C) : AddCommMonoid M :=
  M.isAddCommMonoid

instance (M : ComoduleCat.{u, v, w} R C) : Module R M :=
  M.isModule

/-- Build a bundled comodule from a type carrying the usual unbundled typeclasses. -/
abbrev of (M : Type w) [AddCommMonoid M] [Module R M] [Comodule R C M] :
    ComoduleCat.{u, v, w} R C where
  carrier := M
  instComodule := inferInstance

/-- The coaction on `ComoduleCat.of` is the original unbundled coaction. -/
@[simp]
theorem of_coact {M : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M] :
    Comodule.coact (R := R) (C := C) (M := of R C M) =
      Comodule.coact (R := R) (C := C) (M := M) :=
  rfl

/-- Morphisms in `ComoduleCat` are morphisms of the underlying right comodules. -/
abbrev Hom (M N : ComoduleCat.{u, v, w} R C) :=
  Comodule.Hom R C M N

instance category : Category (ComoduleCat.{u, v, w} R C) where
  Hom M N := Hom R C M N
  id M := Comodule.Hom.id R C M
  comp f g := Comodule.Hom.comp g f

/-- The zero structure on categorical morphisms is the zero comodule morphism. -/
instance homZero (M N : ComoduleCat.{u, v, w} R C) : Zero (M ⟶ N) :=
  inferInstanceAs (Zero (Comodule.Hom R C M N))

/-- Addition of categorical morphisms is pointwise addition of comodule morphisms. -/
instance homAdd (M N : ComoduleCat.{u, v, w} R C) : Add (M ⟶ N) :=
  inferInstanceAs (Add (Comodule.Hom R C M N))

/-- Categorical morphisms form an additive commutative monoid under pointwise operations. -/
instance homAddCommMonoid (M N : ComoduleCat.{u, v, w} R C) : AddCommMonoid (M ⟶ N) :=
  inferInstanceAs (AddCommMonoid (Comodule.Hom R C M N))

/-- Scalar multiplication of categorical morphisms is pointwise scalar multiplication of
comodule morphisms. -/
instance homSMul (M N : ComoduleCat.{u, v, w} R C) : SMul R (M ⟶ N) :=
  inferInstanceAs (SMul R (Comodule.Hom R C M N))

/-- Categorical morphisms form an `R`-module under pointwise operations. -/
instance homModule (M N : ComoduleCat.{u, v, w} R C) : Module R (M ⟶ N) :=
  inferInstanceAs (Module R (Comodule.Hom R C M N))

/-- `ComoduleCat` is concrete, with concrete morphisms the bundled comodule morphisms. -/
instance concreteCategory :
    ConcreteCategory (ComoduleCat.{u, v, w} R C)
      (fun M N => Comodule.Hom R C M N) where
  hom f := f
  ofHom f := f

/-- Turn a morphism in `ComoduleCat` back into its underlying comodule morphism. -/
abbrev hom {M N : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) :
    Comodule.Hom R C M N :=
  f

/-- Typecheck an unbundled comodule morphism as a morphism in `ComoduleCat`. -/
abbrev ofHom {M N : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] (f : Comodule.Hom R C M N) :
    of R C M ⟶ of R C N :=
  f

/-- Turning an unbundled comodule morphism into a categorical morphism and back is the identity. -/
@[simp]
theorem hom_ofHom {M N : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] (f : Comodule.Hom R C M N) :
    ConcreteCategory.hom (C := ComoduleCat R C) (ofHom (R := R) (C := C) f) = f :=
  rfl

/-- Turning a categorical morphism into an unbundled comodule morphism and back is the identity. -/
@[simp]
theorem ofHom_hom {M N : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) :
    ofHom (R := R) (C := C) (ConcreteCategory.hom (C := ComoduleCat R C) f) = f :=
  rfl

/-- The categorical identity is the bundled form of the identity comodule morphism. -/
@[simp]
theorem ofHom_id {M : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M] :
    ofHom (R := R) (C := C) (Comodule.Hom.id R C M) = 𝟙 (of R C M) :=
  rfl

/-- Categorical composition is the bundled form of composition of comodule morphisms. -/
@[simp]
theorem ofHom_comp {M N P : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N]
    [AddCommMonoid P] [Module R P] [Comodule R C P] (f : Comodule.Hom R C M N)
    (g : Comodule.Hom R C N P) :
    ofHom (R := R) (C := C) (Comodule.Hom.comp g f) =
      ofHom (R := R) (C := C) f ≫ ofHom (R := R) (C := C) g :=
  rfl

/-- The bundled form of a comodule morphism applies as the original morphism. -/
@[simp]
theorem ofHom_apply {M N : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
    [AddCommMonoid N] [Module R N] [Comodule R C N] (f : Comodule.Hom R C M N) (m : M) :
    ofHom (R := R) (C := C) f m = f m :=
  rfl

/-- The underlying linear map of a `ComoduleCat` morphism. -/
abbrev homLinearMap {M N : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) : M →ₗ[R] N :=
  f.toLinearMap

/-- Two morphisms of bundled comodules are equal when their underlying functions are equal. -/
@[ext]
theorem hom_ext {M N : ComoduleCat.{u, v, w} R C} {f g : M ⟶ N} (h : ∀ m, f m = g m) : f = g :=
  Comodule.Hom.ext h

/-- The identity morphism has the identity linear map underneath. -/
@[simp]
theorem toLinearMap_id (M : ComoduleCat.{u, v, w} R C) : (𝟙 M : M ⟶ M).toLinearMap = LinearMap.id :=
  rfl

/-- Composition in `ComoduleCat` is composition of the underlying linear maps. -/
@[simp]
theorem toLinearMap_comp {M N P : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  rfl

/-- The identity morphism acts as the identity function. -/
@[simp]
theorem id_apply (M : ComoduleCat.{u, v, w} R C) (m : M) : (𝟙 M : M ⟶ M) m = m :=
  rfl

/-- Composition of morphisms acts by ordinary function composition. -/
@[simp]
theorem comp_apply {M N P : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) (g : N ⟶ P) (m : M) :
    (f ≫ g) m = g (f m) :=
  rfl

/-- The zero morphism has the zero linear map underneath. -/
@[simp]
theorem toLinearMap_zero (M N : ComoduleCat.{u, v, w} R C) : (0 : M ⟶ N).toLinearMap = 0 :=
  rfl

/-- Addition of morphisms is addition of the underlying linear maps. -/
@[simp]
theorem toLinearMap_add {M N : ComoduleCat.{u, v, w} R C} (f g : M ⟶ N) :
    (f + g).toLinearMap = f.toLinearMap + g.toLinearMap :=
  rfl

/-- Natural-number scalar multiplication of morphisms is natural-number scalar multiplication
of the underlying linear maps. -/
@[simp]
theorem toLinearMap_nsmul {M N : ComoduleCat.{u, v, w} R C} (n : ℕ) (f : M ⟶ N) :
    (n • f).toLinearMap = n • f.toLinearMap :=
  Comodule.Hom.nsmul_toLinearMap n f

/-- Scalar multiplication of morphisms is scalar multiplication of the underlying linear maps. -/
@[simp]
theorem toLinearMap_smul {M N : ComoduleCat.{u, v, w} R C} (r : R) (f : M ⟶ N) :
    (r • f).toLinearMap = r • f.toLinearMap :=
  rfl

/-- Finite sums of morphisms are finite sums of the underlying linear maps. -/
@[simp]
theorem toLinearMap_sum {ι : Type*} {M N : ComoduleCat.{u, v, w} R C} (s : Finset ι)
    (f : ι → (M ⟶ N)) : (∑ i ∈ s, f i).toLinearMap = ∑ i ∈ s, (f i).toLinearMap :=
  Comodule.Hom.sum_toLinearMap s f

/-- The zero morphism acts as the zero function. -/
@[simp]
theorem zero_apply {M N : ComoduleCat.{u, v, w} R C} (m : M) : (0 : M ⟶ N) m = 0 :=
  rfl

/-- Addition of morphisms acts by pointwise addition. -/
@[simp]
theorem add_apply {M N : ComoduleCat.{u, v, w} R C} (f g : M ⟶ N) (m : M) : (f + g) m = f m + g m :=
  rfl

/-- Natural-number scalar multiplication of morphisms acts by pointwise natural-number scalar
multiplication. -/
@[simp]
theorem nsmul_apply {M N : ComoduleCat.{u, v, w} R C} (n : ℕ) (f : M ⟶ N) (m : M) :
    (n • f) m = n • f m :=
  Comodule.Hom.nsmul_apply n f m

/-- Scalar multiplication of morphisms acts by pointwise scalar multiplication. -/
@[simp]
theorem smul_apply {M N : ComoduleCat.{u, v, w} R C} (r : R) (f : M ⟶ N) (m : M) :
    (r • f) m = r • f m :=
  rfl

/-- Finite sums of morphisms act by pointwise finite sums. -/
@[simp]
theorem sum_apply {ι : Type*} {M N : ComoduleCat.{u, v, w} R C} (s : Finset ι)
    (f : ι → (M ⟶ N)) (m : M) : (∑ i ∈ s, f i) m = ∑ i ∈ s, f i m :=
  Comodule.Hom.sum_apply s f m

/-- Composition in `ComoduleCat` is additive in the left morphism. -/
@[simp]
theorem add_comp {M N P : ComoduleCat.{u, v, w} R C} (f g : M ⟶ N) (h : N ⟶ P) :
    (f + g) ≫ h = f ≫ h + g ≫ h := by
  ext m
  exact map_add h.toLinearMap (f m) (g m)

/-- Composition in `ComoduleCat` is additive in the right morphism. -/
@[simp]
theorem comp_add {M N P : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) (g h : N ⟶ P) :
    f ≫ (g + h) = f ≫ g + f ≫ h := by
  ext m
  rfl

/-- Composition in `ComoduleCat` is compatible with scalar multiplication in the left
morphism. -/
@[simp]
theorem smul_comp {M N P : ComoduleCat.{u, v, w} R C} (r : R) (f : M ⟶ N) (g : N ⟶ P) :
    (r • f) ≫ g = r • (f ≫ g) := by
  ext m
  exact map_smul g.toLinearMap r (f m)

/-- Composition in `ComoduleCat` is compatible with scalar multiplication in the right
morphism. -/
@[simp]
theorem comp_smul {M N P : ComoduleCat.{u, v, w} R C} (r : R) (f : M ⟶ N) (g : N ⟶ P) :
    f ≫ (r • g) = r • (f ≫ g) := by
  ext m
  rfl

/-- Composing the zero morphism on the left gives the zero morphism. -/
theorem zero_comp {M N P : ComoduleCat.{u, v, w} R C} (f : N ⟶ P) : (0 : M ⟶ N) ≫ f = 0 := by
  ext m
  exact map_zero f.toLinearMap

/-- Composing the zero morphism on the right gives the zero morphism. -/
theorem comp_zero {M N P : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) :
    f ≫ (0 : N ⟶ P) = 0 := by
  ext m
  rfl

/-- `ComoduleCat` has the standard categorical zero morphisms. -/
instance hasZeroMorphisms :
    CategoryTheory.Limits.HasZeroMorphisms (ComoduleCat.{u, v, w} R C) where
  zero := inferInstance
  comp_zero := fun f P => ComoduleCat.comp_zero (R := R) (C := C) (P := P) f
  zero_comp := fun M {N P} f => ComoduleCat.zero_comp (R := R) (C := C) (M := M) (N := N)
    (P := P) f

/-- The forgetful functor from comodules to their underlying semimodules. -/
instance hasForgetToSemimodule : HasForget₂ (ComoduleCat.{u, v, w} R C) (SemimoduleCat.{w} R) where
  forget₂ :=
    { obj M := SemimoduleCat.of R M
      map f := SemimoduleCat.ofHom f.toLinearMap }

/-- The forgetful functor sends a comodule to its underlying semimodule. -/
@[simp]
theorem forget₂_obj (M : ComoduleCat.{u, v, w} R C) :
    (forget₂ (ComoduleCat.{u, v, w} R C) (SemimoduleCat.{w} R)).obj M =
      SemimoduleCat.of R M :=
  rfl

/-- The forgetful functor sends a comodule morphism to its underlying linear map. -/
@[simp]
theorem forget₂_map {M N : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) :
    (forget₂ (ComoduleCat.{u, v, w} R C) (SemimoduleCat.{w} R)).map f =
      SemimoduleCat.ofHom f.toLinearMap :=
  rfl

/-- A categorical isomorphism of comodules induces the underlying linear equivalence. -/
@[expose] def isoToLinearEquiv {M N : ComoduleCat.{u, v, w} R C} (i : M ≅ N) : M ≃ₗ[R] N :=
  ((forget₂ (ComoduleCat.{u, v, w} R C) (SemimoduleCat.{w} R)).mapIso i).toLinearEquivₛ

/-- The linear equivalence induced by a comodule isomorphism has the isomorphism's forward
comodule morphism underneath. -/
@[simp]
theorem isoToLinearEquiv_toLinearMap {M N : ComoduleCat.{u, v, w} R C} (i : M ≅ N) :
    (isoToLinearEquiv (R := R) (C := C) i).toLinearMap = i.hom.toLinearMap :=
  rfl

/-- The inverse of the linear equivalence induced by a comodule isomorphism has the
isomorphism's inverse comodule morphism underneath. -/
@[simp]
theorem isoToLinearEquiv_symm_toLinearMap {M N : ComoduleCat.{u, v, w} R C} (i : M ≅ N) :
    (isoToLinearEquiv (R := R) (C := C) i).symm.toLinearMap = i.inv.toLinearMap :=
  rfl

/-- The linear equivalence induced by a comodule isomorphism applies as its forward morphism. -/
@[simp]
theorem isoToLinearEquiv_apply {M N : ComoduleCat.{u, v, w} R C} (i : M ≅ N) (m : M) :
    isoToLinearEquiv (R := R) (C := C) i m = i.hom m :=
  rfl

/-- The inverse linear equivalence induced by a comodule isomorphism applies as the inverse
morphism. -/
@[simp]
theorem isoToLinearEquiv_symm_apply {M N : ComoduleCat.{u, v, w} R C} (i : M ≅ N) (n : N) :
    (isoToLinearEquiv (R := R) (C := C) i).symm n = i.inv n :=
  rfl

/-- The linear equivalence induced by the identity comodule isomorphism is the identity. -/
@[simp]
theorem isoToLinearEquiv_refl (M : ComoduleCat.{u, v, w} R C) :
    isoToLinearEquiv (R := R) (C := C) (Iso.refl M) = LinearEquiv.refl R M := by
  ext m
  rfl

/-- The linear equivalence induced by the inverse comodule isomorphism is the inverse linear
equivalence. -/
@[simp]
theorem isoToLinearEquiv_symm {M N : ComoduleCat.{u, v, w} R C} (i : M ≅ N) :
    isoToLinearEquiv (R := R) (C := C) i.symm =
      (isoToLinearEquiv (R := R) (C := C) i).symm := by
  ext n
  rfl

/-- The linear equivalence induced by a composite comodule isomorphism is the composite of
the induced linear equivalences. -/
@[simp]
theorem isoToLinearEquiv_trans {M N P : ComoduleCat.{u, v, w} R C} (i : M ≅ N) (j : N ≅ P) :
    isoToLinearEquiv (R := R) (C := C) (i ≪≫ j) =
      (isoToLinearEquiv (R := R) (C := C) i).trans
        (isoToLinearEquiv (R := R) (C := C) j) := by
  ext m
  rfl

/-- Build a comodule isomorphism from a linear equivalence whose forward map respects the
coactions. -/
@[expose] def isoOfLinearEquiv {M N : ComoduleCat.{u, v, w} R C} (e : M ≃ₗ[R] N)
    (h : TensorProduct.map e.toLinearMap LinearMap.id ∘ₗ
        Comodule.coact (R := R) (C := C) (M := M) =
      Comodule.coact (R := R) (C := C) (M := N) ∘ₗ e.toLinearMap)
    : M ≅ N where
  hom :=
    { toLinearMap := e.toLinearMap
      map_coact := h }
  inv :=
    { toLinearMap := e.symm.toLinearMap
      map_coact := by
        ext n
        have hn : TensorProduct.map e.toLinearMap LinearMap.id
              (Comodule.coact (R := R) (C := C) (M := M) (e.symm n)) =
            Comodule.coact (R := R) (C := C) (M := N) n := by
          simpa using LinearMap.congr_fun h (e.symm n)
        have hn' := congrArg (TensorProduct.map e.symm.toLinearMap LinearMap.id) hn
        simpa [TensorProduct.map_map] using hn'.symm }
  hom_inv_id := by
      ext m
      exact e.symm_apply_apply m
  inv_hom_id := by
      ext n
      exact e.apply_symm_apply n

/-- The forward morphism of `isoOfLinearEquiv` has the original linear equivalence
underneath. -/
@[simp]
theorem isoOfLinearEquiv_hom_toLinearMap {M N : ComoduleCat.{u, v, w} R C} (e : M ≃ₗ[R] N) (h) :
    ((isoOfLinearEquiv (R := R) (C := C) e h).hom).toLinearMap = e.toLinearMap :=
  rfl

/-- The inverse morphism of `isoOfLinearEquiv` has the inverse linear equivalence
underneath. -/
@[simp]
theorem isoOfLinearEquiv_inv_toLinearMap {M N : ComoduleCat.{u, v, w} R C} (e : M ≃ₗ[R] N) (h) :
    ((isoOfLinearEquiv (R := R) (C := C) e h).inv).toLinearMap =
      e.symm.toLinearMap :=
  rfl

/-- The forward morphism of `isoOfLinearEquiv` applies as the original linear equivalence. -/
@[simp]
theorem isoOfLinearEquiv_hom_apply {M N : ComoduleCat.{u, v, w} R C} (e : M ≃ₗ[R] N) (h) (m : M) :
    (isoOfLinearEquiv (R := R) (C := C) e h).hom m = e m :=
  rfl

/-- The inverse morphism of `isoOfLinearEquiv` applies as the inverse linear equivalence. -/
@[simp]
theorem isoOfLinearEquiv_inv_apply {M N : ComoduleCat.{u, v, w} R C} (e : M ≃ₗ[R] N) (h) (n : N) :
    (isoOfLinearEquiv (R := R) (C := C) e h).inv n = e.symm n :=
  rfl

/-- Converting `isoOfLinearEquiv` back to a linear equivalence recovers the original linear
equivalence. -/
@[simp]
theorem isoToLinearEquiv_isoOfLinearEquiv {M N : ComoduleCat.{u, v, w} R C} (e : M ≃ₗ[R] N) (h) :
    isoToLinearEquiv (R := R) (C := C) (isoOfLinearEquiv (R := R) (C := C) e h) =
      e := by
  ext m
  rfl

/-- Rebuilding a comodule isomorphism from its induced linear equivalence recovers the original
isomorphism. -/
@[simp]
theorem isoOfLinearEquiv_isoToLinearEquiv {M N : ComoduleCat.{u, v, w} R C} (i : M ≅ N) :
    isoOfLinearEquiv (R := R) (C := C) (isoToLinearEquiv (R := R) (C := C) i)
      (by simp [i.hom.map_coact]) = i := by
  ext m
  rfl

end ComoduleCat

end TauCeti
