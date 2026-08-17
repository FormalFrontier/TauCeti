/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.LinearAlgebra.End.ScalarExtension

/-!
# Automorphisms of scalar extensions

For a module `V` over a commutative ring `R`, this file packages

`A ↦ Autₐ(A ⊗[R] V)`

as a functor from commutative `R`-algebras to groups. A morphism `φ : A ⟶ B` acts by base change of
the automorphism, `Module.End.mapValueGL`; this file only indexes that operation by the
bundled category of commutative algebras and packages the result as a functor.

The public characterization uses the canonical map `A ⊗[R] V → B ⊗[R] V`. Scalar
extension of an automorphism commutes with this map, and its value on a pure tensor is consequently
determined by the original automorphism on `1 ⊗ₜ v`.

No finiteness, freeness, projectivity, flatness, or nontriviality hypothesis is used. In particular,
the construction includes zero rings and the zero module. This is only the fixed-module
automorphism functor; no representability or functoriality in `V` is asserted.

## Main declarations

* `GeneralLinear.scalarExtensionAutomorphisms`: the automorphism group at a value algebra.
* `GeneralLinear.mapScalarExtensionAutomorphisms`: extension of automorphisms along a value-algebra
  morphism.
* `GeneralLinear.scalarExtensionAutomorphismsFunctor`: the resulting group-valued functor.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.8 and Chapter 4(a).
* The Stacks Project, Tags [00CV](https://stacks.math.columbia.edu/tag/00CV) and
  [05G3](https://stacks.math.columbia.edu/tag/05G3).
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

namespace GeneralLinear

universe u v w

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommMonoid V] [Module R V]

/-- The group of linear automorphisms of the scalar extension `A ⊗[R] V`. -/
abbrev scalarExtensionAutomorphisms (A : CommAlgCat.{w} R) :
    GrpCat.{max v w} :=
  GrpCat.of (LinearMap.GeneralLinearGroup A (A ⊗[R] V))

/-- The canonical map between scalar extensions induced by a morphism of value algebras. -/
def scalarExtensionMap {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    A ⊗[R] V →ₗ[R] B ⊗[R] V :=
  φ.hom.toLinearMap.rTensor V

/-- The canonical map between scalar extensions sends a pure tensor to the corresponding pure
tensor with its scalar mapped into the target algebra. -/
@[simp]
lemma scalarExtensionMap_tmul {A B : CommAlgCat.{w} R} (φ : A ⟶ B) (a : A) (v : V) :
    scalarExtensionMap (V := V) φ (a ⊗ₜ[R] v) = φ.hom a ⊗ₜ[R] v := by
  simp [scalarExtensionMap]

/-- The canonical map between scalar extensions is the value-algebra morphism tensored with the
identity of the module. -/
lemma scalarExtensionMap_eq_map {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    scalarExtensionMap (V := V) φ =
      TensorProduct.map φ.hom.toLinearMap (LinearMap.id (R := R) (M := V)) := by
  ext a v
  simp

/-- Over a flat module, the canonical map between scalar extensions inherits injectivity from the
value-algebra morphism. -/
lemma scalarExtensionMap_injective [Module.Flat R V] {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (hφ : Function.Injective φ.hom) :
    Function.Injective (scalarExtensionMap (V := V) φ) :=
  Module.Flat.rTensor_preserves_injective_linearMap _ hφ

/-- The canonical map associated to the identity morphism is the identity linear map. -/
@[simp]
lemma scalarExtensionMap_id (A : CommAlgCat.{w} R) :
    scalarExtensionMap (V := V) (𝟙 A) = LinearMap.id := by
  unfold scalarExtensionMap
  simpa only [CommAlgCat.hom_id, AlgHom.toLinearMap_id] using
    (LinearMap.rTensor_id (R := R) V A)

/-- Canonical maps between scalar extensions compose covariantly. -/
@[simp]
lemma scalarExtensionMap_comp {A B C : CommAlgCat.{w} R} (φ : A ⟶ B) (ψ : B ⟶ C) :
    scalarExtensionMap (V := V) (φ ≫ ψ) =
      (scalarExtensionMap (V := V) ψ).comp (scalarExtensionMap (V := V) φ) := by
  unfold scalarExtensionMap
  simpa only [CommAlgCat.hom_comp, AlgHom.comp_toLinearMap] using
    (LinearMap.rTensor_comp (M := V) (f := φ.hom.toLinearMap) (g := ψ.hom.toLinearMap))

/-- The canonical map between scalar extensions is semilinear for the value-algebra morphism. -/
@[simp]
lemma scalarExtensionMap_smul {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (a : A) (x : A ⊗[R] V) :
    scalarExtensionMap (V := V) φ (a • x) =
      φ.hom a • scalarExtensionMap (V := V) φ x :=
  rTensor_algHom_smul φ.hom a x

/-- Extend a scalar-extension automorphism along a morphism of value algebras.

This is `Module.End.mapValueGL` at the underlying algebra morphism, bundled as a morphism of
groups; all of its computation rules come from there. -/
noncomputable def mapScalarExtensionAutomorphisms
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    scalarExtensionAutomorphisms (V := V) A ⟶
      scalarExtensionAutomorphisms (V := V) B :=
  GrpCat.ofHom (Module.End.mapValueGL (M := V) φ.hom)

/-- The underlying endomorphism of an extended automorphism is the base change of the underlying
endomorphism. -/
@[simp]
lemma val_mapScalarExtensionAutomorphisms
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (g : scalarExtensionAutomorphisms (V := V) A) :
    ((mapScalarExtensionAutomorphisms (V := V) φ g).val : Module.End B (B ⊗[R] V)) =
      Module.End.mapValue φ.hom (g : Module.End A (A ⊗[R] V)) := by
  simp [mapScalarExtensionAutomorphisms]

/-- Scalar extension of an automorphism is characterized on pure tensors by its value on the
canonical copy of the original module. -/
@[simp]
lemma mapScalarExtensionAutomorphisms_tmul
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (g : scalarExtensionAutomorphisms (V := V) A) (b : B) (v : V) :
    (mapScalarExtensionAutomorphisms (V := V) φ g).val (b ⊗ₜ[R] v) =
      b • scalarExtensionMap (V := V) φ (g.val (1 ⊗ₜ[R] v)) := by
  rw [val_mapScalarExtensionAutomorphisms, scalarExtensionMap, Module.End.mapValue_tmul]

/-- Extending an automorphism commutes with the canonical map between scalar extensions. -/
@[simp]
lemma mapScalarExtensionAutomorphisms_apply_scalarExtensionMap
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (g : scalarExtensionAutomorphisms (V := V) A) (x : A ⊗[R] V) :
    (mapScalarExtensionAutomorphisms (V := V) φ g).val
        (scalarExtensionMap (V := V) φ x) =
      scalarExtensionMap (V := V) φ (g.val x) := by
  rw [val_mapScalarExtensionAutomorphisms, scalarExtensionMap,
    Module.End.mapValue_rTensor_apply]

/-- A target automorphism that intertwines the canonical map with `g` is the scalar extension of
`g`. -/
lemma eq_mapScalarExtensionAutomorphisms_of_apply_scalarExtensionMap_eq
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (g : scalarExtensionAutomorphisms (V := V) A)
    (h : scalarExtensionAutomorphisms (V := V) B)
    (h_apply : ∀ x, h.val (scalarExtensionMap (V := V) φ x) =
      scalarExtensionMap (V := V) φ (g.val x)) :
    h = mapScalarExtensionAutomorphisms (V := V) φ g := by
  refine Units.ext ?_
  rw [val_mapScalarExtensionAutomorphisms]
  exact Module.End.eq_mapValue φ.hom (g : Module.End A (A ⊗[R] V))
    (h : Module.End B (B ⊗[R] V)) (LinearMap.ext h_apply)

/-- Extension of automorphisms is injective as soon as the canonical map between scalar extensions
is. An automorphism of `A ⊗[R] V` is determined by its values on the pure tensors `1 ⊗ v`, and
those values are recorded faithfully by the canonical map. -/
lemma mapScalarExtensionAutomorphisms_injective
    {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (hφ : Function.Injective (scalarExtensionMap (V := V) φ)) :
    Function.Injective (mapScalarExtensionAutomorphisms (V := V) φ) := by
  intro g g' hg
  apply Units.ext
  refine LinearMap.ext fun x => hφ ?_
  rw [← mapScalarExtensionAutomorphisms_apply_scalarExtensionMap φ g x,
    ← mapScalarExtensionAutomorphisms_apply_scalarExtensionMap φ g' x, hg]

/-- Extension of scalar-extension automorphisms preserves identity morphisms of value algebras. -/
@[simp]
lemma mapScalarExtensionAutomorphisms_id (A : CommAlgCat.{w} R) :
    mapScalarExtensionAutomorphisms (V := V) (𝟙 A) =
      𝟙 (scalarExtensionAutomorphisms (V := V) A) := by
  refine GrpCat.ext fun g ↦ Units.ext ?_
  rw [val_mapScalarExtensionAutomorphisms, CommAlgCat.hom_id, Module.End.mapValue_id]
  rfl

/-- Extension of scalar-extension automorphisms preserves composition of value-algebra
morphisms. -/
@[simp]
lemma mapScalarExtensionAutomorphisms_comp
    {A B C : CommAlgCat.{w} R} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapScalarExtensionAutomorphisms (V := V) (φ ≫ ψ) =
      mapScalarExtensionAutomorphisms (V := V) φ ≫
        mapScalarExtensionAutomorphisms (V := V) ψ := by
  refine GrpCat.ext fun g ↦ Units.ext ?_
  rw [val_mapScalarExtensionAutomorphisms, CommAlgCat.hom_comp, Module.End.mapValue_comp,
    ← val_mapScalarExtensionAutomorphisms, ← val_mapScalarExtensionAutomorphisms]
  rfl

/-- The group-valued functor of linear automorphisms of scalar extensions of `V`. -/
-- `@[expose]` matches `HopfAlgebra.pointsFunctor`: natural transformations out of
-- either functor need the object part to unfold cross-module.
@[expose] noncomputable def scalarExtensionAutomorphismsFunctor :
    CommAlgCat.{w} R ⥤ GrpCat.{max v w} where
  obj A := scalarExtensionAutomorphisms (V := V) A
  map φ := mapScalarExtensionAutomorphisms (V := V) φ
  map_id A := mapScalarExtensionAutomorphisms_id (V := V) A
  map_comp φ ψ := mapScalarExtensionAutomorphisms_comp (V := V) φ ψ

/-- The functor takes a value algebra to the automorphism group of the corresponding scalar
extension. -/
@[simp]
lemma scalarExtensionAutomorphismsFunctor_obj (A : CommAlgCat.{w} R) :
    (scalarExtensionAutomorphismsFunctor (V := V)).obj A =
      scalarExtensionAutomorphisms (V := V) A :=
  (rfl)

/-- The functor takes a morphism of value algebras to the corresponding extension of
automorphisms. -/
@[simp]
lemma scalarExtensionAutomorphismsFunctor_map {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    (scalarExtensionAutomorphismsFunctor (V := V)).map φ =
      eqToHom (scalarExtensionAutomorphismsFunctor_obj (V := V) A) ≫
        mapScalarExtensionAutomorphisms (V := V) φ ≫
          eqToHom (scalarExtensionAutomorphismsFunctor_obj (V := V) B).symm := by
  apply (conj_eqToHom_iff_heq _ _
    (scalarExtensionAutomorphismsFunctor_obj (V := V) A)
    (scalarExtensionAutomorphismsFunctor_obj (V := V) B)).2
  unfold scalarExtensionAutomorphismsFunctor
  rfl

end GeneralLinear

end TauCeti
