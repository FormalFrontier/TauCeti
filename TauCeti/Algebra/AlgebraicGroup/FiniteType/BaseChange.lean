/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.Product
public import Mathlib.RingTheory.FiniteStability

/-!
# Base change of finite-type commutative Hopf algebras

This file packages the scalar extension `K ⊗[k] H` of a finite-type commutative Hopf
`k`-algebra as a finite-type commutative Hopf `K`-algebra. The generic bundled commutative
Hopf-algebra base-change API is in `CommHopfAlgCatBaseChange`; this file restricts it to the
finite-type full subcategory, using Mathlib's finite-type base-change instance.

It is the finite-type coordinate-Hopf-algebra wrapper for the ReductiveGroups roadmap Layer 0
base-change item: geometric notions are studied after replacing the coordinate Hopf algebra
`H` by `K ⊗[k] H`, and the functor of points of this base-changed object is identified with
the original points evaluated on `K`-algebras.

## Main declarations

* `FiniteTypeCommHopfAlgCat.baseChange`: the bundled finite-type Hopf `K`-algebra
  `K ⊗[k] H`.
* `FiniteTypeCommHopfAlgCat.baseChangeMap`: scalar extension of a coordinate morphism.
* `FiniteTypeCommHopfAlgCat.baseChangeFunctor`: functorial base change.
* `FiniteTypeCommHopfAlgCat.baseChangeTensorProductIso`: the canonical comparison between the
  base change of a tensor product and the tensor product of the base changes.
* `FiniteTypeCommHopfAlgCat.baseChangeIsoOfObjIso`: lift an isomorphism between specified
  underlying base-changed objects to the finite-type full subcategory.
* `FiniteTypeCommHopfAlgCat.baseChangePointsMulEquiv`: the inherited point equivalence
  `(K ⊗[k] H →ₐ[K] A) ≃* (H →ₐ[k] A)`.

## References

This builds on `CommHopfAlgCat.baseChange` and `CommHopfAlgCat.baseChangeFunctor`, whose
point equivalence ultimately comes from Tau Ceti's unbundled
`AlgHom.baseChangePointsMulEquiv`, plus Mathlib's `Algebra.FiniteType.baseChange`.
-/

public section

open CategoryTheory TensorProduct WithConv

namespace TauCeti

universe u v w x

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} {K : Type w} [CommRing k] [CommRing K] [Algebra k K]

/-- Base change of a finite-type commutative Hopf algebra along `k → K`.

The underlying coordinate Hopf algebra is `K ⊗[k] H`, with the tensor-product Hopf algebra
structure over `K`. -/
noncomputable abbrev baseChange (H : FiniteTypeCommHopfAlgCat.{u, v} k) :
    FiniteTypeCommHopfAlgCat.{w, max w v} K :=
  ⟨CommHopfAlgCat.baseChange (K := K) H.obj,
    inferInstanceAs (Algebra.FiniteType K (K ⊗[k] H))⟩

/-- Scalar extension of a morphism of finite-type commutative Hopf algebras. -/
noncomputable abbrev baseChangeMap {H L : FiniteTypeCommHopfAlgCat.{u, v} k}
    (φ : H ⟶ L) : baseChange (K := K) H ⟶ baseChange (K := K) L :=
  ObjectProperty.homMk (CommHopfAlgCat.baseChangeMap (K := K) φ.hom)

/-- The underlying bialgebra hom of `baseChangeMap` is tensoring the morphism with
the identity on the new base. -/
@[simp]
lemma toBialgHom_baseChangeMap {H L : FiniteTypeCommHopfAlgCat.{u, v} k}
    (φ : H ⟶ L) :
    toBialgHom (baseChangeMap (K := K) φ) =
      _root_.Bialgebra.TensorProduct.map (_root_.BialgHom.id K K) (toBialgHom φ) :=
  rfl

/-- On pure tensors, `baseChangeMap` applies the original morphism to the second factor. -/
lemma baseChangeMap_apply_tmul {H L : FiniteTypeCommHopfAlgCat.{u, v} k}
    (φ : H ⟶ L) (s : K) (h : H) :
    toBialgHom (baseChangeMap (K := K) φ) (s ⊗ₜ[k] h) = s ⊗ₜ[k] toBialgHom φ h :=
  CommHopfAlgCat.baseChangeMap_apply_tmul (K := K) φ.hom s h

/-- Base change is functorial on finite-type commutative Hopf algebras. -/
noncomputable abbrev baseChangeFunctor :
    FiniteTypeCommHopfAlgCat.{u, v} k ⥤ FiniteTypeCommHopfAlgCat.{w, max w v} K where
  obj H := baseChange (K := K) H
  map φ := baseChangeMap (K := K) φ
  map_id H := by
    apply hom_ext
    exact congrArg _root_.CommHopfAlgCat.Hom.hom
      ((CommHopfAlgCat.baseChangeFunctor (K := K)).map_id H.obj)
  map_comp φ ψ := by
    apply hom_ext
    exact congrArg _root_.CommHopfAlgCat.Hom.hom
      ((CommHopfAlgCat.baseChangeFunctor (K := K)).map_comp φ.hom ψ.hom)

/-- The object part of `baseChangeFunctor` is the bundled base-change object. -/
@[simp]
lemma baseChangeFunctor_obj (H : FiniteTypeCommHopfAlgCat.{u, v} k) :
    (baseChangeFunctor (K := K)).obj H = baseChange (K := K) H :=
  (rfl)

/-- The morphism part of `baseChangeFunctor` is scalar extension of coordinate morphisms. -/
@[simp]
lemma baseChangeFunctor_map {H L : FiniteTypeCommHopfAlgCat.{u, v} k} (φ : H ⟶ L) :
    (baseChangeFunctor (K := K)).map φ = baseChangeMap (K := K) φ :=
  (rfl)

/-- **Base change commutes with finite-type affine-group products.**

This is `Bialgebra.TensorProduct.baseChangeTensorBialgEquiv` bundled as an isomorphism in the
finite-type commutative Hopf-algebra category. -/
noncomputable def baseChangeTensorProductIso
    (K : Type w) [CommRing K] [Algebra k K]
    (H L : FiniteTypeCommHopfAlgCat.{u, v} k) :
    baseChange (K := K) (tensorProduct H L) ≅
      tensorProduct (baseChange (K := K) H) (baseChange (K := K) L) :=
  ObjectProperty.isoMk _ <| _root_.CommHopfAlgCat.isoMk <|
    Bialgebra.TensorProduct.baseChangeTensorBialgEquiv k K H L

/-- The underlying bialgebra equivalence of the finite-type product/base-change isomorphism is
the canonical tensor-product comparison. -/
@[simp]
theorem toBialgHom_baseChangeTensorProductIso_hom
    (K : Type w) [CommRing K] [Algebra k K]
    (H L : FiniteTypeCommHopfAlgCat.{u, v} k) :
    toBialgHom (baseChangeTensorProductIso K H L).hom =
      Bialgebra.TensorProduct.baseChangeTensorBialgEquiv k K H L := by
  simp only [baseChangeTensorProductIso, ObjectProperty.isoMk_hom,
    _root_.CommHopfAlgCat.isoMk_hom, toBialgHom_ofHom]

/-- The underlying bialgebra equivalence of the inverse finite-type product/base-change
isomorphism is the inverse canonical tensor-product comparison. -/
@[simp]
theorem toBialgHom_baseChangeTensorProductIso_inv
    (K : Type w) [CommRing K] [Algebra k K]
    (H L : FiniteTypeCommHopfAlgCat.{u, v} k) :
    toBialgHom (baseChangeTensorProductIso K H L).inv =
      (Bialgebra.TensorProduct.baseChangeTensorBialgEquiv k K H L).symm := by
  simp only [baseChangeTensorProductIso, ObjectProperty.isoMk_inv,
    _root_.CommHopfAlgCat.isoMk_inv, toBialgHom_ofHom]

/-- The product/base-change isomorphism carries the base change of the left coordinate inclusion
to the left coordinate inclusion between the base-changed factors. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_includeLeft_comp_baseChangeTensorProductIso_hom
    (K : Type w) [CommRing K] [Algebra k K]
    (H L : FiniteTypeCommHopfAlgCat.{u, v} k) :
    baseChangeMap (K := K) (includeLeft H L) ≫
        (baseChangeTensorProductIso K H L).hom =
      includeLeft (baseChange (K := K) H) (baseChange (K := K) L) := by
  apply hom_ext
  rw [toBialgHom_comp]
  apply _root_.BialgHom.coe_toAlgHom_injective
  apply Algebra.TensorProduct.ext'
  intro s h
  simp only [_root_.BialgHom.coe_toAlgHom, _root_.BialgHom.comp_apply]
  rw [baseChangeMap_apply_tmul, includeLeft_apply,
    toBialgHom_baseChangeTensorProductIso_hom]
  -- The underlying-map lemma has removed the categorical wrapper; expose its function coercion.
  change Bialgebra.TensorProduct.baseChangeTensorBialgEquiv k K H L
      (s ⊗ₜ[k] (h ⊗ₜ[k] (1 : L))) = _
  rw [Bialgebra.TensorProduct.baseChangeTensorBialgEquiv_tmul]
  rw [includeLeft_apply, Algebra.TensorProduct.one_def]

/-- The product/base-change isomorphism carries the base change of the right coordinate inclusion
to the right coordinate inclusion between the base-changed factors. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_includeRight_comp_baseChangeTensorProductIso_hom
    (K : Type w) [CommRing K] [Algebra k K]
    (H L : FiniteTypeCommHopfAlgCat.{u, v} k) :
    baseChangeMap (K := K) (includeRight H L) ≫
        (baseChangeTensorProductIso K H L).hom =
      includeRight (baseChange (K := K) H) (baseChange (K := K) L) := by
  apply hom_ext
  rw [toBialgHom_comp]
  apply _root_.BialgHom.coe_toAlgHom_injective
  apply Algebra.TensorProduct.ext'
  intro s l
  simp only [_root_.BialgHom.coe_toAlgHom, _root_.BialgHom.comp_apply]
  rw [baseChangeMap_apply_tmul, includeRight_apply,
    toBialgHom_baseChangeTensorProductIso_hom]
  -- The underlying-map lemma has removed the categorical wrapper; expose its function coercion.
  change Bialgebra.TensorProduct.baseChangeTensorBialgEquiv k K H L
      (s ⊗ₜ[k] ((1 : H) ⊗ₜ[k] l)) = _
  rw [Bialgebra.TensorProduct.baseChangeTensorBialgEquiv_tmul]
  rw [includeRight_apply, Algebra.TensorProduct.one_def]
  have hsH : s ⊗ₜ[k] (1 : H) = s • ((1 : K) ⊗ₜ[k] (1 : H)) :=
    TensorProduct.tmul_eq_smul_one_tmul s (1 : H)
  have hsL : s ⊗ₜ[k] l = s • ((1 : K) ⊗ₜ[k] l) :=
    TensorProduct.tmul_eq_smul_one_tmul s l
  rw [hsH, hsL]
  exact TensorProduct.smul_tmul s ((1 : K) ⊗ₜ[k] (1 : H)) ((1 : K) ⊗ₜ[k] l)

/-- Lift an isomorphism between specified underlying base-changed Hopf algebras to the
finite-type full subcategory. The object equalities record the chosen presentations of the
source and target coordinate Hopf algebras. -/
noncomputable def baseChangeIsoOfObjIso
    {H : FiniteTypeCommHopfAlgCat.{u, v} k}
    {H' : FiniteTypeCommHopfAlgCat.{w, max w v} K}
    {B : _root_.CommHopfAlgCat.{v} k} {B' : _root_.CommHopfAlgCat.{max w v} K}
    (hH : H.obj = B) (hH' : H'.obj = B')
    (e : CommHopfAlgCat.baseChange (K := K) B ≅ B') :
    baseChange (K := K) H ≅ H' :=
  ObjectProperty.isoMk _ <|
    eqToIso (congrArg (CommHopfAlgCat.baseChange (K := K)) hH) ≪≫ e ≪≫ eqToIso hH'.symm

/-- The underlying morphism of `baseChangeIsoOfObjIso` is the supplied isomorphism, conjugated
by the specified object equalities. -/
@[simp]
theorem baseChangeIsoOfObjIso_hom
    {H : FiniteTypeCommHopfAlgCat.{u, v} k}
    {H' : FiniteTypeCommHopfAlgCat.{w, max w v} K}
    {B : _root_.CommHopfAlgCat.{v} k} {B' : _root_.CommHopfAlgCat.{max w v} K}
    (hH : H.obj = B) (hH' : H'.obj = B')
    (e : CommHopfAlgCat.baseChange (K := K) B ≅ B') :
    (baseChangeIsoOfObjIso hH hH' e).hom.hom =
      (eqToIso (congrArg (CommHopfAlgCat.baseChange (K := K)) hH) ≪≫ e ≪≫
        eqToIso hH'.symm).hom := by
  simp only [baseChangeIsoOfObjIso, ObjectProperty.isoMk_hom, ObjectProperty.homMk_hom]

variable (A : CommAlgCat.{x} K)

/-- The points of the base-changed finite-type Hopf algebra are the original points evaluated
on the same algebra, with scalars restricted from `K` to `k`. -/
noncomputable def baseChangePointsMulEquiv (H : FiniteTypeCommHopfAlgCat.{u, v} k) :
    HopfAlgebra.points (R := K) (H := baseChange (K := K) H) A ≃*
      HopfAlgebra.points (R := k) (H := H)
        (_root_.TauCeti.CommAlgCat.restrictScalarsObj (algebraMap k K) A) :=
  CommHopfAlgCat.baseChangePointsMulEquiv (K := K) A H.obj

/-- Applying the base-change points equivalence restricts a `K`-point along `h ↦ 1 ⊗ h`. -/
@[simp]
lemma baseChangePointsMulEquiv_apply_apply (H : FiniteTypeCommHopfAlgCat.{u, v} k)
    (f : HopfAlgebra.points (R := K) (H := baseChange (K := K) H) A) (h : H) :
    (baseChangePointsMulEquiv (K := K) A H f).ofConv h = f.ofConv (1 ⊗ₜ[k] h) :=
  CommHopfAlgCat.baseChangePointsMulEquiv_apply_apply (K := K) A H.obj f h

/-- The inverse base-change points equivalence sends a restricted point to
`s ⊗ h ↦ s • f h`. -/
@[simp]
lemma baseChangePointsMulEquiv_symm_apply_tmul
    (H : FiniteTypeCommHopfAlgCat.{u, v} k)
    (f : HopfAlgebra.points (R := k) (H := H)
      (_root_.TauCeti.CommAlgCat.restrictScalarsObj (algebraMap k K) A))
    (s : K) (h : H) :
    ((baseChangePointsMulEquiv (K := K) A H).symm f).ofConv (s ⊗ₜ[k] h) = s • f.ofConv h :=
  CommHopfAlgCat.baseChangePointsMulEquiv_symm_apply_tmul (K := K) A H.obj f s h

variable {A}

/-- The base-change points equivalence is natural in the value algebra. -/
lemma baseChangePointsMulEquiv_mapValue
    {B : CommAlgCat.{x} K} (H : FiniteTypeCommHopfAlgCat.{u, v} k)
    (χ : A ⟶ B) (f : HopfAlgebra.points (R := K) (H := baseChange (K := K) H) A) :
    baseChangePointsMulEquiv (K := K) B H (HopfAlgebra.mapPoints (H := baseChange (K := K) H) χ f) =
      HopfAlgebra.mapPoints (H := H)
        ((_root_.TauCeti.CommAlgCat.restrictScalars (algebraMap k K)).map χ)
        (baseChangePointsMulEquiv (K := K) A H f) :=
  CommHopfAlgCat.baseChangePointsMulEquiv_mapValue (K := K) H.obj χ f

/-- The base-change points equivalence is natural in the coordinate Hopf algebra. -/
lemma baseChangePointsMulEquiv_mapDomain {H L : FiniteTypeCommHopfAlgCat.{u, v} k}
    (φ : H ⟶ L) (f : HopfAlgebra.points (R := K) (H := baseChange (K := K) L) A) :
    baseChangePointsMulEquiv (K := K) A H
        (AlgHom.mapDomain (A := A) (toBialgHom (baseChangeMap (K := K) φ)) f) =
      AlgHom.mapDomain
        (A := _root_.TauCeti.CommAlgCat.restrictScalarsObj (algebraMap k K) A)
        (toBialgHom φ)
        (baseChangePointsMulEquiv (K := K) A L f) :=
  CommHopfAlgCat.baseChangePointsMulEquiv_mapDomain (K := K) φ.hom f

end FiniteTypeCommHopfAlgCat

end TauCeti
