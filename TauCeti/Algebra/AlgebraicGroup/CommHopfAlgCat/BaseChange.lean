/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.LinearAlgebra.TensorProduct.RightExactness

public import TauCeti.Algebra.AlgebraicGroup.BaseChange.Naturality
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Basic
public import TauCeti.Algebra.Category.CommAlgCat.RestrictScalars

/-!
# Base change of commutative Hopf algebras

This file packages the scalar extension `K ⊗[k] H` of a commutative Hopf `k`-algebra as a
commutative Hopf `K`-algebra, functorially in the bundled commutative Hopf algebra. It also
records the corresponding base-change equivalence on functors of points.

It is the bundled Hopf-algebra base-change layer for the ReductiveGroups roadmap Layer 0
base-change item: geometric notions are studied after replacing the coordinate Hopf algebra
`H` by `K ⊗[k] H`, and the functor of points of this base-changed object is identified with
the original points evaluated on `K`-algebras.

## Main declarations

* `CommHopfAlgCat.baseChange`: the bundled Hopf `K`-algebra `K ⊗[k] H`.
* `CommHopfAlgCat.baseChangeMap`: scalar extension of a coordinate morphism.
* `CommHopfAlgCat.baseChangeMap_surjective`: base change preserves surjectivity.
* `CommHopfAlgCat.baseChangeFunctor`: functorial base change on commutative Hopf algebras.
* `CommHopfAlgCat.baseChangePointsMulEquiv`: the inherited point equivalence
  `(K ⊗[k] H →ₐ[K] A) ≃* (H →ₐ[k] A)`.
* `CommHopfAlgCat.baseChangeIsoPointsMulEquiv`: the same equivalence for a Hopf `K`-algebra
  presented as a scalar extension by an isomorphism `L ≅ K ⊗[k] H`.

## References

This builds on Tau Ceti's unbundled base-change equivalence
`AlgHom.baseChangePointsMulEquiv` and its naturality lemmas, plus Mathlib's
`Bialgebra.TensorProduct.map`.
-/

public section

open CategoryTheory TensorProduct WithConv

namespace TauCeti

universe u v w x

namespace CommHopfAlgCat

variable {k : Type u} {K : Type w} [CommRing k] [CommRing K] [Algebra k K]

/-- Base change of a commutative Hopf algebra along `k → K`.

The underlying coordinate Hopf algebra is `K ⊗[k] H`, with the tensor-product Hopf algebra
structure over `K`. -/
noncomputable abbrev baseChange (H : _root_.CommHopfAlgCat.{v} k) :
    _root_.CommHopfAlgCat.{max w v} K :=
  _root_.CommHopfAlgCat.of K (K ⊗[k] H)

/-- Scalar extension of a morphism of commutative Hopf algebras. -/
noncomputable abbrev baseChangeMap {H L : _root_.CommHopfAlgCat.{v} k}
    (φ : H ⟶ L) : baseChange (K := K) H ⟶ baseChange (K := K) L :=
  _root_.CommHopfAlgCat.ofHom
    (_root_.Bialgebra.TensorProduct.map (_root_.BialgHom.id K K) φ.hom)

/-- The underlying bialgebra hom of `baseChangeMap` is tensoring the morphism with
the identity on the new base. -/
@[simp]
lemma hom_baseChangeMap {H L : _root_.CommHopfAlgCat.{v} k}
    (φ : H ⟶ L) :
    (baseChangeMap (K := K) φ).hom =
      _root_.Bialgebra.TensorProduct.map (_root_.BialgHom.id K K) φ.hom :=
  rfl

/-- On pure tensors, `baseChangeMap` applies the original morphism to the second factor. -/
lemma baseChangeMap_apply_tmul {H L : _root_.CommHopfAlgCat.{v} k}
    (φ : H ⟶ L) (s : K) (h : H) :
    (baseChangeMap (K := K) φ).hom (s ⊗ₜ[k] h) = s ⊗ₜ[k] φ.hom h := by
  rw [hom_baseChangeMap, _root_.Bialgebra.TensorProduct.map_tmul,
    _root_.BialgHom.id_apply]

/-- Base change along `k → K` preserves surjectivity of a morphism of commutative Hopf
algebras. -/
theorem baseChangeMap_surjective {H L : _root_.CommHopfAlgCat.{v} k}
    (φ : H ⟶ L) (hφ : Function.Surjective φ.hom) :
    Function.Surjective (baseChangeMap (K := K) φ).hom := by
  rw [hom_baseChangeMap]
  exact Algebra.TensorProduct.map_surjective (AlgHom.id k K) φ.hom.toAlgHom
    Function.surjective_id hφ

/-- Base change is functorial on commutative Hopf algebras. -/
noncomputable abbrev baseChangeFunctor :
    _root_.CommHopfAlgCat.{v} k ⥤ _root_.CommHopfAlgCat.{max w v} K where
  obj H := baseChange (K := K) H
  map φ := baseChangeMap (K := K) φ
  map_id H := by
    apply _root_.CommHopfAlgCat.hom_ext
    apply _root_.BialgHom.ext
    intro x
    have hAlg :
        ((baseChangeMap (K := K) (𝟙 H)).hom).toAlgHom =
          ((𝟙 (baseChange (K := K) H) : baseChange (K := K) H ⟶
            baseChange (K := K) H).hom).toAlgHom := by
      apply Algebra.TensorProduct.ext'
      intro s h
      simp
    exact AlgHom.congr_fun hAlg x
  map_comp φ ψ := by
    apply _root_.CommHopfAlgCat.hom_ext
    apply _root_.BialgHom.ext
    intro x
    have hAlg :
        ((baseChangeMap (K := K) (φ ≫ ψ)).hom).toAlgHom =
          (((baseChangeMap (K := K) φ ≫ baseChangeMap (K := K) ψ) :
            baseChange (K := K) _ ⟶ baseChange (K := K) _).hom).toAlgHom := by
      apply Algebra.TensorProduct.ext'
      intro s h
      simp
    exact AlgHom.congr_fun hAlg x

/-- The object part of `baseChangeFunctor` is the bundled base-change object. -/
@[simp]
lemma baseChangeFunctor_obj (H : _root_.CommHopfAlgCat.{v} k) :
    (baseChangeFunctor (K := K)).obj H = baseChange (K := K) H :=
  (rfl)

/-- The morphism part of `baseChangeFunctor` is scalar extension of coordinate morphisms. -/
@[simp]
lemma baseChangeFunctor_map {H L : _root_.CommHopfAlgCat.{v} k} (φ : H ⟶ L) :
    (baseChangeFunctor (K := K)).map φ = baseChangeMap (K := K) φ :=
  (rfl)

variable (A : CommAlgCat.{x} K)

/-- The points of the base-changed Hopf algebra are the original points evaluated
on the same algebra, with scalars restricted from `K` to `k`. -/
noncomputable def baseChangePointsMulEquiv (H : _root_.CommHopfAlgCat.{v} k) :
    HopfAlgebra.points (R := K) (H := baseChange (K := K) H) A ≃*
      HopfAlgebra.points (R := k) (H := H)
        (_root_.TauCeti.CommAlgCat.restrictScalarsObj (algebraMap k K) A) :=
  letI : Algebra k A := Algebra.compHom A (algebraMap k K)
  letI : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  (AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := H) (R := A)).symm

/-- Applying the base-change points equivalence restricts a `K`-point along `h ↦ 1 ⊗ h`. -/
@[simp]
lemma baseChangePointsMulEquiv_apply_apply (H : _root_.CommHopfAlgCat.{v} k)
    (f : HopfAlgebra.points (R := K) (H := baseChange (K := K) H) A) (h : H) :
    (baseChangePointsMulEquiv (K := K) A H f).ofConv h = f.ofConv (1 ⊗ₜ[k] h) :=
  letI : Algebra k A := Algebra.compHom A (algebraMap k K)
  letI : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  AlgHom.baseChangePointsMulEquiv_symm_apply f h

/-- The inverse base-change points equivalence sends a restricted point to
`s ⊗ h ↦ s • f h`. -/
@[simp]
lemma baseChangePointsMulEquiv_symm_apply_tmul
    (H : _root_.CommHopfAlgCat.{v} k)
    (f : HopfAlgebra.points (R := k) (H := H)
      (_root_.TauCeti.CommAlgCat.restrictScalarsObj (algebraMap k K) A))
    (s : K) (h : H) :
    ((baseChangePointsMulEquiv (K := K) A H).symm f).ofConv (s ⊗ₜ[k] h) = s • f.ofConv h :=
  letI : Algebra k A := Algebra.compHom A (algebraMap k K)
  letI : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  AlgHom.baseChangePointsMulEquiv_apply_tmul f s h

variable {A}

/-- The base-change points equivalence is natural in the value algebra. -/
lemma baseChangePointsMulEquiv_mapValue
    {B : CommAlgCat.{x} K} (H : _root_.CommHopfAlgCat.{v} k)
    (χ : A ⟶ B) (f : HopfAlgebra.points (R := K) (H := baseChange (K := K) H) A) :
    baseChangePointsMulEquiv (K := K) B H (HopfAlgebra.mapPoints (H := baseChange (K := K) H) χ f) =
      HopfAlgebra.mapPoints (H := H)
        ((_root_.TauCeti.CommAlgCat.restrictScalars (algebraMap k K)).map χ)
      (baseChangePointsMulEquiv (K := K) A H f) := by
  let : Algebra k A := Algebra.compHom A (algebraMap k K)
  let : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra k B := Algebra.compHom B (algebraMap k K)
  let : IsScalarTower k K B := IsScalarTower.of_algebraMap_eq' rfl
  rw [_root_.TauCeti.CommAlgCat.restrictScalars_map]
  -- `HopfAlgebra.mapPoints` is definitionally the multiplicative map induced by
  -- `AlgHom.mapValue`; after rewriting the restricted categorical map, `change` exposes
  -- that underlying `AlgHom.mapValue` statement.
  change baseChangePointsMulEquiv (K := K) B H
      (HopfAlgebra.mapPoints (H := baseChange (K := K) H) χ f) =
    AlgHom.mapValue (H := H) (χ.hom.restrictScalars k)
      (baseChangePointsMulEquiv (K := K) A H f)
  simpa [baseChangePointsMulEquiv, HopfAlgebra.mapPoints,
    _root_.TauCeti.CommAlgCat.restrictScalarsMap, AlgHom.mapValue_apply]
    using AlgHom.baseChangePointsMulEquiv_symm_mapValue (k := k) (K := K) (A := H)
      (R := A) (S := B) χ.hom f

/-- The base-change points equivalence is natural in the coordinate Hopf algebra. -/
lemma baseChangePointsMulEquiv_mapDomain {H L : _root_.CommHopfAlgCat.{v} k}
    (φ : H ⟶ L) (f : HopfAlgebra.points (R := K) (H := baseChange (K := K) L) A) :
    baseChangePointsMulEquiv (K := K) A H
        (AlgHom.mapDomain (A := A) ((baseChangeMap (K := K) φ).hom) f) =
      AlgHom.mapDomain
        (A := _root_.TauCeti.CommAlgCat.restrictScalarsObj (algebraMap k K) A)
        φ.hom
        (baseChangePointsMulEquiv (K := K) A L f) := by
  let : Algebra k A := Algebra.compHom A (algebraMap k K)
  let : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  simpa [baseChangePointsMulEquiv, hom_baseChangeMap]
    using AlgHom.baseChangePointsMulEquiv_symm_mapDomain (k := k) (K := K)
      (A := H) (B := L) (R := A) φ.hom f

variable {H : _root_.CommHopfAlgCat.{v} k} {L : _root_.CommHopfAlgCat.{max w v} K}

/-- **The points of a commutative Hopf `K`-algebra presented as a scalar extension.** An
isomorphism `e : L ≅ K ⊗[k] H` identifies the points of `L` on a value algebra `A` with the
points of `H` on `A` with its scalars restricted to `k`; the carrier `L` need not be the tensor
product itself. This is `baseChangePointsMulEquiv` preceded by transport along `e`. -/
noncomputable def baseChangeIsoPointsMulEquiv (e : L ≅ baseChange (K := K) H)
    (A : CommAlgCat.{x} K) :
    HopfAlgebra.points (R := K) (H := L) A ≃*
      HopfAlgebra.points (R := k) (H := H)
        (_root_.TauCeti.CommAlgCat.restrictScalarsObj (algebraMap k K) A) :=
  (AlgHom.mapDomainMulEquiv (A := A) (_root_.CommHopfAlgCat.ofIso e.symm)).trans
    (baseChangePointsMulEquiv (K := K) A H)

/-- The presented point equivalence evaluates a point of `L` at the image of `1 ⊗ h` under the
presenting isomorphism. -/
@[simp]
lemma baseChangeIsoPointsMulEquiv_apply_apply (e : L ≅ baseChange (K := K) H)
    (A : CommAlgCat.{x} K) (f : HopfAlgebra.points (R := K) (H := L) A) (h : H) :
    (baseChangeIsoPointsMulEquiv e A f).ofConv h = f.ofConv (e.inv (1 ⊗ₜ[k] h)) := by
  rw [baseChangeIsoPointsMulEquiv, MulEquiv.trans_apply, baseChangePointsMulEquiv_apply_apply,
    AlgHom.mapDomainMulEquiv_apply, AlgHom.mapDomain_apply_apply]
  exact congrArg f.ofConv (_root_.CommHopfAlgCat.ofIso_apply e.symm _)

/-- The presented point equivalence is natural in the value algebra. -/
lemma baseChangeIsoPointsMulEquiv_mapPoints (e : L ≅ baseChange (K := K) H)
    {A B : CommAlgCat.{x} K} (χ : A ⟶ B)
    (f : HopfAlgebra.points (R := K) (H := L) A) :
    baseChangeIsoPointsMulEquiv e B (HopfAlgebra.mapPoints (H := L) χ f) =
      HopfAlgebra.mapPoints (H := H)
        ((_root_.TauCeti.CommAlgCat.restrictScalars (algebraMap k K)).map χ)
        (baseChangeIsoPointsMulEquiv e A f) := by
  -- Transport along `e` is a pre-composition in the coordinate Hopf algebra, so it commutes with
  -- the post-composition by `χ` in the value algebra. The bundled `mapDomainMulEquiv` and
  -- `mapPoints` are unfolded to `mapDomain` and `mapValue` to reach `mapValue_mapDomain`.
  have h : AlgHom.mapDomainMulEquiv (A := B) (_root_.CommHopfAlgCat.ofIso e.symm)
        (HopfAlgebra.mapPoints (H := L) χ f) =
      HopfAlgebra.mapPoints (H := baseChange (K := K) H) χ
        (AlgHom.mapDomainMulEquiv (A := A) (_root_.CommHopfAlgCat.ofIso e.symm) f) := by
    simp only [AlgHom.mapDomainMulEquiv_apply, HopfAlgebra.mapPoints]
    exact DFunLike.congr_fun
      (AlgHom.mapValue_mapDomain (_root_.CommHopfAlgCat.ofIso e.symm).toBialgHom χ.hom) f
  simp only [baseChangeIsoPointsMulEquiv, MulEquiv.trans_apply, h]
  rw [baseChangePointsMulEquiv_mapValue]

end CommHopfAlgCat

end TauCeti
