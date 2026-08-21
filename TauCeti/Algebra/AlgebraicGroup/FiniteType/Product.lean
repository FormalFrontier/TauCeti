/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteStability
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Product

/-!
# Products of finite-type commutative Hopf algebras

This file packages the tensor product of two finite-type commutative Hopf algebras as another
object of `FiniteTypeCommHopfAlgCat`. On affine group schemes this is the coordinate algebra
of the direct product. The Hopf-algebra structure is Mathlib's tensor-product Hopf algebra;
the finite-type input is Mathlib's stability of finite type under base change, followed by
transitivity of finite type along `R → H₁ → H₁ ⊗[R] H₂`.

The coordinate inclusions `H₁ → H₁ ⊗[R] H₂` and `H₂ → H₁ ⊗[R] H₂` are also bundled as
morphisms in `FiniteTypeCommHopfAlgCat`. The points of the finite-type product are identified
with pairs of points by the existing product-points equivalence from
`TauCeti.Algebra.AlgebraicGroup.Product`.

This is a finite-type wrapper for the ReductiveGroups roadmap Layer 0 product/functor-of-points
infrastructure: affine group schemes of finite type should remain finite type under products.
-/

public section

open CategoryTheory TensorProduct WithConv

namespace TauCeti

universe u v w

namespace FiniteTypeCommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- The tensor product of two finite-type commutative algebras is finite type over the base. -/
theorem tensorProduct_finiteType (A B : Type v) [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FiniteType R A] [Algebra.FiniteType R B] :
    Algebra.FiniteType R (A ⊗[R] B) :=
  Algebra.FiniteType.trans (R := R) (S := A) (A := A ⊗[R] B) inferInstance inferInstance

/-- The tensor product of two finite-type commutative Hopf algebras, bundled as a finite-type
commutative Hopf algebra.

Contravariantly, this is the coordinate-Hopf-algebra model for the product of the represented
affine group schemes. -/
noncomputable abbrev tensorProduct (H K : FiniteTypeCommHopfAlgCat.{u, v} R) :
    FiniteTypeCommHopfAlgCat.{u, v} R :=
  letI : Algebra.FiniteType R (H ⊗[R] K) := tensorProduct_finiteType (R := R) H K
  of R (H ⊗[R] K)

/-- The left coordinate inclusion `H → H ⊗[R] K`, bundled in the finite-type commutative
Hopf-algebra category. On points this is the first projection from product points. -/
noncomputable abbrev includeLeft (H K : FiniteTypeCommHopfAlgCat.{u, v} R) :
    H ⟶ tensorProduct H K :=
  letI : Algebra.FiniteType R (H ⊗[R] K) := tensorProduct_finiteType (R := R) H K
  ofHom (Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H) (H₂ := K))

/-- The right coordinate inclusion `K → H ⊗[R] K`, bundled in the finite-type commutative
Hopf-algebra category. On points this is the second projection from product points. -/
noncomputable abbrev includeRight (H K : FiniteTypeCommHopfAlgCat.{u, v} R) :
    K ⟶ tensorProduct H K :=
  letI : Algebra.FiniteType R (H ⊗[R] K) := tensorProduct_finiteType (R := R) H K
  ofHom (Bialgebra.TensorProduct.includeRight (R := R) (H₁ := H) (H₂ := K))

variable (A : CommAlgCat.{w} R)

/-- The product-points equivalence for the finite-type tensor-product object. -/
noncomputable def pointsMulEquiv (H K : FiniteTypeCommHopfAlgCat.{u, v} R) :
    HopfAlgebra.points (R := R) (H := tensorProduct H K) A ≃*
      HopfAlgebra.points (R := R) (H := H) A × HopfAlgebra.points (R := R) (H := K) A :=
  AffineGroup.Product.pointsMulEquiv (R := R) (H₁ := H) (H₂ := K) (A := A)

/-- The first component of `pointsMulEquiv` is induced by the left coordinate inclusion. -/
@[simp]
theorem pointsMulEquiv_fst
    (H K : FiniteTypeCommHopfAlgCat.{u, v} R)
    (f : HopfAlgebra.points (R := R) (H := tensorProduct H K) A) :
    (pointsMulEquiv A H K f).1 =
      (((pointsFunctor (R := R)).map (includeLeft H K).op).app A f) := by
  apply WithConv.ofConv_injective
  ext h
  rw [pointsMulEquiv]
  exact (pointsFunctor_map_app_apply_apply (R := R) (φ := (includeLeft H K).op) A f h).symm

/-- The second component of `pointsMulEquiv` is induced by the right coordinate inclusion. -/
@[simp]
theorem pointsMulEquiv_snd
    (H K : FiniteTypeCommHopfAlgCat.{u, v} R)
    (f : HopfAlgebra.points (R := R) (H := tensorProduct H K) A) :
    (pointsMulEquiv A H K f).2 =
      (((pointsFunctor (R := R)).map (includeRight H K).op).app A f) := by
  apply WithConv.ofConv_injective
  ext k
  rw [pointsMulEquiv]
  exact (pointsFunctor_map_app_apply_apply (R := R) (φ := (includeRight H K).op) A f k).symm

/-- The inverse of `pointsMulEquiv` is Mathlib's tensor-product product map. -/
@[simp]
theorem pointsMulEquiv_symm_apply (H K : FiniteTypeCommHopfAlgCat.{u, v} R)
    (p : HopfAlgebra.points (R := R) (H := H) A × HopfAlgebra.points (R := R) (H := K) A) :
    (pointsMulEquiv A H K).symm p =
      toConv (Algebra.TensorProduct.productMap p.1.ofConv p.2.ofConv) :=
  AffineGroup.Product.pointsMulEquiv_symm_apply (R := R) (H₁ := H) (H₂ := K) (A := A) p

variable {B : CommAlgCat.{w} R}

/-- The product-points equivalence is natural in the value algebra: post-composing a point of
the product by `φ`, then splitting it into its two factor points, agrees with splitting first
and then post-composing each factor point by `φ`. -/
theorem pointsMulEquiv_mapValue (H K : FiniteTypeCommHopfAlgCat.{u, v} R) (φ : A →ₐ[R] B)
    (f : HopfAlgebra.points (R := R) (H := tensorProduct H K) A) :
    pointsMulEquiv B H K (AlgHom.mapValue (H := tensorProduct H K) φ f) =
      (AlgHom.mapValue (H := H) φ (pointsMulEquiv A H K f).1,
        AlgHom.mapValue (H := K) φ (pointsMulEquiv A H K f).2) :=
  AffineGroup.Product.pointsMulEquiv_mapValue (R := R) (H₁ := H) (H₂ := K) φ f

/-- First-component form of `pointsMulEquiv_mapValue`. -/
theorem pointsMulEquiv_mapValue_fst (H K : FiniteTypeCommHopfAlgCat.{u, v} R) (φ : A →ₐ[R] B)
    (f : HopfAlgebra.points (R := R) (H := tensorProduct H K) A) :
    (pointsMulEquiv B H K (AlgHom.mapValue (H := tensorProduct H K) φ f)).1 =
      AlgHom.mapValue (H := H) φ (pointsMulEquiv A H K f).1 :=
  AffineGroup.Product.pointsMulEquiv_mapValue_fst (R := R) (H₁ := H) (H₂ := K) φ f

/-- Second-component form of `pointsMulEquiv_mapValue`. -/
theorem pointsMulEquiv_mapValue_snd (H K : FiniteTypeCommHopfAlgCat.{u, v} R) (φ : A →ₐ[R] B)
    (f : HopfAlgebra.points (R := R) (H := tensorProduct H K) A) :
    (pointsMulEquiv B H K (AlgHom.mapValue (H := tensorProduct H K) φ f)).2 =
      AlgHom.mapValue (H := K) φ (pointsMulEquiv A H K f).2 :=
  AffineGroup.Product.pointsMulEquiv_mapValue_snd (R := R) (H₁ := H) (H₂ := K) φ f

/-- The inverse product-points map is natural in the value algebra: assembling an `A`-valued
product point from a pair of factor points and post-composing by `φ` is the same as
post-composing both factor points by `φ` and then assembling the resulting `B`-valued point. -/
theorem mapValue_pointsMulEquiv_symm_apply (H K : FiniteTypeCommHopfAlgCat.{u, v} R)
    (φ : A →ₐ[R] B)
    (p : HopfAlgebra.points (R := R) (H := H) A × HopfAlgebra.points (R := R) (H := K) A) :
    AlgHom.mapValue (H := tensorProduct H K) φ ((pointsMulEquiv A H K).symm p) =
      (pointsMulEquiv B H K).symm
        (AlgHom.mapValue (H := H) φ p.1, AlgHom.mapValue (H := K) φ p.2) :=
  AffineGroup.Product.mapValue_pointsMulEquiv_symm_apply (R := R) (H₁ := H) (H₂ := K) φ p

/-- On pure tensors, naturality of the inverse product-points map evaluates post-composition by
`φ` as applying `φ` to the product of the two factor values. -/
theorem mapValue_pointsMulEquiv_symm_apply_tmul (H K : FiniteTypeCommHopfAlgCat.{u, v} R)
    (φ : A →ₐ[R] B)
    (p : HopfAlgebra.points (R := R) (H := H) A × HopfAlgebra.points (R := R) (H := K) A)
    (x : H) (y : K) :
    (AlgHom.mapValue (H := tensorProduct H K) φ ((pointsMulEquiv A H K).symm p)).ofConv
        (x ⊗ₜ[R] y) =
      φ (p.1.ofConv x * p.2.ofConv y) :=
  AffineGroup.Product.mapValue_pointsMulEquiv_symm_apply_tmul
    (R := R) (H₁ := H) (H₂ := K) φ p x y

/-- On pure tensors, assembling after post-composing both factor points by `φ` multiplies the
two post-composed factor values. -/
theorem pointsMulEquiv_symm_mapValue_apply_tmul (H K : FiniteTypeCommHopfAlgCat.{u, v} R)
    (φ : A →ₐ[R] B)
    (p : HopfAlgebra.points (R := R) (H := H) A × HopfAlgebra.points (R := R) (H := K) A)
    (x : H) (y : K) :
    ((pointsMulEquiv B H K).symm
        (AlgHom.mapValue (H := H) φ p.1, AlgHom.mapValue (H := K) φ p.2)).ofConv (x ⊗ₜ[R] y) =
      φ (p.1.ofConv x) * φ (p.2.ofConv y) :=
  AffineGroup.Product.pointsMulEquiv_symm_mapValue_apply_tmul
    (R := R) (H₁ := H) (H₂ := K) φ p x y

end FiniteTypeCommHopfAlgCat

end TauCeti
