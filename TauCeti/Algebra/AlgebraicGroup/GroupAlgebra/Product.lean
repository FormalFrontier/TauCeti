/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.Algebra.Bialgebra.MonoidAlgebraProduct
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.AlgebraicGroup.Product
public import TauCeti.Algebra.Bialgebra.TensorProduct

/-!
# The diagonalizable group of a product

This file records the functor-of-points consequence of
`TauCeti.MonoidAlgebra.prodTensorBialgEquiv`: for commutative monoids `G` and `H`, points of
`Spec R[G × H]` split as pairs of points of `Spec R[G]` and `Spec R[H]`. For commutative groups,
this specializes to the diagonalizable group statement
`D(G × H)(A) ≃* D(G)(A) × D(H)(A)`.

On points this composes with `TauCeti.AffineGroup.Product.pointsMulEquiv`, the tensor-product
points calculation, through the equiv-version `AlgHom.mapDomainMulEquiv` of the contravariant
functoriality `AlgHom.mapDomain`. When `G` and `H` are commutative groups the group algebras
are Hopf algebras and these convolution monoids are the convolution groups of points
(`TauCeti.AlgHom.instGroup`), so the points equivalence is automatically an isomorphism of
groups: `D(G × H)(A) ≅ D(G)(A) × D(H)(A)`.

This advances the reductive-groups roadmap (`ReductiveGroups/README.md` in TauCetiRoadmap,
Layer 4 "Diagonalizable groups" and the "Worked examples / products" theme, together with the
Layer 0 functor-of-points dictionary): this supplies the binary product step used in the
calculation of split tori as iterated products of `𝔾ₘ`.

## Main definitions

* `TauCeti.MonoidAlgebra.prodPointsMulEquiv`: on convolution points,
  `Spec R[G × H](A) ≃* Spec R[G](A) × Spec R[H](A)`.
* `TauCeti.DiagonalizableGroup.prodPointsMulEquiv`: for commutative groups, on points,
  `D(G × H)(A) ≃* D(G)(A) × D(H)(A)`.

## References

The tensor-product points calculation `TauCeti.AffineGroup.Product.pointsMulEquiv`, the generic
monoid-algebra bialgebra product `TauCeti.MonoidAlgebra.prodTensorBialgEquiv`, and the
contravariant functoriality `TauCeti.AlgHom.mapDomain` are Tau Ceti's existing
functor-of-points infrastructure, built on Mathlib's tensor-product and monoid-algebra
bialgebra structures and the Mathlib convolution monoid of Yaël Dillies, Michał Mrugała and
Yunzhou Xie.
-/

public section

open TensorProduct WithConv MonoidAlgebra

namespace TauCeti

universe u v w w'

variable {R : Type u} [CommSemiring R]
variable {G : Type v} {H : Type w} [CommMonoid G] [CommMonoid H]
variable {A : Type w'} [CommSemiring A] [Algebra R A]

namespace MonoidAlgebra

/-- **The monoid algebra of a product gives the product functor on convolution points.**
For commutative monoids `G` and `H` and every commutative `R`-algebra `A`, the convolution
monoid of `A`-points of `Spec R[G × H]` is the product of the convolution monoids of
`A`-points of `Spec R[G]` and `Spec R[H]`. -/
noncomputable def prodPointsMulEquiv :
    WithConv (MonoidAlgebra R (G × H) →ₐ[R] A) ≃*
      WithConv (MonoidAlgebra R G →ₐ[R] A) × WithConv (MonoidAlgebra R H →ₐ[R] A) :=
  (AlgHom.mapDomainMulEquiv (A := A) (MonoidAlgebra.prodTensorBialgEquiv R)).symm.trans
    AffineGroup.Product.pointsMulEquiv

/-- The first component of `prodPointsMulEquiv` restricts an `A`-point of `Spec R[G × H]` to
the factor `Spec R[G]`: on the generator `single g 1` it evaluates the original point at
`single (g, 1) 1`, the image of `g` under `G → G × H`. -/
@[simp]
theorem prodPointsMulEquiv_fst_ofConv_single
    (f : WithConv (MonoidAlgebra R (G × H) →ₐ[R] A)) (g : G) :
    (prodPointsMulEquiv f).1.ofConv (single g (1 : R)) =
      f.ofConv (single (g, (1 : H)) 1) := by
  rw [prodPointsMulEquiv, MulEquiv.trans_apply, AffineGroup.Product.pointsMulEquiv_apply,
    AlgHom.mapDomainMulEquiv_symm_apply]
  simp only [AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
    BialgHom.coe_toAlgHom, Bialgebra.TensorProduct.includeLeft_apply, BialgEquiv.coe_toBialgHom]
  rw [MonoidAlgebra.one_def, MonoidAlgebra.prodTensorBialgEquiv_symm_tmul_single]

/-- The second component of `prodPointsMulEquiv` restricts an `A`-point of `Spec R[G × H]` to
the factor `Spec R[H]`: on the generator `single h 1` it evaluates the original point at
`single (1, h) 1`, the image of `h` under `H → G × H`. -/
@[simp]
theorem prodPointsMulEquiv_snd_ofConv_single
    (f : WithConv (MonoidAlgebra R (G × H) →ₐ[R] A)) (h : H) :
    (prodPointsMulEquiv f).2.ofConv (single h (1 : R)) =
      f.ofConv (single ((1 : G), h) 1) := by
  rw [prodPointsMulEquiv, MulEquiv.trans_apply, AffineGroup.Product.pointsMulEquiv_apply,
    AlgHom.mapDomainMulEquiv_symm_apply]
  simp only [AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
    BialgHom.coe_toAlgHom, Bialgebra.TensorProduct.includeRight_apply, BialgEquiv.coe_toBialgHom]
  rw [MonoidAlgebra.one_def, MonoidAlgebra.prodTensorBialgEquiv_symm_tmul_single]

/-- The inverse of `prodPointsMulEquiv` assembles an `A`-point of `Spec R[G × H]` from a pair of
points of `Spec R[G]` and `Spec R[H]`: on the generator `single (g, h) 1` it multiplies the
value of the first point at `single g 1` and the value of the second at `single h 1`. -/
@[simp]
theorem prodPointsMulEquiv_symm_ofConv_single
    (f₁ : WithConv (MonoidAlgebra R G →ₐ[R] A)) (f₂ : WithConv (MonoidAlgebra R H →ₐ[R] A))
    (g : G) (h : H) :
    (prodPointsMulEquiv.symm (f₁, f₂)).ofConv (single (g, h) (1 : R)) =
      f₁.ofConv (single g 1) * f₂.ofConv (single h 1) := by
  rw [prodPointsMulEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_symm,
    AlgHom.mapDomainMulEquiv_apply]
  simp only [AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply, BialgHom.coe_toAlgHom,
    BialgEquiv.coe_toBialgHom, MonoidAlgebra.prodTensorBialgEquiv_single,
    AffineGroup.Product.pointsMulEquiv_symm_apply, Algebra.TensorProduct.productMap_apply_tmul]

variable {B : Type*} [CommSemiring B] [Algebra R B]

/-- The product-points equivalence is natural in the value algebra. -/
theorem prodPointsMulEquiv_mapValue (φ : A →ₐ[R] B)
    (f : WithConv (MonoidAlgebra R (G × H) →ₐ[R] A)) :
    prodPointsMulEquiv (A := B) (AlgHom.mapValue (H := MonoidAlgebra R (G × H)) φ f) =
      (AlgHom.mapValue (H := MonoidAlgebra R G) φ (prodPointsMulEquiv f).1,
        AlgHom.mapValue (H := MonoidAlgebra R H) φ (prodPointsMulEquiv f).2) := by
  apply Prod.ext
  · apply WithConv.ofConv_injective
    apply MonoidAlgebra.algHom_ext
    · intro g
      simp
    · ext
  · apply WithConv.ofConv_injective
    apply MonoidAlgebra.algHom_ext
    · intro h
      simp
    · ext

end MonoidAlgebra

namespace DiagonalizableGroup

variable {G' : Type v} {H' : Type w} [CommGroup G'] [CommGroup H']

/-- **The diagonalizable group of a product is the product of diagonalizable groups, on points.**
For commutative groups `G` and `H` and every commutative `R`-algebra `A`, the convolution group
of `A`-points of `D(G × H)` is the product of the convolution groups of `A`-points of `D(G)` and
`D(H)`. -/
noncomputable def prodPointsMulEquiv :
    WithConv (MonoidAlgebra R (G' × H') →ₐ[R] A) ≃*
      WithConv (MonoidAlgebra R G' →ₐ[R] A) × WithConv (MonoidAlgebra R H' →ₐ[R] A) :=
  MonoidAlgebra.prodPointsMulEquiv (G := G') (H := H')

/-- On generators, the first component of the diagonalizable product-points equivalence restricts
along `g ↦ (g, 1)`. -/
@[simp]
theorem prodPointsMulEquiv_fst_ofConv_single
    (f : WithConv (MonoidAlgebra R (G' × H') →ₐ[R] A)) (g : G') :
    (prodPointsMulEquiv f).1.ofConv (single g (1 : R)) =
      f.ofConv (single (g, (1 : H')) 1) :=
  MonoidAlgebra.prodPointsMulEquiv_fst_ofConv_single (H := H') f g

/-- On generators, the second component of the diagonalizable product-points equivalence restricts
along `h ↦ (1, h)`. -/
@[simp]
theorem prodPointsMulEquiv_snd_ofConv_single
    (f : WithConv (MonoidAlgebra R (G' × H') →ₐ[R] A)) (h : H') :
    (prodPointsMulEquiv f).2.ofConv (single h (1 : R)) =
      f.ofConv (single ((1 : G'), h) 1) :=
  MonoidAlgebra.prodPointsMulEquiv_snd_ofConv_single (G := G') f h

/-- On generators, the inverse diagonalizable product-points equivalence multiplies the two
factor-point values. -/
@[simp]
theorem prodPointsMulEquiv_symm_ofConv_single
    (f₁ : WithConv (MonoidAlgebra R G' →ₐ[R] A)) (f₂ : WithConv (MonoidAlgebra R H' →ₐ[R] A))
    (g : G') (h : H') :
    (prodPointsMulEquiv.symm (f₁, f₂)).ofConv (single (g, h) (1 : R)) =
      f₁.ofConv (single g 1) * f₂.ofConv (single h 1) :=
  MonoidAlgebra.prodPointsMulEquiv_symm_ofConv_single f₁ f₂ g h

/-- The diagonalizable product-points equivalence is natural in the value algebra. -/
theorem prodPointsMulEquiv_mapValue {B : Type*} [CommSemiring B] [Algebra R B] (φ : A →ₐ[R] B)
    (f : WithConv (MonoidAlgebra R (G' × H') →ₐ[R] A)) :
    prodPointsMulEquiv (A := B) (AlgHom.mapValue (H := MonoidAlgebra R (G' × H')) φ f) =
      (AlgHom.mapValue (H := MonoidAlgebra R G') φ (prodPointsMulEquiv f).1,
        AlgHom.mapValue (H := MonoidAlgebra R H') φ (prodPointsMulEquiv f).2) :=
  MonoidAlgebra.prodPointsMulEquiv_mapValue φ f

/-- The diagonalizable product-points equivalence agrees with the existing character
description of diagonalizable-group points: reading the character of a product point is the
coproduct of the characters read from its two restrictions. -/
theorem pointsMulEquiv_prodPointsMulEquiv
    (f : WithConv (MonoidAlgebra R (G' × H') →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := A) (G := G' × H') f =
      (pointsMulEquiv (R := R) (A := A) (G := G') (prodPointsMulEquiv f).1).coprod
        (pointsMulEquiv (R := R) (A := A) (G := H') (prodPointsMulEquiv f).2) := by
  ext p
  simp only [pointsMulEquiv_apply, MonoidHom.coprod_apply, Units.val_mul]
  rw [charOfPoint_apply_coe, charOfPoint_apply_coe, charOfPoint_apply_coe,
    prodPointsMulEquiv_fst_ofConv_single, prodPointsMulEquiv_snd_ofConv_single]
  rw [← map_mul, single_mul_single, Prod.mk_mul_mk, mul_one, one_mul]
  simp

end DiagonalizableGroup

end TauCeti
