/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Commutator.Basic
public import TauCeti.Algebra.AlgebraicGroup.Product
public import TauCeti.Algebra.Coalgebra.Convolution

/-!
# The commutator morphism in Hopf-algebra coordinates

For a commutative Hopf algebra `H` over a commutative semiring `R`, this file constructs the
algebra morphism

```text
H ⟶ H ⊗[R] H
```

representing the group commutator `(g, h) ↦ g * h * g⁻¹ * h⁻¹`. If `i₁` and `i₂` are the
two universal points with values in `H ⊗[R] H`, the morphism is the algebra map underlying the
convolution point `i₁ * i₂ * i₁⁻¹ * i₂⁻¹`.

The commutator is not generally a group homomorphism from the product, so this construction is an
algebra morphism rather than a bialgebra morphism. Its kernel nevertheless determines the smallest
closed subgroup scheme containing the image, constructed in
`TauCeti.Algebra.AlgebraicGroup.Derived`.

## Main declarations

* `TauCeti.HopfAlgebra.commutatorAlgHom`: the coordinate algebra morphism of the commutator.
* `TauCeti.HopfAlgebra.productMap_comp_commutatorAlgHom`: evaluation at two algebra-valued points.
* `TauCeti.HopfAlgebra.comp_commutatorAlgHom`: evaluation against an arbitrary map from the tensor
  square.

## References

* J. S. Milne, *Algebraic Groups* (2017), §6d.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 10.

This is the coordinate prerequisite for the derived group `G_der` in Layer 6 of the
ReductiveGroups roadmap.
-/

public section

open TensorProduct WithConv
open scoped commutatorElement

namespace TauCeti.HopfAlgebra

universe u v w

variable {R : Type u} {H : Type v} [CommSemiring R] [CommSemiring H]
variable [_root_.HopfAlgebra R H]

/-- The coordinate algebra morphism of the group commutator
`(g, h) ↦ g * h * g⁻¹ * h⁻¹`.

The two tensor factors are the two commutator variables, in that order. -/
noncomputable def commutatorAlgHom : H →ₐ[R] H ⊗[R] H :=
  (toConv (Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H) (H₂ := H)).toAlgHom *
      toConv (Bialgebra.TensorProduct.includeRight (R := R) (H₁ := H) (H₂ := H)).toAlgHom *
      (toConv
        (Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H) (H₂ := H)).toAlgHom)⁻¹ *
      (toConv
        (Bialgebra.TensorProduct.includeRight (R := R) (H₁ := H) (H₂ := H)).toAlgHom)⁻¹).ofConv

/-- The commutator coordinate morphism is the convolution commutator of the two universal
tensor-factor points. -/
theorem toConv_commutatorAlgHom :
    toConv (commutatorAlgHom (R := R) (H := H)) =
      toConv (Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H) (H₂ := H)).toAlgHom *
        toConv (Bialgebra.TensorProduct.includeRight (R := R) (H₁ := H) (H₂ := H)).toAlgHom *
        (toConv
          (Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H) (H₂ := H)).toAlgHom)⁻¹ *
        (toConv
          (Bialgebra.TensorProduct.includeRight (R := R) (H₁ := H) (H₂ := H)).toAlgHom)⁻¹ := by
  rw [commutatorAlgHom, toConv_ofConv]

/-- Evaluating the commutator coordinate morphism at two algebra-valued points gives their
group-theoretic commutator. -/
@[simp]
theorem productMap_comp_commutatorAlgHom
    {A : Type w} [CommSemiring A] [Algebra R A]
    (g h : WithConv (H →ₐ[R] A)) :
    (Algebra.TensorProduct.productMap g.ofConv h.ofConv).comp
      (commutatorAlgHom (R := R) (H := H)) =
      (⁅g, h⁆).ofConv := by
  have hmap :
      AlgHom.mapValue (H := H) (Algebra.TensorProduct.productMap g.ofConv h.ofConv)
          (toConv (commutatorAlgHom (R := R) (H := H))) = ⁅g, h⁆ := by
    rw [toConv_commutatorAlgHom, map_mul, map_mul, map_mul, map_inv, map_inv]
    simp only [AlgHom.mapValue_apply,
      Bialgebra.TensorProduct.includeLeft_toAlgHom,
      Bialgebra.TensorProduct.includeRight_toAlgHom,
      Algebra.TensorProduct.productMap_left, Algebra.TensorProduct.productMap_right,
      commutatorElement_def]
  exact congrArg WithConv.ofConv hmap

/-- Evaluation against an arbitrary algebra map out of the tensor square takes the commutator of
its restrictions to the two tensor factors. -/
theorem comp_commutatorAlgHom {A : Type w} [CommSemiring A] [Algebra R A]
    (phi : H ⊗[R] H →ₐ[R] A) :
    phi.comp (commutatorAlgHom (R := R) (H := H)) =
      (⁅toConv (phi.comp Algebra.TensorProduct.includeLeft),
        toConv (phi.comp Algebra.TensorProduct.includeRight)⁆).ofConv := by
  calc
    phi.comp (commutatorAlgHom (R := R) (H := H)) =
        (Algebra.TensorProduct.productMap
          (phi.comp Algebra.TensorProduct.includeLeft)
          (phi.comp Algebra.TensorProduct.includeRight)).comp
            (commutatorAlgHom (R := R) (H := H)) :=
      congrArg (fun psi : H ⊗[R] H →ₐ[R] A ↦
        psi.comp (commutatorAlgHom (R := R) (H := H)))
        (AffineGroup.Product.productMap_restrict phi).symm
    _ = _ := by
      simpa only [ofConv_toConv] using
        productMap_comp_commutatorAlgHom (R := R) (H := H)
          (toConv (phi.comp Algebra.TensorProduct.includeLeft))
          (toConv (phi.comp Algebra.TensorProduct.includeRight))

/-- The commutator with the identity in the first variable is the identity point. -/
@[simp]
theorem productMap_one_id_comp_commutatorAlgHom :
    (Algebra.TensorProduct.productMap
        (1 : WithConv (H →ₐ[R] H)).ofConv (AlgHom.id R H)).comp
      (commutatorAlgHom (R := R) (H := H)) =
        (1 : WithConv (H →ₐ[R] H)).ofConv := by
  simpa using productMap_comp_commutatorAlgHom (R := R) (H := H)
    (1 : WithConv (H →ₐ[R] H)) (toConv (AlgHom.id R H))

/-- The commutator with the identity in the second variable is the identity point. -/
@[simp]
theorem productMap_id_one_comp_commutatorAlgHom :
    (Algebra.TensorProduct.productMap
        (AlgHom.id R H) (1 : WithConv (H →ₐ[R] H)).ofConv).comp
      (commutatorAlgHom (R := R) (H := H)) =
        (1 : WithConv (H →ₐ[R] H)).ofConv := by
  simpa using productMap_comp_commutatorAlgHom (R := R) (H := H)
    (toConv (AlgHom.id R H)) (1 : WithConv (H →ₐ[R] H))

end TauCeti.HopfAlgebra
