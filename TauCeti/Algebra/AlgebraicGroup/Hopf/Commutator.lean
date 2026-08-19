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
`TauCeti.Algebra.AlgebraicGroup.Derived.Basic`.

## Main declarations

* `TauCeti.HopfAlgebra.commutatorAlgHom`: the coordinate algebra morphism of the commutator.
* `TauCeti.HopfAlgebra.productMap_comp_commutatorAlgHom`: evaluation at two algebra-valued points.

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
  rw [AlgHom.mapValue_apply] at hmap
  simpa only [ofConv_toConv] using congrArg WithConv.ofConv hmap

end TauCeti.HopfAlgebra
