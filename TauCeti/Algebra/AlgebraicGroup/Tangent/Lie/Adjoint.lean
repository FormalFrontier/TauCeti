/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Basic
public import Mathlib.RepresentationTheory.Basic

/-!
# The adjoint action on the tangent space

The points of a Hopf algebra act on the counit-valued derivations — the tangent
vectors at the identity — by convolution conjugation: `Ad g d = g ⋆ d ⋆ g⁻¹` in the
convolution ring of linear maps, the differential of the conjugation
`c_g x = g ⋆ x ⋆ g⁻¹` of the group of points. Conjugation is a ring automorphism of
the whole convolution ring; this file shows it restricts to the derivations, and
packages the restriction as a representation of the group of points on the tangent
space (`adRepresentation`). This is the adjoint action of the corresponding affine
group scheme on its Lie functor, for commutative `A`.

Closure is composition-level, by the exterior-product calculus of `Lie.Basic`: an
algebra-map point satisfies `g ∘ mul = g ⊠ g`, a derivation satisfies
`d ∘ mul = e ⊠ d + d ⊠ e` for the convolution unit `e`, and the conjugates collapse
by `g ⋆ e ⋆ g⁻¹ = e`, leaving the Leibniz form for `g ⋆ d ⋆ g⁻¹`. No antipode
computation appears; inverses come from the group of points.

## Main declarations

* `TauCeti.Derivation.adDerivation`: the conjugate of a tangent vector by a point.
* `TauCeti.Derivation.adRepresentation`: the adjoint action, as a representation of
  the convolution group of points on the tangent space.

The action stays on the Lie functor `B ↦ Derivation R A (CounitAlgebra R A B)`;
presenting it as `G → GL(Lie G)` on a fixed module needs a finite-projectivity
hypothesis on the conormal module and is not attempted here.
-/

public section

namespace TauCeti

namespace Derivation

open Coalgebra WithConv TensorProduct

variable {R A B : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [CommRing B] [Algebra R B]

/-- An algebra-map point composed with multiplication is its own exterior square:
the multiplicativity of the point, in convolution form. -/
lemma toConv_algHom_comp_mul' (g : A →ₐ[R] Bialgebra.CounitAlgebra R A B) :
    toConv (g.toLinearMap ∘ₗ LinearMap.mul' R A) =
      mulTensor (toConv g.toLinearMap) (toConv g.toLinearMap) := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp [mulTensor_ofConv_tmul]

/-- The linear images of a point and of its convolution inverse multiply to the
convolution unit. -/
lemma toConv_toLinearMap_mul_inv (g : WithConv (A →ₐ[R] Bialgebra.CounitAlgebra R A B)) :
    toConv (g.ofConv.toLinearMap) * toConv ((g⁻¹).ofConv.toLinearMap) =
      (1 : WithConv (A →ₗ[R] Bialgebra.CounitAlgebra R A B)) := by
  have h := congrArg (fun ψ : WithConv (A →ₐ[R] Bialgebra.CounitAlgebra R A B) =>
    toConv ψ.ofConv.toLinearMap) (mul_inv_cancel g)
  rwa [AlgHom.toLinearMap_convMul, AlgHom.toLinearMap_convOne] at h

private lemma conj_comp_mul'
    (g : WithConv (A →ₐ[R] Bialgebra.CounitAlgebra R A B))
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    toConv ((toConv g.ofConv.toLinearMap *
        toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
        toConv ((g⁻¹).ofConv.toLinearMap)).ofConv ∘ₗ LinearMap.mul' R A) =
      mulTensor 1 (toConv g.ofConv.toLinearMap *
          toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
          toConv ((g⁻¹).ofConv.toLinearMap)) +
        mulTensor (toConv g.ofConv.toLinearMap *
          toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
          toConv ((g⁻¹).ofConv.toLinearMap)) 1 := by
  have h := LinearMap.convMul_comp_coalgHom_distrib
    (toConv g.ofConv.toLinearMap * toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B))
    (toConv ((g⁻¹).ofConv.toLinearMap)) (_root_.Bialgebra.mulCoalgHom R A)
  have h2 := LinearMap.convMul_comp_coalgHom_distrib
    (toConv g.ofConv.toLinearMap) (toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B))
    (_root_.Bialgebra.mulCoalgHom R A)
  rw [show (_root_.Bialgebra.mulCoalgHom R A).toLinearMap = LinearMap.mul' R A from rfl] at h h2
  rw [h, toConv_ofConv]
  rw [show (toConv g.ofConv.toLinearMap *
      toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B)).ofConv ∘ₗ
      LinearMap.mul' R A = ((toConv g.ofConv.toLinearMap *
        toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B)).ofConv).comp
        (LinearMap.mul' R A) from rfl, h2, toConv_ofConv]
  rw [show g.ofConv.toLinearMap ∘ₗ LinearMap.mul' R A =
      (g.ofConv.toLinearMap).comp (LinearMap.mul' R A) from rfl]
  rw [show toConv (g.ofConv.toLinearMap.comp (LinearMap.mul' R A)) =
      mulTensor (toConv g.ofConv.toLinearMap) (toConv g.ofConv.toLinearMap) from
      toConv_algHom_comp_mul' g.ofConv,
    toConv_coe_comp_mul' d,
    show toConv (((g⁻¹).ofConv.toLinearMap).comp (LinearMap.mul' R A)) =
      mulTensor (toConv (g⁻¹).ofConv.toLinearMap) (toConv (g⁻¹).ofConv.toLinearMap) from
      toConv_algHom_comp_mul' (g⁻¹).ofConv]
  rw [mul_add, add_mul, mulTensor_convMul, mulTensor_convMul, mulTensor_convMul,
    mulTensor_convMul, mul_one, toConv_toLinearMap_mul_inv]

end Derivation

end TauCeti
