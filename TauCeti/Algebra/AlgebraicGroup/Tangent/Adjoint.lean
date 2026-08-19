/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Basic
public import Mathlib.RepresentationTheory.Basic

/-!
# The adjoint action on the tangent space

The points of a Hopf algebra act on the counit-valued derivations — the tangent
vectors at the identity — by convolution conjugation: `Ad g d = g ⋆ d ⋆ g⁻¹` in the
convolution semiring of linear maps, the differential of the conjugation
`c_g x = g ⋆ x ⋆ g⁻¹` of the group of points. Conjugation is a semiring automorphism of
the whole convolution semiring; this file shows it restricts to the derivations, and
packages the restriction, one coefficient algebra `B` at a time, as a representation of
the `B`-points on the `B`-valued tangent vectors (`adRepresentation`). For commutative
`A` these are the coefficientwise layers of the adjoint action of the corresponding
affine group scheme on its Lie functor; their compatibility as `B` varies
(postcomposition naturality) is later infrastructure, not packaged here.

Closure is composition-level, by the exterior-product calculus of `Tangent.Basic`: an
algebra-map point satisfies `g ∘ mul = g ⊠ g`, a derivation satisfies
`d ∘ mul = e ⊠ d + d ⊠ e` for the convolution unit `e`, and the conjugates collapse
by `g ⋆ e ⋆ g⁻¹ = e`, leaving the Leibniz form for `g ⋆ d ⋆ g⁻¹`. No antipode
computation appears; inverses come from the group of points.

## Main declarations

* `Derivation.adDerivation`: the conjugate of a tangent vector by a point.
* `Derivation.toConv_coe_adDerivation`: that conjugate as the convolution product
  `g ⋆ d ⋆ g⁻¹`, the form the algebraic manipulations use.
* `Derivation.adRepresentation`: the adjoint action, as a representation of
  the convolution group of points on the tangent space.

Compatibility of the action with the Lie bracket needs the Lie structure and so lives in
`Tangent.Lie.Adjoint.Basic`, keeping this module free of it.

The action stays on the Lie functor `B ↦ Derivation R A (CounitAlgebra R A B)`; at
each `B` it is a genuine representation. Identifying the functor's value at `B` with
`B ⊗ Lie(G)(R)` — the classical fixed-module `G → GL(Lie G)` — needs a
finite-projectivity hypothesis on the conormal module and is not attempted here.

## References

* J. S. Milne, *Algebraic Groups* (2017), §14 (the adjoint representation).
* J. C. Jantzen, *Representations of Algebraic Groups*, I.7.18.
-/

public section

namespace Derivation

open TauCeti _root_.Coalgebra WithConv TensorProduct

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [HopfAlgebra R A]
  [CommSemiring B] [Algebra R B]

private lemma conj_comp_mul'
    (g : WithConv (A →ₐ[R] Bialgebra.CounitAlgebra R A B))
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    toConv ((toConv g.ofConv.toLinearMap *
        toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
        toConv ((g⁻¹).ofConv.toLinearMap)).ofConv ∘ₗ LinearMap.mul' R A) =
      LinearMap.mulTensor 1 (toConv g.ofConv.toLinearMap *
          toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
          toConv ((g⁻¹).ofConv.toLinearMap)) +
        LinearMap.mulTensor (toConv g.ofConv.toLinearMap *
          toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
          toConv ((g⁻¹).ofConv.toLinearMap)) 1 := by
  have h := LinearMap.convMul_comp_coalgHom_distrib
    (toConv g.ofConv.toLinearMap * toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B))
    (toConv ((g⁻¹).ofConv.toLinearMap)) (_root_.Bialgebra.mulCoalgHom R A)
  have h2 := LinearMap.convMul_comp_coalgHom_distrib
    (toConv g.ofConv.toLinearMap) (toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B))
    (_root_.Bialgebra.mulCoalgHom R A)
  -- The `toLinearMap` field of `mulCoalgHom` is definitionally `mul'`; the library
  -- states this only for the coercion, whose pattern does not match the field
  -- projection, so the identification is by `rfl`.
  rw [show (_root_.Bialgebra.mulCoalgHom R A).toLinearMap = LinearMap.mul' R A from rfl] at h h2
  rw [h, toConv_ofConv]
  rw [h2, toConv_ofConv]
  rw [AlgHom.toConv_toLinearMap_comp_mul' g.ofConv, toConv_coe_comp_mul' d,
    AlgHom.toConv_toLinearMap_comp_mul' (g⁻¹).ofConv]
  rw [mul_add, add_mul, LinearMap.mulTensor_convMul, LinearMap.mulTensor_convMul,
    LinearMap.mulTensor_convMul, LinearMap.mulTensor_convMul, mul_one,
    ← AlgHom.toLinearMap_convMul, mul_inv_cancel, AlgHom.toLinearMap_convOne]

/-- The Leibniz rule for a conjugated derivation, in scalar-action form. -/
private lemma conj_ofConv_mul
    (g : WithConv (A →ₐ[R] Bialgebra.CounitAlgebra R A B))
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) (a b : A) :
    (toConv g.ofConv.toLinearMap *
        toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
        toConv ((g⁻¹).ofConv.toLinearMap)).ofConv (a * b) =
      a • (toConv g.ofConv.toLinearMap *
          toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
          toConv ((g⁻¹).ofConv.toLinearMap)).ofConv b +
        b • (toConv g.ofConv.toLinearMap *
          toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
          toConv ((g⁻¹).ofConv.toLinearMap)).ofConv a := by
  have h := congrArg (fun F => F.ofConv (a ⊗ₜ[R] b)) (conj_comp_mul' g d)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mul'_apply,
    ofConv_add, LinearMap.add_apply, LinearMap.mulTensor_apply_tmul,
    LinearMap.convOne_apply, Bialgebra.CounitAlgebra.algebraMap_base] at h
  rw [h, ← Bialgebra.CounitAlgebra.algebraMap_apply R A B a,
    ← Bialgebra.CounitAlgebra.algebraMap_apply R A B b, ← Algebra.commutes,
    ← Algebra.smul_def, ← Algebra.smul_def]

variable (B) in
/-- The conjugate of a tangent vector by a point: the adjoint action
`Ad g d = g ⋆ d ⋆ g⁻¹`, the differential of conjugation on the group of points. -/
noncomputable def adDerivation (g : WithConv (A →ₐ[R] Bialgebra.CounitAlgebra R A B))
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    Derivation R A (Bialgebra.CounitAlgebra R A B) where
  toLinearMap :=
    (toConv g.ofConv.toLinearMap *
        toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
        toConv ((g⁻¹).ofConv.toLinearMap)).ofConv
  map_one_eq_zero' := by
    -- The middle factor kills `1`: `d 1 = 0`, and both convolution products
    -- evaluate at `1` factorwise since `comul 1 = 1 ⊗ 1`.
    simp [Algebra.TensorProduct.one_def, Derivation.coeFn_coe]
  leibniz' a b := conj_ofConv_mul g d a b

/-- The adjoint action is the convolution conjugate, on underlying linear maps. -/
@[simp]
theorem coe_adDerivation_linearMap (g : WithConv (A →ₐ[R] Bialgebra.CounitAlgebra R A B))
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    ↑(adDerivation B g d) =
      (toConv g.ofConv.toLinearMap *
        toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
        toConv ((g⁻¹).ofConv.toLinearMap)).ofConv := by
  -- `adDerivation` has no equation lemma to rewrite with; `change` spells out its
  -- definitional unfolding once, explicitly.
  change (toConv g.ofConv.toLinearMap *
      toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
      toConv ((g⁻¹).ofConv.toLinearMap)).ofConv = _
  rfl

/-- The adjoint action, valuewise: the conjugate evaluated at an element of the
bialgebra. -/
@[simp]
theorem adDerivation_apply (g : WithConv (A →ₐ[R] Bialgebra.CounitAlgebra R A B))
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) (a : A) :
    adDerivation B g d a =
      (toConv g.ofConv.toLinearMap *
        toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
        toConv ((g⁻¹).ofConv.toLinearMap)).ofConv a := by
  have h := DFunLike.congr_fun (coe_adDerivation_linearMap g d) a
  simpa only [Derivation.coeFn_coe] using h

/-- **The conjugate of a tangent vector, in convolution form**: `Ad g d` is the product
`g ⋆ d ⋆ g⁻¹` in the convolution algebra of linear maps.  This is the form in which the
adjoint action is manipulated algebraically, and the bracket compatibility in
`Tangent.Lie.Adjoint.Basic` is proved from it. -/
lemma toConv_coe_adDerivation
    (g : WithConv (A →ₐ[R] Bialgebra.CounitAlgebra R A B))
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    toConv (↑(adDerivation B g d) : A →ₗ[R] Bialgebra.CounitAlgebra R A B) =
      toConv g.ofConv.toLinearMap *
        toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
        toConv ((g⁻¹).ofConv.toLinearMap) := by
  rw [coe_adDerivation_linearMap, toConv_ofConv]

variable (B) in
/-- The adjoint action of the group of points on the tangent space, as a
`B`-linear representation: conjugation is a semiring automorphism of the convolution
semiring, it restricts to the derivations, and scalars of the coefficient algebra pass
through the conjugation because `B` is commutative. -/
noncomputable def adRepresentation :
    Representation B (WithConv (A →ₐ[R] Bialgebra.CounitAlgebra R A B))
      (Derivation R A (Bialgebra.CounitAlgebra R A B)) where
  toFun g :=
    { toFun := adDerivation B g
      map_add' := fun d₁ d₂ => Derivation.ext fun a => by
        simp only [Derivation.add_apply]
        rw [adDerivation_apply, adDerivation_apply, adDerivation_apply,
          Derivation.coe_add_linearMap, toConv_add, mul_add, add_mul,
          ofConv_add, LinearMap.add_apply]
      map_smul' := fun b d => Derivation.ext fun a => by
        simp only [Derivation.smul_apply, RingHom.id_apply]
        rw [adDerivation_apply, adDerivation_apply, Derivation.coe_smul_linearMap,
          toConv_smul, mul_smul_comm, smul_mul_assoc, ofConv_smul,
          LinearMap.smul_apply] }
  map_one' := by
    ext d a
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.one_apply]
    rw [adDerivation_apply, AlgHom.toLinearMap_convOne, inv_one,
      AlgHom.toLinearMap_convOne, one_mul, mul_one, ofConv_toConv,
      Derivation.coeFn_coe]
  map_mul' g h := by
    ext d a
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply]
    rw [adDerivation_apply, adDerivation_apply, toConv_coe_adDerivation, mul_inv_rev,
      AlgHom.toLinearMap_convMul, AlgHom.toLinearMap_convMul]
    exact DFunLike.congr_fun (congrArg ofConv (by simp [mul_assoc])) a

@[simp]
lemma adRepresentation_apply (g : WithConv (A →ₐ[R] Bialgebra.CounitAlgebra R A B))
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    adRepresentation B g d = adDerivation B g d := by
  -- `adRepresentation` has no equation lemma to rewrite with; `change` spells out its
  -- definitional unfolding once, explicitly.
  change adDerivation B g d = _
  rfl

end Derivation
