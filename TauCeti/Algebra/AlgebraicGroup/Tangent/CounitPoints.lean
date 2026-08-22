/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Bialgebra.CounitAlgebra` and its identification with the coefficient algebra live here.
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Basic

/-!
# Points valued in the counit algebra

Tangent vectors at the identity of `Spec H` are derivations valued in
`Bialgebra.CounitAlgebra R H B`, and the points that conjugate them are therefore points valued
in that same algebra. The counit algebra is `B` carrying one extra `H`-algebra structure, which
an `R`-algebra homomorphism out of `H` does not see, so those points are just the `B`-points.

This file records that identification as an isomorphism of convolution groups, so that a
computation of the adjoint action stated for counit-algebra-valued points can be read off the
ordinary functor of points.

## Main declarations

* `TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv`: points valued in the counit algebra are the
  points valued in the coefficient algebra.
* `TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv_eq_mapValue`: the identification is
  postcomposition with `TauCeti.Bialgebra.CounitAlgebra.algEquivSelf`.
* `TauCeti.Bialgebra.CounitAlgebra.pointsMulEquiv_mapValue` and
  `TauCeti.Bialgebra.CounitAlgebra.mapValue_pointsMulEquiv_symm_apply`: the identification is
  natural in the coefficient algebra.

This is coefficient bookkeeping for the adjoint action of Layer 2, "Lie algebra and the adjoint
representation", of the ReductiveGroups roadmap.
-/

public section

open WithConv

namespace TauCeti

namespace Bialgebra.CounitAlgebra

universe u v w

variable (R : Type u) (H : Type v) (B : Type w)
variable [CommSemiring R] [CommSemiring H] [HopfAlgebra R H] [CommSemiring B] [Algebra R B]

/-- Points valued in the counit algebra of `H` are the points valued in the coefficient algebra
`B` itself: the counit algebra is `B` with one extra `H`-algebra structure, which an `R`-algebra
homomorphism out of `H` does not see. The identification is an isomorphism of convolution
groups. -/
noncomputable def pointsMulEquiv :
    WithConv (H →ₐ[R] CounitAlgebra R H B) ≃* WithConv (H →ₐ[R] B) where
  toFun := AlgHom.mapValue (H := H) (algEquivSelf R H B).toAlgHom
  invFun := AlgHom.mapValue (H := H) (algEquivSelf R H B).symm.toAlgHom
  left_inv _ := by
    apply WithConv.ofConv_injective
    ext x
    simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
    exact AlgEquiv.symm_apply_apply _ _
  right_inv _ := by
    apply WithConv.ofConv_injective
    ext x
    simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
    exact AlgEquiv.apply_symm_apply _ _
  map_mul' := map_mul _

/-- The transport of points is postcomposition with the identification of the counit algebra
with the coefficient algebra. -/
theorem pointsMulEquiv_eq_mapValue (g : WithConv (H →ₐ[R] CounitAlgebra R H B)) :
    pointsMulEquiv R H B g =
      AlgHom.mapValue (H := H) (algEquivSelf R H B).toAlgHom g :=
  (rfl)

/-- Transporting a counit-algebra-valued point does not change its values. -/
@[simp]
theorem pointsMulEquiv_apply (g : WithConv (H →ₐ[R] CounitAlgebra R H B)) (h : H) :
    (pointsMulEquiv R H B g).ofConv h = algEquivSelf R H B (g.ofConv h) := by
  -- `pointsMulEquiv` has no equation lemma; unfold its forward map once, explicitly.
  change (AlgHom.mapValue (H := H) (algEquivSelf R H B).toAlgHom g).ofConv h =
    algEquivSelf R H B (g.ofConv h)
  rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
  rfl

/-- Transporting a `B`-valued point into the counit algebra does not change its values. -/
@[simp]
theorem pointsMulEquiv_symm_apply (f : WithConv (H →ₐ[R] B)) (h : H) :
    ((pointsMulEquiv R H B).symm f).ofConv h = (algEquivSelf R H B).symm (f.ofConv h) := by
  -- `pointsMulEquiv` has no equation lemma; unfold its inverse map once, explicitly.
  change (AlgHom.mapValue (H := H) (algEquivSelf R H B).symm.toAlgHom f).ofConv h =
    (algEquivSelf R H B).symm (f.ofConv h)
  rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
  rfl

section Naturality

variable {C : Type*} [CommSemiring C] [Algebra R C]

/-- The counit-points equivalence is natural in the coefficient algebra. -/
theorem pointsMulEquiv_mapValue (phi : B →ₐ[R] C)
    (g : WithConv (H →ₐ[R] CounitAlgebra R H B)) :
    pointsMulEquiv R H C
        (AlgHom.mapValue (H := H)
          (mapAlgHom (R := R) (A := H) (B := B) (C := C) phi) g) =
      AlgHom.mapValue (H := H) phi (pointsMulEquiv R H B g) := by
  apply WithConv.ofConv_injective
  ext h
  simp only [AlgHom.mapValue_apply, pointsMulEquiv_apply, AlgHom.coe_comp,
    Function.comp_apply, mapAlgHom_apply]
  calc
    _ = phi (g.ofConv h) := algEquivSelf_apply (R := R) (A := H) (B := C) _
    _ = _ := congrArg phi (algEquivSelf_apply (R := R) (A := H) (B := B) _).symm

/-- Naturality of the inverse counit-points equivalence in the coefficient algebra. -/
theorem mapValue_pointsMulEquiv_symm_apply (phi : B →ₐ[R] C)
    (f : WithConv (H →ₐ[R] B)) :
    AlgHom.mapValue (H := H)
        (mapAlgHom (R := R) (A := H) (B := B) (C := C) phi)
        ((pointsMulEquiv R H B).symm f) =
      (pointsMulEquiv R H C).symm (AlgHom.mapValue (H := H) phi f) := by
  apply (pointsMulEquiv R H C).injective
  rw [pointsMulEquiv_mapValue, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

end Naturality

end Bialgebra.CounitAlgebra

end TauCeti
