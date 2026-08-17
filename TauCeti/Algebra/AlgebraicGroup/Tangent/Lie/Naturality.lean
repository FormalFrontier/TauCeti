/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Naturality

/-!
# The tangent Lie algebra is natural in the coefficient algebra

Postcomposition along a homomorphism of coefficient rings preserves the convolution
commutator bracket on counit-valued derivations. Thus the functorial linear map
`Derivation.mapValue` upgrades to a Lie algebra homomorphism. This is the
Lie-algebra layer of the natural adjoint action constructed in `Tangent.Naturality`.

## Main declarations

* `Derivation.mapValue_lie`: postcomposition preserves the tangent bracket.
* `Derivation.lieMapValue`: change of coefficients as a Lie algebra
  homomorphism.
-/

public section

namespace Derivation

open TauCeti _root_.Coalgebra

variable {R A B C : Type*} [CommRing R] [CommRing A] [Bialgebra R A]
  [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]

/-- Postcomposition of counit-valued derivations preserves their convolution
commutator bracket. -/
@[simp]
theorem mapValue_lie (phi : B →ₐ[R] C)
    (d e : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    mapValue (A := A) phi ⁅d, e⁆ =
      ⁅mapValue (A := A) phi d, mapValue (A := A) phi e⁆ := by
  ext a
  rw [mapValue_apply]
  rw [← Bialgebra.CounitAlgebra.mapAlgHom_apply (A := A) phi]
  -- Extensionality and `mapValue_apply` leave function coercions on the two
  -- brackets; restating them as linear-map applications lets `coe_bracket` apply.
  change ((Bialgebra.CounitAlgebra.mapAlgHom (A := A) phi).toLinearMap.comp
      (↑⁅d, e⁆ : A →ₗ[R] Bialgebra.CounitAlgebra R A B)) a =
    (↑⁅mapValue (A := A) phi d, mapValue (A := A) phi e⁆ :
      A →ₗ[R] Bialgebra.CounitAlgebra R A C) a
  rw [coe_bracket, coe_bracket]
  simp only [LinearMap.comp_sub]
  rw [LinearMap.algHom_comp_convMul_distrib, LinearMap.algHom_comp_convMul_distrib]
  simp only [coe_mapValue_linearMap]

/-- Change of coefficient algebra on the tangent Lie algebra. -/
noncomputable def lieMapValue (phi : B →ₐ[R] C) :
  Derivation R A (Bialgebra.CounitAlgebra R A B) →ₗ⁅R⁆
      Derivation R A (Bialgebra.CounitAlgebra R A C) where
  toLinearMap := mapValue (A := A) phi
  map_lie' := fun {d e} => mapValue_lie (A := A) phi d e

/-- The underlying linear map of change of coefficients on the tangent Lie algebra is
`mapValue`. -/
@[simp]
lemma lieMapValue_toLinearMap (phi : B →ₐ[R] C) :
    (lieMapValue (R := R) (A := A) (B := B) (C := C) phi).toLinearMap =
      mapValue (A := A) phi := by
  ext d a
  -- `lieMapValue` has no equation lemma; this is its `toLinearMap` field,
  -- evaluated after extensionality.
  change mapValue (A := A) phi d a = mapValue (A := A) phi d a
  rfl

/-- Change of coefficients on the tangent Lie algebra acts pointwise by
postcomposition. -/
@[simp]
lemma lieMapValue_apply (phi : B →ₐ[R] C)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) (a : A) :
    lieMapValue (R := R) (A := A) (B := B) (C := C) phi d a =
      phi (d a) := by
  rw [← mapValue_apply (A := A) phi d a]
  have h := DFunLike.congr_fun
    (lieMapValue_toLinearMap (R := R) (A := A) (B := B) (C := C) phi) d
  exact DFunLike.congr_fun h a

/-- Change of coefficients by the identity is the identity Lie algebra homomorphism. -/
@[simp]
theorem lieMapValue_id :
    lieMapValue (A := A) (AlgHom.id R B) =
      LieHom.id (R := R) := by
  apply LieHom.ext
  intro d
  -- `LieHom.ext` states the goal through function coercions, while the public
  -- functoriality theorem is about underlying linear maps. Expose that stable
  -- projection once so `lieMapValue_toLinearMap` and `mapValue_id` apply.
  change (lieMapValue (A := A) (AlgHom.id R B)).toLinearMap d =
    (LieHom.id (R := R)).toLinearMap d
  rw [lieMapValue_toLinearMap, mapValue_id]
  rfl

/-- Change of coefficients on tangent Lie algebras preserves composition. -/
@[simp]
theorem lieMapValue_comp {D : Type*} [CommRing D] [Algebra R D]
    (psi : C →ₐ[R] D) (phi : B →ₐ[R] C) :
    lieMapValue (A := A) (psi.comp phi) =
      (lieMapValue (A := A) psi).comp (lieMapValue (A := A) phi) := by
  apply LieHom.ext
  intro d
  -- As above, this conversion connects `LieHom.ext` to the public underlying-map
  -- API; it does not unfold the implementation of coefficient transport.
  change (lieMapValue (A := A) (psi.comp phi)).toLinearMap d =
    ((lieMapValue (A := A) psi).comp (lieMapValue (A := A) phi)).toLinearMap d
  rw [lieMapValue_toLinearMap, LieHom.toLinearMap_comp, lieMapValue_toLinearMap,
    lieMapValue_toLinearMap, mapValue_comp]

end Derivation
