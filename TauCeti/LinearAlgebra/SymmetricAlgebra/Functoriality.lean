/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# Functoriality of symmetric algebras

A linear map induces an algebra homomorphism between symmetric algebras. This file constructs the
map from the universal property, proves its identity and composition laws, and packages linear
equivalences as algebra equivalences. Chosen one-sided inverses remain one-sided inverses after
passing to symmetric algebras.

## Main definitions

* `SymmetricAlgebra.map`: the algebra homomorphism induced by a linear map.
* `SymmetricAlgebra.mapEquiv`: the algebra equivalence induced by a linear equivalence.

## Main results

* `SymmetricAlgebra.map_ι`: evaluation of the induced map on a canonical generator.
* `SymmetricAlgebra.map_id` and `SymmetricAlgebra.map_comp`: functoriality laws.
* `SymmetricAlgebra.map_injective_of_leftInverse` and
  `SymmetricAlgebra.map_surjective_of_rightInverse`: transport of split morphisms.

## Roadmap

This supplies the symmetric-algebra side of functoriality for subalgebras and direct sums in
Layer 3 of the LieHighestWeight roadmap. The product comparison and naturality of the canonical
map to the PBW associated graded are downstream.
-/

public section

namespace SymmetricAlgebra

universe u v w x

variable (R : Type u) [CommSemiring R]
variable {M : Type v} {N : Type w} {P : Type x}
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

/-- The algebra homomorphism between symmetric algebras induced by a linear map. -/
noncomputable def map (f : M →ₗ[R] N) :
    SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R N :=
  lift ((ι R N).comp f)

/-- A symmetric-algebra map acts on canonical generators by the original linear map. -/
@[simp]
theorem map_ι (f : M →ₗ[R] N) (a : M) :
    map R f (ι R M a) = ι R N (f a) := by
  simp [map]

/-- An algebra homomorphism between symmetric algebras is induced by `f` exactly when it has the
prescribed value on every canonical generator. -/
theorem map_unique (f : M →ₗ[R] N)
    (g : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R N) :
    (∀ a, g (ι R M a) = ι R N (f a)) ↔ g = map R f := by
  constructor
  · intro h
    apply algHom_ext
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply]
    exact (h a).trans (map_ι R f a).symm
  · rintro rfl
    exact map_ι R f

/-- The identity linear map induces the identity algebra homomorphism. -/
@[simp]
theorem map_id :
    map R (LinearMap.id (R := R) (M := M)) = AlgHom.id R (SymmetricAlgebra R M) := by
  apply algHom_ext
  ext a
  simp

/-- Composition of linear maps becomes composition of the induced algebra homomorphisms. -/
@[simp]
theorem map_comp (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    map R (g.comp f) = (map R g).comp (map R f) := by
  apply algHom_ext
  ext a
  simp

/-- A left inverse of linear maps induces a left inverse of the corresponding symmetric-algebra
maps. -/
theorem map_leftInverse {f : M →ₗ[R] N} {g : N →ₗ[R] M}
    (h : g.comp f = LinearMap.id) : Function.LeftInverse (map R g) (map R f) := by
  intro a
  have hmaps : (map R g).comp (map R f) = AlgHom.id R (SymmetricAlgebra R M) := by
    rw [← map_comp, h, map_id]
  exact AlgHom.congr_fun hmaps a

/-- A right inverse of linear maps induces a right inverse of the corresponding symmetric-algebra
maps. -/
theorem map_rightInverse {f : M →ₗ[R] N} {g : N →ₗ[R] M}
    (h : f.comp g = LinearMap.id) : Function.RightInverse (map R g) (map R f) := by
  intro a
  have hmaps : (map R f).comp (map R g) = AlgHom.id R (SymmetricAlgebra R N) := by
    rw [← map_comp, h, map_id]
  exact AlgHom.congr_fun hmaps a

/-- A split monomorphism induces an injective map of symmetric algebras. -/
theorem map_injective_of_leftInverse (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (h : g.comp f = LinearMap.id) : Function.Injective (map R f) :=
  (map_leftInverse R h).injective

/-- A split epimorphism induces a surjective map of symmetric algebras. -/
theorem map_surjective_of_rightInverse (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (h : f.comp g = LinearMap.id) : Function.Surjective (map R f) :=
  (map_rightInverse R h).surjective

/-- A linear equivalence induces an algebra equivalence of symmetric algebras. -/
noncomputable def mapEquiv (e : M ≃ₗ[R] N) :
    SymmetricAlgebra R M ≃ₐ[R] SymmetricAlgebra R N :=
  AlgEquiv.ofAlgHom (map R e.toLinearMap) (map R e.symm.toLinearMap)
    (by rw [← map_comp, e.comp_symm, map_id])
    (by rw [← map_comp, e.symm_comp, map_id])

/-- The algebra homomorphism underlying `mapEquiv` is induced by the underlying linear map. -/
@[simp]
theorem mapEquiv_toAlgHom (e : M ≃ₗ[R] N) :
    (mapEquiv R e).toAlgHom = map R e.toLinearMap := by
  rw [mapEquiv, AlgEquiv.toAlgHom_ofAlgHom]

/-- The induced algebra equivalence acts on canonical generators by the original linear
equivalence. -/
@[simp]
theorem mapEquiv_ι (e : M ≃ₗ[R] N) (a : M) :
    mapEquiv R e (ι R M a) = ι R N (e a) := by
  rw [← AlgEquiv.toAlgHom_apply, mapEquiv_toAlgHom, map_ι, LinearEquiv.coe_toLinearMap]

/-- Passing the inverse linear equivalence to symmetric algebras gives the inverse algebra
equivalence. -/
@[simp]
theorem mapEquiv_symm (e : M ≃ₗ[R] N) :
    (mapEquiv R e).symm = mapEquiv R e.symm := by
  apply AlgEquiv.ext
  intro a
  rw [mapEquiv, AlgEquiv.ofAlgHom_symm]
  simp only [AlgEquiv.ofAlgHom_apply, mapEquiv, LinearEquiv.symm_symm]

/-- The identity linear equivalence induces the identity algebra equivalence. -/
@[simp]
theorem mapEquiv_refl :
    mapEquiv R (LinearEquiv.refl R M) = AlgEquiv.refl := by
  apply AlgEquiv.coe_toAlgHom_injective
  rw [mapEquiv_toAlgHom, LinearEquiv.refl_toLinearMap, map_id, AlgEquiv.refl_toAlgHom]

/-- Composition of linear equivalences becomes composition of the induced algebra
equivalences. -/
@[simp]
theorem mapEquiv_trans (e : M ≃ₗ[R] N) (d : N ≃ₗ[R] P) :
    (mapEquiv R e).trans (mapEquiv R d) = mapEquiv R (e.trans d) := by
  apply AlgEquiv.coe_toAlgHom_injective
  rw [mapEquiv_toAlgHom]
  have htrans : ((mapEquiv R e).trans (mapEquiv R d)).toAlgHom =
      (mapEquiv R d).toAlgHom.comp (mapEquiv R e).toAlgHom := by
    apply AlgHom.ext
    intro a
    simp only [AlgEquiv.toAlgHom_apply, AlgEquiv.trans_apply, AlgHom.comp_apply]
  rw [htrans, mapEquiv_toAlgHom, mapEquiv_toAlgHom]
  have h : (e.trans d).toLinearMap = d.toLinearMap.comp e.toLinearMap := by
    ext a
    simp only [LinearMap.comp_apply, LinearEquiv.trans_apply, LinearEquiv.coe_toLinearMap]
  rw [h, map_comp]

end SymmetricAlgebra
