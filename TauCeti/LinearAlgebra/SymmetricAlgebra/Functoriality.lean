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
equivalences as algebra equivalences.

The construction and its lemma set follow Mathlib's `CliffordAlgebra.map` and `ExteriorAlgebra.map`
functoriality APIs (`Mathlib/LinearAlgebra/CliffordAlgebra/Basic.lean` and
`Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean`).

The declaration order, API naming, and proof organization also adapt the prior
Tau Ceti formalization in `TauCeti/Algebra/Lie/UniversalEnveloping/Functoriality.lean`.

## Main definitions

* `SymmetricAlgebra.map`: the algebra homomorphism induced by a linear map.
* `SymmetricAlgebra.mapEquiv`: the algebra equivalence induced by a linear equivalence.

## Main results

* `SymmetricAlgebra.map_apply_ι`: evaluation of the induced map on a canonical generator.
* `SymmetricAlgebra.map_unique`: characterization of the induced map by its generators.
* `SymmetricAlgebra.map_id` and `SymmetricAlgebra.map_comp_map`: functoriality laws.

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
theorem map_apply_ι (f : M →ₗ[R] N) (a : M) :
    map R f (ι R M a) = ι R N (f a) := by
  simp [map]

/-- The universal property characterizes the induced map by its values on generators. -/
theorem map_unique (f : M →ₗ[R] N) (g : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R N) :
    (∀ a, g (ι R M a) = ι R N (f a)) ↔ g = map R f := by
  constructor
  · intro h
    apply algHom_ext
    ext a
    -- `algHom_ext` and `ext` leave the generator equality under bundled maps.
    simpa [LinearMap.comp_apply, map_apply_ι] using h a
  · intro h a
    rw [h, map_apply_ι]

/-- The identity linear map induces the identity algebra homomorphism. -/
@[simp]
theorem map_id :
    map R (LinearMap.id (R := R) (M := M)) = AlgHom.id R (SymmetricAlgebra R M) := by
  apply algHom_ext
  ext a
  simp

/-- The induced map commutes with the canonical generator maps. -/
@[simp]
theorem map_comp_ι (f : M →ₗ[R] N) :
    (map R f).toLinearMap ∘ₗ ι R M = ι R N ∘ₗ f := by
  ext a
  simp

/-- Composition of linear maps becomes composition of the induced algebra homomorphisms. -/
@[simp]
theorem map_comp_map (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    (map R g).comp (map R f) = map R (g.comp f) := by
  apply algHom_ext
  ext a
  simp

/-- A left inverse of linear maps induces a left inverse of the corresponding symmetric-algebra
maps. -/
theorem map_leftInverse {f : M →ₗ[R] N} {g : N →ₗ[R] M}
    (h : Function.LeftInverse g f) : Function.LeftInverse (map R g) (map R f) := by
  intro a
  have hmaps : (map R g).comp (map R f) = AlgHom.id R (SymmetricAlgebra R M) := by
    have hgf : g.comp f = LinearMap.id := LinearMap.ext fun x => h x
    rw [map_comp_map, hgf, map_id]
  exact AlgHom.congr_fun hmaps a

/-- A right inverse of linear maps induces a right inverse of the corresponding symmetric-algebra
maps. -/
theorem map_rightInverse {f : M →ₗ[R] N} {g : N →ₗ[R] M}
    (h : Function.RightInverse g f) : Function.RightInverse (map R g) (map R f) :=
  map_leftInverse R (f := g) (g := f) h.leftInverse

/-- A split monomorphism induces an injective map of symmetric algebras. -/
theorem map_injective_of_leftInverse (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (h : Function.LeftInverse g f) : Function.Injective (map R f) :=
  (map_leftInverse R h).injective

/-- A split epimorphism induces a surjective map of symmetric algebras. -/
theorem map_surjective_of_rightInverse (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (h : Function.RightInverse g f) : Function.Surjective (map R f) :=
  (map_rightInverse R h).surjective

/-- A surjective linear map induces a surjective map of symmetric algebras. -/
theorem map_surjective (f : M →ₗ[R] N)
    (h : Function.Surjective f) : Function.Surjective (map R f) := by
  intro b
  induction b using SymmetricAlgebra.induction with
  | algebraMap r =>
      exact ⟨algebraMap R (SymmetricAlgebra R M) r, by simp⟩
  | ι y =>
      obtain ⟨x, rfl⟩ := h y
      exact ⟨ι R M x, by simp⟩
  | mul a b ha hb =>
      obtain ⟨a', ha'⟩ := ha
      obtain ⟨b', hb'⟩ := hb
      exact ⟨a' * b', by simp [ha', hb']⟩
  | add a b ha hb =>
      obtain ⟨a', ha'⟩ := ha
      obtain ⟨b', hb'⟩ := hb
      exact ⟨a' + b', by simp [ha', hb']⟩

/-- A linear equivalence induces an algebra equivalence of symmetric algebras. -/
noncomputable def mapEquiv (e : M ≃ₗ[R] N) :
    SymmetricAlgebra R M ≃ₐ[R] SymmetricAlgebra R N :=
  AlgEquiv.ofAlgHom (map R e.toLinearMap) (map R e.symm.toLinearMap)
    (by rw [map_comp_map, e.comp_symm, map_id])
    (by rw [map_comp_map, e.symm_comp, map_id])

/-- The algebra homomorphism underlying `mapEquiv` is induced by the underlying linear map. -/
@[simp]
theorem mapEquiv_toAlgHom (e : M ≃ₗ[R] N) :
    (mapEquiv R e).toAlgHom = map R e.toLinearMap := by
  rw [mapEquiv, AlgEquiv.toAlgHom_ofAlgHom]

/-- The induced equivalence agrees with the induced algebra map on every element. -/
@[simp]
theorem mapEquiv_apply (e : M ≃ₗ[R] N) (a : SymmetricAlgebra R M) :
    mapEquiv R e a = map R e.toLinearMap a := by
  rw [← AlgEquiv.toAlgHom_apply, mapEquiv_toAlgHom]

/-- The bundled equivalence acts on canonical generators by the underlying linear equivalence. -/
theorem mapEquiv_ι (e : M ≃ₗ[R] N) (a : M) :
    mapEquiv R e (ι R M a) = ι R N (e a) := by
  simp [mapEquiv_apply]

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
  apply AlgEquiv.ext
  intro a
  simp only [AlgEquiv.trans_apply, mapEquiv_apply]
  calc
    _ = ((map R d.toLinearMap).comp (map R e.toLinearMap)) a := by
      rw [AlgHom.comp_apply]
    _ = map R (d.toLinearMap.comp e.toLinearMap) a := by rw [map_comp_map]
    _ = _ := by rw [LinearEquiv.coe_trans]

end SymmetricAlgebra
