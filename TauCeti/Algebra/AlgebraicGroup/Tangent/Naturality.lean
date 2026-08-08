/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Adjoint

/-!
# Naturality of the tangent and adjoint actions in the coefficient algebra

For a Hopf algebra `A` over `R`, the tangent space is naturally a functor of the
coefficient algebra:

`B ↦ Derivation R A (Bialgebra.CounitAlgebra R A B)`.

An `R`-algebra homomorphism `φ : B →ₐ[R] C` postcomposes a counit-valued
derivation. This file packages that operation as `Derivation.mapValue`, proves its
functoriality, and shows that it intertwines the adjoint actions at `B` and `C`.
Together, these statements make the valuewise representations in
`Tangent.Adjoint` into a natural action on the Lie functor.

## Main declarations

* `TauCeti.Bialgebra.CounitAlgebra.mapAlgHom`: the coefficient algebra map.
* `TauCeti.Bialgebra.CounitAlgebra.map`: the same map, linear over the Hopf algebra
  through the counit actions.
* `TauCeti.Derivation.mapValue`: postcomposition of counit-valued derivations.
* `TauCeti.Derivation.mapValue_adDerivation`: the adjoint action commutes with
  change of coefficient algebra.

The Lie-bracket compatibility, which requires additive inverses, is in
`Tangent.Lie.Naturality`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §14.
-/

public section

namespace TauCeti

open _root_.Coalgebra WithConv

namespace Bialgebra.CounitAlgebra

variable {R A B C : Type*} [CommSemiring R] [CommSemiring A] [Bialgebra R A]
  [CommSemiring B] [Algebra R B] [CommSemiring C] [Algebra R C]

/-- An algebra homomorphism of coefficients, transported to the counit coefficient
algebras. -/
noncomputable def mapAlgHom (phi : B →ₐ[R] C) :
    CounitAlgebra R A B →ₐ[R] CounitAlgebra R A C :=
  (algEquivSelf R A C).symm.toAlgHom.comp (phi.comp (algEquivSelf R A B).toAlgHom)

omit [CommSemiring A] [Bialgebra R A] in
/-- The coefficient algebra map is the original map under the canonical
identifications with its source and target. -/
lemma algEquivSelf_mapAlgHom (phi : B →ₐ[R] C) (b : CounitAlgebra R A B) :
    algEquivSelf R A C (mapAlgHom (A := A) phi b) =
      phi (algEquivSelf R A B b) := by
  -- The public equivalences are the API for crossing the coefficient synonyms;
  -- `change` exposes the composite through those equivalences once.
  change algEquivSelf R A C
      ((algEquivSelf R A C).symm (phi (algEquivSelf R A B b))) = _
  rw [AlgEquiv.apply_symm_apply]

omit [CommSemiring A] [Bialgebra R A] in
/-- The identity coefficient homomorphism induces the identity homomorphism of
counit coefficient algebras. -/
@[simp]
lemma mapAlgHom_id :
    mapAlgHom (A := A) (AlgHom.id R B) =
      AlgHom.id R (CounitAlgebra R A B) := by
  ext b
  apply (algEquivSelf R A B).injective
  rw [algEquivSelf_mapAlgHom, AlgHom.id_apply, AlgHom.id_apply]

omit [CommSemiring A] [Bialgebra R A] in
/-- Homomorphisms of counit coefficient algebras preserve composition. -/
@[simp]
lemma mapAlgHom_comp {D : Type*} [CommSemiring D] [Algebra R D]
    (psi : C →ₐ[R] D) (phi : B →ₐ[R] C) :
    mapAlgHom (A := A) (psi.comp phi) =
      (mapAlgHom (A := A) psi).comp (mapAlgHom (A := A) phi) := by
  ext b
  apply (algEquivSelf R A D).injective
  rw [algEquivSelf_mapAlgHom, AlgHom.comp_apply, AlgHom.comp_apply,
    algEquivSelf_mapAlgHom, algEquivSelf_mapAlgHom]

/-- An algebra map between coefficient algebras, regarded as a linear map for the
`A`-module structures induced by the counit. -/
noncomputable def map (phi : B →ₐ[R] C) :
    CounitAlgebra R A B →ₗ[A] CounitAlgebra R A C where
  toFun := mapAlgHom (A := A) phi
  map_add' := map_add (mapAlgHom (A := A) phi)
  map_smul' a b := by
    have hB : algEquivSelf R A B (algebraMap A (CounitAlgebra R A B) a) =
        algebraMap R B (counit a) := calc
      _ = algEquivSelf R A B
          (algebraMap R (CounitAlgebra R A B) (counit a)) :=
        congrArg (algEquivSelf R A B) (algebraMap_apply R A B a)
      _ = _ := (algEquivSelf R A B).commutes (counit a)
    have hC : algEquivSelf R A C (algebraMap A (CounitAlgebra R A C) a) =
        algebraMap R C (counit a) := calc
      _ = algEquivSelf R A C
          (algebraMap R (CounitAlgebra R A C) (counit a)) :=
        congrArg (algEquivSelf R A C) (algebraMap_apply R A C a)
      _ = _ := (algEquivSelf R A C).commutes (counit a)
    rw [Algebra.smul_def, Algebra.smul_def]
    apply (algEquivSelf R A C).injective
    rw [algEquivSelf_mapAlgHom, map_mul, map_mul, map_mul, algEquivSelf_mapAlgHom,
      hB, RingHom.id_apply, hC, phi.commutes]

/-- The linear coefficient map has the same underlying function as the coefficient
algebra map. -/
@[simp]
lemma map_apply (phi : B →ₐ[R] C) (b : CounitAlgebra R A B) :
    map (A := A) phi b = mapAlgHom (A := A) phi b := by
  change mapAlgHom (A := A) phi b = _
  rfl

/-- The identity algebra homomorphism induces the identity coefficient map. -/
@[simp]
lemma map_id :
    map (A := A) (AlgHom.id R B) =
      LinearMap.id (R := A) (M := CounitAlgebra R A B) := by
  ext b
  apply (algEquivSelf R A B).injective
  rw [map_apply, algEquivSelf_mapAlgHom, LinearMap.id_apply, AlgHom.id_apply]

/-- Coefficient maps preserve composition. -/
@[simp]
lemma map_comp {D : Type*} [CommSemiring D] [Algebra R D]
    (psi : C →ₐ[R] D) (phi : B →ₐ[R] C) :
    map (A := A) (psi.comp phi) =
      (map (A := A) psi).comp (map (A := A) phi) := by
  ext b
  apply (algEquivSelf R A D).injective
  rw [map_apply, algEquivSelf_mapAlgHom, LinearMap.comp_apply, map_apply,
    algEquivSelf_mapAlgHom, map_apply, algEquivSelf_mapAlgHom, AlgHom.comp_apply]

end Bialgebra.CounitAlgebra

namespace Derivation

variable {R A B C : Type*} [CommSemiring R] [CommSemiring A] [HopfAlgebra R A]
  [CommSemiring B] [Algebra R B] [CommSemiring C] [Algebra R C]

/-- Postcomposition of a counit-valued derivation along an algebra homomorphism of
coefficients. This is the functorial map on tangent vectors. -/
noncomputable def mapValue (phi : B →ₐ[R] C) :
    Derivation R A (Bialgebra.CounitAlgebra R A B) →ₗ[R]
      Derivation R A (Bialgebra.CounitAlgebra R A C) :=
  (Bialgebra.CounitAlgebra.map (A := A) phi).compDer |>.restrictScalars R

/-- Postcomposition of a counit-valued derivation acts pointwise. -/
@[simp]
lemma mapValue_apply (phi : B →ₐ[R] C)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) (a : A) :
    mapValue phi d a = Bialgebra.CounitAlgebra.mapAlgHom (A := A) phi (d a) := by
  change Bialgebra.CounitAlgebra.map (A := A) phi (d a) = _
  rw [Bialgebra.CounitAlgebra.map_apply]

/-- On underlying linear maps, change of coefficients is postcomposition by the
coefficient algebra map. -/
@[simp]
lemma coe_mapValue_linearMap (phi : B →ₐ[R] C)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    ↑(mapValue phi d) =
      (Bialgebra.CounitAlgebra.mapAlgHom (A := A) phi).toLinearMap.comp
        (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B) := by
  ext a
  -- Extensionality presents the left side through its underlying linear map;
  -- `mapValue_apply` is stated through the derivation coercion.
  change mapValue phi d a = _
  rw [mapValue_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rfl

/-- Postcomposition by the identity is the identity on counit-valued derivations. -/
@[simp]
theorem mapValue_id :
    mapValue (A := A) (AlgHom.id R B) =
      LinearMap.id (R := R)
        (M := Derivation R A (Bialgebra.CounitAlgebra R A B)) := by
  ext d a
  apply (Bialgebra.CounitAlgebra.algEquivSelf R A B).injective
  rw [mapValue_apply, Bialgebra.CounitAlgebra.algEquivSelf_mapAlgHom,
    LinearMap.id_apply, AlgHom.id_apply]

/-- Postcomposition of counit-valued derivations preserves composition. -/
@[simp]
theorem mapValue_comp {D : Type*} [CommSemiring D] [Algebra R D]
    (psi : C →ₐ[R] D) (phi : B →ₐ[R] C) :
    mapValue (A := A) (psi.comp phi) =
      (mapValue (A := A) psi).comp (mapValue (A := A) phi) := by
  ext d a
  apply (Bialgebra.CounitAlgebra.algEquivSelf R A D).injective
  rw [mapValue_apply, Bialgebra.CounitAlgebra.algEquivSelf_mapAlgHom,
    LinearMap.comp_apply, mapValue_apply, mapValue_apply,
    Bialgebra.CounitAlgebra.algEquivSelf_mapAlgHom,
    Bialgebra.CounitAlgebra.algEquivSelf_mapAlgHom, AlgHom.comp_apply]

/-- **The adjoint action is natural in the coefficient algebra.** Mapping a point and
a tangent vector along `phi` and then applying the adjoint action gives the same
result as applying the action first and postcomposing the resulting derivation. -/
theorem mapValue_adDerivation (phi : B →ₐ[R] C)
    (g : WithConv (A →ₐ[R] Bialgebra.CounitAlgebra R A B))
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    mapValue phi (adDerivation B g d) =
      adDerivation C
        (AlgHom.mapValue (R := R) (H := A)
          (Bialgebra.CounitAlgebra.mapAlgHom
            (R := R) (A := A) (B := B) (C := C) phi) g)
        (mapValue phi d) := by
  ext a
  rw [mapValue_apply, adDerivation_apply, adDerivation_apply]
  -- The algebra-hom coercion and its underlying linear map agree pointwise; the
  -- convolution distribution lemma is stated for the latter.
  change (Bialgebra.CounitAlgebra.mapAlgHom (A := A) phi).toLinearMap
      ((toConv g.ofConv.toLinearMap *
          toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
          toConv ((g⁻¹).ofConv.toLinearMap)).ofConv a) = _
  rw [← LinearMap.comp_apply
    (Bialgebra.CounitAlgebra.mapAlgHom (A := A) phi).toLinearMap]
  rw [LinearMap.algHom_comp_convMul_distrib, LinearMap.algHom_comp_convMul_distrib]
  simp only [AlgHom.mapValue_apply, coe_mapValue_linearMap, AlgHom.comp_toLinearMap,
    toConv_ofConv]
  rfl

/-- The valuewise adjoint representations intertwine the functorial maps on points
and tangent vectors. -/
theorem mapValue_adRepresentation (phi : B →ₐ[R] C)
    (g : WithConv (A →ₐ[R] Bialgebra.CounitAlgebra R A B))
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    mapValue phi (adRepresentation B g d) =
      adRepresentation C
        (AlgHom.mapValue (R := R) (H := A)
          (Bialgebra.CounitAlgebra.mapAlgHom
            (R := R) (A := A) (B := B) (C := C) phi) g)
        (mapValue phi d) := by
  rw [adRepresentation_apply, adRepresentation_apply, mapValue_adDerivation]

end Derivation

end TauCeti
