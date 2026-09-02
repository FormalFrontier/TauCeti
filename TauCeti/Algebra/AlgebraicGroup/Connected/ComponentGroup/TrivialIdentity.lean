/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Representable
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic

/-!
# Finite groups with trivial identity component

Let `H` be the coordinate Hopf algebra of a finite-type affine group over an algebraically
closed field. If its identity component is the trivial subgroup scheme, then the canonical
component morphism identifies the group with the finite constant group of connected components.
In particular, `H` is finite-dimensional over the ground field.

The proof uses the existing description of the component morphism. It is surjective on points
over every commutative test algebra, and its scheme-theoretic kernel is the identity component.
When that kernel is trivial, the point map is also injective. Full faithfulness of the functor of
points then promotes the pointwise isomorphism to an isomorphism of coordinate Hopf algebras.

## Main declarations

* `componentCoordinateIsoOfIdentityComponentHopfIdealEqAugmentation`: a finite-type affine group
  with trivial identity component is the constant group on its connected components.
* `moduleFinite_of_identityComponentHopfIdeal_eq_augmentation`: its coordinate algebra is
  finite-dimensional.
* `algebraEtale_of_identityComponentHopfIdeal_eq_augmentation`: its coordinate algebra is
  etale.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 6.7.

This is the component-group input for the Layer 6 theorem that the center of a semisimple affine
group is finite. Applied to the reduced center, it turns the vanishing of that smooth group's
identity component into finiteness; finiteness of the original center then follows by controlling
its nilpotent thickening.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem componentPointsHom_injective_of_identityComponentHopfIdeal_eq_augmentation
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H) =
      HopfIdeal.augmentation k H) (A : CommAlgCat.{u} k) :
    Function.Injective (componentPointsHom H A) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rw [componentPointsHom_apply] at hg
  have hmem : g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
      (CommHopfAlgCat.kernelHopfIdeal (componentCoordinateHom H)) A :=
    (CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff
      (componentCoordinateHom H) A g).mp hg
  rw [kernelHopfIdeal_componentCoordinateHom, hH] at hmem
  exact CommHopfAlgCat.eq_one_of_mem_quotientPointsSubgroup_augmentation H.obj A hmem

private theorem componentPointsHom_bijective_of_identityComponentHopfIdeal_eq_augmentation
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H) =
      HopfIdeal.augmentation k H) (A : CommAlgCat.{u} k) :
    Function.Bijective (componentPointsHom H A) :=
  ⟨componentPointsHom_injective_of_identityComponentHopfIdeal_eq_augmentation H hH A,
    componentPointsHom_surjective H A⟩

private theorem
    isIso_mapPointsFunctor_componentCoordinateHom_of_identityComponentHopfIdealEqAugmentation
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H) =
      HopfIdeal.augmentation k H) :
    IsIso (CommHopfAlgCat.mapPointsFunctor.{u, u, u} (componentCoordinateHom H)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro A
  apply (ConcreteCategory.isIso_iff_bijective _).2
  have heq (g : HopfAlgebra.points (R := k) (H := H) A) :
      (CommHopfAlgCat.mapPointsFunctor (componentCoordinateHom H)).app A g =
        componentPointsHom H A g := by
    rw [CommHopfAlgCat.mapPointsFunctor_app_apply, componentPointsHom_apply]
  have hb :=
    componentPointsHom_bijective_of_identityComponentHopfIdeal_eq_augmentation H hH A
  constructor
  · intro x y hxy
    apply hb.1
    rw [← heq x, ← heq y]
    exact hxy
  · intro y
    obtain ⟨x, hx⟩ := hb.2 y
    exact ⟨x, (heq x).trans hx⟩

private theorem
    isIso_componentCoordinateHom_of_identityComponentHopfIdeal_eq_augmentation
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H) =
      HopfIdeal.augmentation k H) :
    IsIso (componentCoordinateHom H) := by
  let _ :=
    isIso_mapPointsFunctor_componentCoordinateHom_of_identityComponentHopfIdealEqAugmentation
      H hH
  exact CommHopfAlgCat.isIso_of_isIso_mapPointsFunctor (componentCoordinateHom H)

/-- A finite-type affine group over an algebraically closed field with trivial identity
component is canonically the constant group on the connected components of its spectrum. -/
noncomputable def componentCoordinateIsoOfIdentityComponentHopfIdealEqAugmentation
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H) =
      HopfIdeal.augmentation k H) :
    CommHopfAlgCat.of k
        (ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))) ≅ H.obj := by
  let _ : IsIso (componentCoordinateHom H) :=
    isIso_componentCoordinateHom_of_identityComponentHopfIdeal_eq_augmentation H hH
  exact asIso (componentCoordinateHom H)

/-- The forward morphism of the component-coordinate isomorphism is the canonical component
coordinate morphism. -/
@[simp]
theorem componentCoordinateIsoOfIdentityComponentHopfIdealEqAugmentation_hom
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H) =
      HopfIdeal.augmentation k H) :
    (componentCoordinateIsoOfIdentityComponentHopfIdealEqAugmentation H hH).hom =
      componentCoordinateHom H := by
  rw [componentCoordinateIsoOfIdentityComponentHopfIdealEqAugmentation, asIso_hom]

/-- The coordinate algebra of a finite-type affine group over an algebraically closed field is
finite-dimensional when its identity component is the trivial subgroup scheme. -/
theorem moduleFinite_of_identityComponentHopfIdeal_eq_augmentation
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H) =
      HopfIdeal.augmentation k H) :
    Module.Finite k H := by
  let e := componentCoordinateIsoOfIdentityComponentHopfIdealEqAugmentation H hH
  let eLinear : ConstantGroup.coordinateRing k
      (ConnectedComponents (PrimeSpectrum H)) ≃ₗ[k] H :=
    LinearEquiv.ofBijective e.hom.hom.toLinearMap
      (ConcreteCategory.bijective_of_isIso e.hom)
  exact Module.Finite.equiv eLinear

/-- The coordinate algebra of a finite-type affine group over an algebraically closed field is
etale when its identity component is the trivial subgroup scheme. -/
theorem algebraEtale_of_identityComponentHopfIdeal_eq_augmentation
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H) =
      HopfIdeal.augmentation k H) :
    Algebra.Etale k H := by
  let e := componentCoordinateIsoOfIdentityComponentHopfIdealEqAugmentation H hH
  let eAlg : ConstantGroup.coordinateRing k
      (ConnectedComponents (PrimeSpectrum H)) ≃ₐ[k] H :=
    AlgEquiv.ofBijective e.hom.hom.toAlgHom
      (ConcreteCategory.bijective_of_isIso e.hom)
  exact Algebra.Etale.of_equiv eAlg

end TauCeti.FiniteTypeCommHopfAlgCat
