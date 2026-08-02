/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Basic

/-!
# Scheme-valued points of affine Hopf spectra

For a commutative ring `R`, a same-universe commutative Hopf algebra `H`, and a
same-universe commutative `R`-algebra `A`, this file identifies the convolution group
`WithConv (H →ₐ[R] A)` with the group of morphisms over `Spec R` from `Spec A` into
`Spec H`.

The group law on the scheme side is the pointwise group law induced by the group object
represented by `H`; the source `Spec A` need not itself be a group object. No
cocommutativity assumption is made, so the resulting group of points need not be
commutative. The target `(Spec H).asOver (Spec R)` below is definitionally the underlying
object of `(AlgebraicGeometry.hopfSpec R).obj (Opposite.op H)`.

The equivalence and its multiplicativity are Mathlib's
`AlgebraicGeometry.Spec.mapMulEquiv`. This file proves its covariance in the value algebra
and contravariance in the coordinate Hopf algebra.

## Main declarations

* `TauCeti.CommHopfAlgCat.mapMulEquiv_mapValue`: a value-algebra map becomes
  precomposition by the corresponding spectrum morphism.
* `TauCeti.CommHopfAlgCat.mapMulEquiv_mapDomain`: a coordinate Hopf morphism
  becomes postcomposition by its contravariant `hopfSpec` image.
-/

public section

open CategoryTheory WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti

universe u

namespace CommHopfAlgCat

open AlgebraicGeometry

variable {R : Type u} [CommRing R]

private lemma mapMulEquiv_left
    {S T : Type u} [CommRing S] [CommRing T] [Bialgebra R S] [Algebra R T]
    (f : WithConv (S →ₐ[R] T)) :
    (AlgebraicGeometry.Spec.mapMulEquiv f).left =
      Spec.map (CommRingCat.ofHom f.ofConv.toRingHom) :=
  rfl

private lemma hopfSpec_map_left
    {H K : _root_.CommHopfAlgCat.{u} R} (φ : H ⟶ K) :
    ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map φ.op).hom.hom.left =
      Spec.map (CommRingCat.ofHom φ.hom.toAlgHom.toRingHom) :=
  rfl

/-- Mathlib's spectrum-points equivalence is natural in the value algebra. Postcomposing
an `A`-valued algebra point by `φ : A ⟶ B` corresponds on spectra to precomposing by
`Spec B ⟶ Spec A`. -/
theorem mapMulEquiv_mapValue
    (H : _root_.CommHopfAlgCat.{u} R) {A B : CommAlgCat.{u} R}
    (φ : A ⟶ B) (p : HopfAlgebra.points (R := R) (H := H) A) :
    AlgebraicGeometry.Spec.mapMulEquiv (HopfAlgebra.mapPoints (H := H) φ p) =
      (Spec.map (CommRingCat.ofHom φ.hom.toRingHom)).asOver
          (Spec (CommRingCat.of R)) ≫
        AlgebraicGeometry.Spec.mapMulEquiv p := by
  rw [HopfAlgebra.mapPoints_apply]
  apply Over.OverMorphism.ext
  erw [Over.comp_left]
  simp only [mapMulEquiv_left, OverClass.asOverHom_left]
  erw [← Spec.map_comp]
  rfl

/-- Mathlib's spectrum-points equivalence is contravariantly natural in the coordinate
Hopf algebra. Precomposing a `K`-point by `φ : H ⟶ K` corresponds on spectra to
postcomposing by the group-scheme morphism `Spec K ⟶ Spec H` induced by `hopfSpec`. -/
theorem mapMulEquiv_mapDomain
    {H K : _root_.CommHopfAlgCat.{u} R} (A : CommAlgCat.{u} R)
    (φ : H ⟶ K) (p : HopfAlgebra.points (R := R) (H := K) A) :
    AlgebraicGeometry.Spec.mapMulEquiv ((mapPointsFunctor φ).app A p) =
      AlgebraicGeometry.Spec.mapMulEquiv p ≫
        ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map φ.op).hom.hom := by
  rw [mapPointsFunctor_app_apply]
  apply Over.OverMorphism.ext
  erw [Over.comp_left]
  simp only [mapMulEquiv_left, hopfSpec_map_left]
  erw [← Spec.map_comp]
  rfl

end CommHopfAlgCat

end TauCeti
