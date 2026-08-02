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
`AlgebraicGeometry.Spec.mapMulEquiv`. This file gives that result a reusable
Hopf-spectrum-facing boundary, records its two computations, and proves its covariance in
the value algebra and contravariance in the coordinate Hopf algebra.

## Main declarations

* `TauCeti.CommHopfAlgCat.hopfSpecPointsMulEquiv`: convolution points are morphisms into
  the affine Hopf spectrum over the base spectrum.
* `TauCeti.CommHopfAlgCat.hopfSpecPointsMulEquiv_mapValue`: a value-algebra map becomes
  precomposition by the corresponding spectrum morphism.
* `TauCeti.CommHopfAlgCat.hopfSpecPointsMulEquiv_mapDomain`: a coordinate Hopf morphism
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

/-- The convolution group of `A`-valued points of a commutative Hopf algebra `H` is
multiplicatively equivalent to the morphisms over `Spec R` from `Spec A` to `Spec H`.

The target is the underlying object of the affine group scheme
`(AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H)`. Multiplication on
the hom-set is therefore induced by the group-object multiplication dual to the
comultiplication of `H`. -/
noncomputable def hopfSpecPointsMulEquiv
    (H : _root_.CommHopfAlgCat.{u} R) (A : CommAlgCat.{u} R) :
    HopfAlgebra.points (R := R) (H := H) A ≃*
      ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
        (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) :=
  AlgebraicGeometry.Spec.mapMulEquiv

/-- An algebra-valued point is sent to its contravariant spectrum morphism over the base
spectrum. -/
@[simp]
theorem hopfSpecPointsMulEquiv_apply
    (H : _root_.CommHopfAlgCat.{u} R) (A : CommAlgCat.{u} R)
    (p : HopfAlgebra.points (R := R) (H := H) A) :
    hopfSpecPointsMulEquiv H A p =
      (Spec.map (CommRingCat.ofHom p.ofConv.toRingHom)).asOver
        (Spec (CommRingCat.of R)) := by
  rfl

/-- The inverse scheme-points equivalence recovers the map on coordinate rings induced by
the underlying morphism of affine schemes. -/
@[simp]
theorem hopfSpecPointsMulEquiv_symm_apply_toRingHom
    (H : _root_.CommHopfAlgCat.{u} R) (A : CommAlgCat.{u} R)
    (f : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) :
    (↑((hopfSpecPointsMulEquiv H A).symm f).ofConv : H →+* A) =
      (Spec.preimage f.left).hom := by
  rfl

/-- The Hopf-spectrum points equivalence is natural in the value algebra. Postcomposing an
`A`-valued algebra point by `φ : A ⟶ B` corresponds on spectra to precomposing by
`Spec B ⟶ Spec A`. -/
theorem hopfSpecPointsMulEquiv_mapValue
    (H : _root_.CommHopfAlgCat.{u} R) {A B : CommAlgCat.{u} R}
    (φ : A ⟶ B) (p : HopfAlgebra.points (R := R) (H := H) A) :
    hopfSpecPointsMulEquiv H B (HopfAlgebra.mapPoints (H := H) φ p) =
      (Spec.map (CommRingCat.ofHom φ.hom.toRingHom)).asOver
          (Spec (CommRingCat.of R)) ≫
        hopfSpecPointsMulEquiv H A p := by
  apply Over.OverMorphism.ext
  -- On underlying affine schemes this is contravariance of `Spec` applied to the
  -- composite coordinate map `H → A → B`.
  change Spec.map (CommRingCat.ofHom (φ.hom.comp p.ofConv).toRingHom) =
    Spec.map (CommRingCat.ofHom φ.hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom p.ofConv.toRingHom)
  rw [← Spec.map_comp]
  rfl

/-- The Hopf-spectrum points equivalence is contravariantly natural in the coordinate Hopf
algebra. Precomposing a `K`-point by `φ : H ⟶ K` corresponds on spectra to
postcomposing by the group-scheme morphism `Spec K ⟶ Spec H` induced by `hopfSpec`. -/
theorem hopfSpecPointsMulEquiv_mapDomain
    {H K : _root_.CommHopfAlgCat.{u} R} (A : CommAlgCat.{u} R)
    (φ : H ⟶ K) (p : HopfAlgebra.points (R := R) (H := K) A) :
    hopfSpecPointsMulEquiv H A ((mapPointsFunctor φ).app A p) =
      hopfSpecPointsMulEquiv K A p ≫
        ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map φ.op).hom.hom := by
  apply Over.OverMorphism.ext
  -- The underlying map of `hopfSpec.map φ.op` is definitionally `Spec.map φ`; the
  -- square is therefore contravariance of `Spec` for `H → K → A`.
  change Spec.map (CommRingCat.ofHom (p.ofConv.comp φ.hom).toRingHom) =
    Spec.map (CommRingCat.ofHom p.ofConv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom φ.hom.toAlgHom.toRingHom)
  rw [← Spec.map_comp]
  rfl

end CommHopfAlgCat

end TauCeti
