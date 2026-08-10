/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Basic
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec

/-!
# Smooth affine group schemes

This file records smoothness of affine group schemes as an object property and compares it with
smoothness of their coordinate Hopf algebras. On the coordinate side, smoothness is
`Algebra.Smooth R H`. On the scheme side, it is smoothness of the structural morphism
`G ⟶ Spec R`.

The key comparison is `TauCeti.algebraSmooth_iff_smooth_hopfSpec`: a commutative Hopf algebra is
smooth over its base exactly when the structural morphism of its Hopf spectrum is smooth.
Smoothness remains a separate object property rather than being built into the definition of an
affine group scheme, so finite-type group schemes that are non-smooth over a characteristic-`p`
base, such as `μₚ` and `αₚ`, remain in the ambient category.

## Main declarations

* `TauCeti.smoothAffineGroupSchemeProperty`: the smooth structural-morphism property on affine
  group schemes.
* `TauCeti.algebraSmooth_iff_smooth_hopfSpec`: compatibility of the algebraic and
  scheme-theoretic smoothness conditions.

## References

The comparison uses Mathlib's `AlgebraicGeometry.hopfSpec`,
`AlgebraicGeometry.HasRingHomProperty.Spec_iff`, and `RingHom.smooth_algebraMap`. This is the
explicit smoothness predicate requested in the standing hypotheses of the ReductiveGroups
roadmap.
-/

public section

namespace TauCeti

open CategoryTheory AlgebraicGeometry Opposite

universe u

private instance smooth_respectsIso :
    MorphismProperty.RespectsIso (@Smooth) := by
  rw [HasRingHomProperty.eq_affineLocally @Smooth]
  exact affineLocally_respectsIso (@RingHom.Smooth) RingHom.Smooth.respectsIso

/-- The object property on affine group schemes over `Spec S` selecting those whose structural
morphism is smooth. -/
def smoothAffineGroupSchemeProperty (S : CommRingCat.{u}) :
    ObjectProperty (AffineGroupSchemeCat S) :=
  fun G => Smooth G.obj.X.hom

/-- Membership in the smooth affine-group-scheme object property. -/
@[simp]
lemma smoothAffineGroupSchemeProperty_iff (S : CommRingCat.{u})
    (G : AffineGroupSchemeCat S) :
    smoothAffineGroupSchemeProperty S G ↔ Smooth G.obj.X.hom :=
  Iff.rfl

/-- A commutative Hopf algebra is smooth over its base exactly when the structural morphism of
its Hopf spectrum is smooth.

This is the predicate-level compatibility needed to restrict the affine Hopf/group-scheme
anti-equivalence to smooth objects. -/
theorem algebraSmooth_iff_smooth_hopfSpec
    (R : Type u) [CommRing R] (H : CommHopfAlgCat.{u} R) :
    Algebra.Smooth R H ↔
      Smooth (((hopfSpec (CommRingCat.of R)).obj (op H)).X.hom) := by
  rw [hopfSpec_obj_X_hom]
  rw [MorphismProperty.cancel_left_of_respectsIso
    (P := @Smooth) (eqToHom (hopfSpec_obj_X_left R H))]
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.symm

end TauCeti
