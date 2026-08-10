/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Equivalence
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec

/-!
# Smooth affine group schemes

This file restricts the anti-equivalence between commutative Hopf algebras and affine group
schemes to the smooth objects. On the coordinate side, smoothness is `Algebra.Smooth R H`. On
the scheme side, it is smoothness of the structural morphism `G ⟶ Spec R`.

The key comparison is `TauCeti.algebraSmooth_iff_smooth_hopfSpec`: a commutative Hopf algebra is
smooth over its base exactly when the structural morphism of its Hopf spectrum is smooth. It
restricts the existing affine anti-equivalence to

`(SmoothCommHopfAlgCat R)ᵒᵖ ≌ SmoothAffineGroupSchemeCat (CommRingCat.of R)`.

Smoothness remains a separate object property in both models. In particular it is not built into
the definition of an affine group scheme, so finite-type group schemes that are non-smooth over a
characteristic-`p` base, such as `μₚ` and `αₚ`, remain in the ambient category.

## Main declarations

* `TauCeti.smoothAffineGroupSchemeProperty`: the smooth structural-morphism property on affine
  group schemes.
* `TauCeti.algebraSmooth_iff_smooth_hopfSpec`: compatibility of the algebraic and
  scheme-theoretic smoothness conditions.
* `TauCeti.smoothCommHopfAlgCatOpEquivSmoothAffineGroupSchemeCat`: the restricted
  anti-equivalence.

## References

The affine anti-equivalence is `TauCeti.commHopfAlgCatOpEquivAffineGroupSchemeCat`, assembled
from Mathlib's `AlgebraicGeometry.hopfSpec`. The smoothness comparison uses Mathlib's
`AlgebraicGeometry.HasRingHomProperty.Spec_iff` and `RingHom.smooth_algebraMap`. The organization
mirrors the companion finite-type restriction in Tau Ceti PR #2556. This is the smoothness
predicate synchronization requested in Layer 0 of the ReductiveGroups roadmap.
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
  (MorphismProperty.overObj (@Smooth)).inverseImage
    ((affineGroupSchemeProperty S).ι ⋙ Grp.forget _)

/-- Membership in the smooth affine-group-scheme object property. -/
@[simp]
lemma smoothAffineGroupSchemeProperty_iff (S : CommRingCat.{u})
    (G : AffineGroupSchemeCat S) :
    smoothAffineGroupSchemeProperty S G ↔ Smooth G.obj.X.hom :=
  Iff.rfl

instance (S : CommRingCat.{u}) :
    (smoothAffineGroupSchemeProperty S).IsClosedUnderIsomorphisms := by
  unfold smoothAffineGroupSchemeProperty
  let _ : (MorphismProperty.overObj (@Smooth)
      (X := Spec S)).IsClosedUnderIsomorphisms :=
    MorphismProperty.instIsClosedUnderIsomorphismsOverOverObjOfRespectsIso
  infer_instance

/-- The category of smooth affine group schemes over the affine base `Spec S`.

Smoothness is kept as an object property rather than included in the definition of an affine
group scheme. -/
abbrev SmoothAffineGroupSchemeCat (S : CommRingCat.{u}) :=
  (smoothAffineGroupSchemeProperty S).FullSubcategory

/-- An object of `SmoothAffineGroupSchemeCat S` has a smooth structural morphism by
construction. -/
instance (G : SmoothAffineGroupSchemeCat S) : Smooth G.obj.obj.X.hom :=
  (smoothAffineGroupSchemeProperty_iff S G.obj).mp G.property

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

/-- Under the affine Hopf/group-scheme anti-equivalence, the inverse image of the smooth scheme
property is the smooth coordinate-algebra property. -/
theorem smoothAffineGroupSchemeProperty_inverseImage
    (R : Type u) [CommRing R] :
    (smoothAffineGroupSchemeProperty (CommRingCat.of R)).inverseImage
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).functor =
      (smoothCommHopfAlgProperty R).op := by
  let Q : ObjectProperty (Grp (Over (Spec (CommRingCat.of R)))) :=
    (MorphismProperty.overObj (@Smooth)).inverseImage (Grp.forget _)
  let _ : (MorphismProperty.overObj (@Smooth)
      (X := Spec (CommRingCat.of R))).IsClosedUnderIsomorphisms :=
    MorphismProperty.instIsClosedUnderIsomorphismsOverOverObjOfRespectsIso
  let _ : Q.IsClosedUnderIsomorphisms := by
    unfold Q
    infer_instance
  -- Unfold the scheme-side predicate to the ambient group-scheme property `Q`: this is the form
  -- expected by the generic inverse-image comparison theorem.
  change (Q.inverseImage (affineGroupSchemeProperty (CommRingCat.of R)).ι).inverseImage
      (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).functor =
    (smoothCommHopfAlgProperty R).op
  apply commHopfAlgCatOpEquivAffineGroupSchemeCat.inverseImage_eq_op
  intro H
  rw [smoothCommHopfAlgProperty_iff]
  exact algebraSmooth_iff_smooth_hopfSpec R H

/-- `Spec` as an anti-equivalence from smooth commutative `R`-Hopf algebras to smooth affine
group schemes over `Spec R`.

This is the restriction of `commHopfAlgCatOpEquivAffineGroupSchemeCat` along
`smoothAffineGroupSchemeProperty_inverseImage`. -/
noncomputable def smoothCommHopfAlgCatOpEquivSmoothAffineGroupSchemeCat
    (R : Type u) [CommRing R] :
    (SmoothCommHopfAlgCat.{u, u} R)ᵒᵖ ≌ SmoothAffineGroupSchemeCat (CommRingCat.of R) :=
  commHopfAlgCatOpEquivAffineGroupSchemeCat.restrict (CommRingCat.of R)
    (smoothCommHopfAlgProperty R)
    (smoothAffineGroupSchemeProperty (CommRingCat.of R))
    (smoothAffineGroupSchemeProperty_inverseImage R)

/-- The forward smooth anti-equivalence, followed by the inclusions into affine group schemes
and then all group schemes, is Mathlib's `hopfSpec` applied after forgetting the smoothness proof.
This is the computation interface for the restricted equivalence. -/
noncomputable def smoothCommHopfAlgCatOpEquivSmoothAffineGroupSchemeCat.functorCompιIso
    (R : Type u) [CommRing R] :
    (smoothCommHopfAlgCatOpEquivSmoothAffineGroupSchemeCat R).functor ⋙
          (smoothAffineGroupSchemeProperty (CommRingCat.of R)).ι ⋙
        (affineGroupSchemeProperty (CommRingCat.of R)).ι ≅
      (smoothCommHopfAlgProperty R).ι.op ⋙ hopfSpec (CommRingCat.of R) :=
  commHopfAlgCatOpEquivAffineGroupSchemeCat.restrictFunctorCompιIso
    (CommRingCat.of R) (smoothCommHopfAlgProperty R)
    (smoothAffineGroupSchemeProperty (CommRingCat.of R))
    (smoothAffineGroupSchemeProperty_inverseImage R)

end TauCeti
