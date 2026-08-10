/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.CommHopfAlgCat
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Equivalence
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec

/-!
# Affine group schemes of finite type

This file restricts the anti-equivalence between commutative Hopf algebras and affine group
schemes to the finite-type objects. On the coordinate side, finite type means
`Algebra.FiniteType R H`. On the scheme side, it means that the structural morphism
`G ⟶ Spec R` is locally of finite type. Since the source and target are affine, this is the
usual finite-type condition for an affine group scheme.

The key compatibility theorem is
`TauCeti.algebraFiniteType_iff_locallyOfFiniteType_hopfSpec`: the coordinate algebra `H` is
finitely generated over `R` exactly when the structural morphism of its Hopf spectrum is
locally of finite type. Restricting the existing anti-equivalence along this equality gives

`(FiniteTypeCommHopfAlgCat R)ᵒᵖ ≌ FiniteTypeAffineGroupSchemeCat (CommRingCat.of R)`.

Thus finite type remains a separate object property in both models, as required by the
reductive-groups roadmap, while the dictionary records that the two predicates correspond.

## Main declarations

* `TauCeti.finiteTypeAffineGroupSchemeProperty`: the locally-of-finite-type object property
  on affine group schemes over an affine base.
* `TauCeti.FiniteTypeAffineGroupSchemeCat`: the resulting full subcategory.
* `TauCeti.algebraFiniteType_iff_locallyOfFiniteType_hopfSpec`: compatibility of the
  algebraic and scheme-theoretic finite-type conditions.
* `TauCeti.finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat`: the restricted
  anti-equivalence.
* `TauCeti.finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat.functorCompιIso`:
  after both inclusions, the forward functor is Mathlib's `AlgebraicGeometry.hopfSpec`.

## References

The affine anti-equivalence is `TauCeti.commHopfAlgCatOpEquivAffineGroupSchemeCat`, assembled
from Mathlib's `AlgebraicGeometry.hopfSpec`. The finite-type comparison uses Mathlib's
`AlgebraicGeometry.HasRingHomProperty.Spec_iff` for locally finite-type morphisms and
`RingHom.finiteType_algebraMap`. This is the finite-type predicate synchronization requested
in Layer 0 of `TauCetiRoadmap/ReductiveGroups/README.md`.
-/

public section

namespace TauCeti

open CategoryTheory AlgebraicGeometry Opposite

universe u

private instance locallyOfFiniteType_respectsIso :
    MorphismProperty.RespectsIso (@LocallyOfFiniteType) := by
  rw [HasRingHomProperty.eq_affineLocally @LocallyOfFiniteType]
  exact affineLocally_respectsIso (@RingHom.FiniteType)
    RingHom.finiteType_respectsIso

/-- The object property on affine group schemes over `Spec S` selecting those whose structural
morphism is locally of finite type. Since both the group scheme and the base are affine, these
are precisely the affine group schemes of finite type over `S`. -/
def finiteTypeAffineGroupSchemeProperty (S : CommRingCat.{u}) :
    ObjectProperty (AffineGroupSchemeCat S) :=
  fun G => LocallyOfFiniteType G.obj.X.hom

/-- Membership in the finite-type affine-group-scheme object property. -/
@[simp]
lemma finiteTypeAffineGroupSchemeProperty_iff (S : CommRingCat.{u})
    (G : AffineGroupSchemeCat S) :
    finiteTypeAffineGroupSchemeProperty S G ↔ LocallyOfFiniteType G.obj.X.hom :=
  Iff.rfl

/-- Local finite type of the structural morphism is invariant under isomorphism of affine group
schemes. This lets the predicate restrict equivalences to full subcategories. -/
instance (S : CommRingCat.{u}) :
    (finiteTypeAffineGroupSchemeProperty S).IsClosedUnderIsomorphisms where
  of_iso e hX :=
    (MorphismProperty.over_iso_iff (@LocallyOfFiniteType)
      ((Grp.forget _).mapIso ((affineGroupSchemeProperty S).ι.mapIso e))).mp hX

/-- The category of affine group schemes of finite type over the affine base `Spec S`.

Finite type is kept as an object property rather than included in the definition of an affine
group scheme. -/
abbrev FiniteTypeAffineGroupSchemeCat (S : CommRingCat.{u}) :=
  (finiteTypeAffineGroupSchemeProperty S).FullSubcategory

/-- An object of `FiniteTypeAffineGroupSchemeCat S` has a locally finite-type structural
morphism by construction. -/
instance (G : FiniteTypeAffineGroupSchemeCat S) :
    LocallyOfFiniteType G.obj.obj.X.hom :=
  G.property

/-- A commutative Hopf algebra is finitely generated over its base exactly when the structural
morphism of its Hopf spectrum is locally of finite type.

This is the predicate-level compatibility needed to restrict the affine Hopf/group-scheme
anti-equivalence to finite-type objects. -/
theorem algebraFiniteType_iff_locallyOfFiniteType_hopfSpec
    (R : Type u) [CommRing R] (H : CommHopfAlgCat.{u} R) :
    Algebra.FiniteType R H ↔
      LocallyOfFiniteType
        (((hopfSpec (CommRingCat.of R)).obj (op H)).X.hom) := by
  rw [hopfSpec_obj_X_hom]
  rw [MorphismProperty.cancel_left_of_respectsIso
    (P := @LocallyOfFiniteType) (eqToHom (hopfSpec_obj_X_left R H))]
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.symm

/-- Under the affine Hopf/group-scheme anti-equivalence, the inverse image of the finite-type
scheme property is the finite-type coordinate-algebra property. -/
theorem finiteTypeAffineGroupSchemeProperty_inverseImage
    (R : Type u) [CommRing R] :
    (finiteTypeAffineGroupSchemeProperty (CommRingCat.of R)).inverseImage
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).functor =
      (finiteTypeCommHopfAlgProperty R).op := by
  let Q : ObjectProperty (Grp (Over (Spec (CommRingCat.of R)))) :=
    (MorphismProperty.overObj (@LocallyOfFiniteType)).inverseImage (Grp.forget _)
  let _ : (MorphismProperty.overObj (@LocallyOfFiniteType)
      (X := Spec (CommRingCat.of R))).IsClosedUnderIsomorphisms :=
    MorphismProperty.instIsClosedUnderIsomorphismsOverOverObjOfRespectsIso
  let _ : Q.IsClosedUnderIsomorphisms := by
    unfold Q
    infer_instance
  change (Q.inverseImage (affineGroupSchemeProperty (CommRingCat.of R)).ι).inverseImage
      (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).functor =
    (finiteTypeCommHopfAlgProperty R).op
  apply commHopfAlgCatOpEquivAffineGroupSchemeCat.inverseImage_eq_op
  intro H
  exact algebraFiniteType_iff_locallyOfFiniteType_hopfSpec R H

/-- `Spec` as an anti-equivalence from finite-type commutative `R`-Hopf algebras to affine
group schemes of finite type over `Spec R`.

This is the restriction of `commHopfAlgCatOpEquivAffineGroupSchemeCat` along
`finiteTypeAffineGroupSchemeProperty_inverseImage`. -/
noncomputable def finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat
    (R : Type u) [CommRing R] :
    (FiniteTypeCommHopfAlgCat.{u, u} R)ᵒᵖ ≌
      FiniteTypeAffineGroupSchemeCat (CommRingCat.of R) :=
  commHopfAlgCatOpEquivAffineGroupSchemeCat.restrict (CommRingCat.of R)
    (finiteTypeCommHopfAlgProperty R)
    (finiteTypeAffineGroupSchemeProperty (CommRingCat.of R))
    (finiteTypeAffineGroupSchemeProperty_inverseImage R)

/-- The forward finite-type anti-equivalence, followed by the inclusions into affine group
schemes and then all group schemes, is Mathlib's `hopfSpec` applied after forgetting the
finite-type proof. This is the computation interface for the restricted equivalence. -/
noncomputable def
    finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat.functorCompιIso
    (R : Type u) [CommRing R] :
    (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat R).functor ⋙
          (finiteTypeAffineGroupSchemeProperty (CommRingCat.of R)).ι ⋙
        (affineGroupSchemeProperty (CommRingCat.of R)).ι ≅
      (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} R)
          (CommHopfAlgCat.{u} R)).op ⋙ hopfSpec (CommRingCat.of R) :=
  commHopfAlgCatOpEquivAffineGroupSchemeCat.restrictFunctorCompιIso
    (CommRingCat.of R) (finiteTypeCommHopfAlgProperty R)
    (finiteTypeAffineGroupSchemeProperty (CommRingCat.of R))
    (finiteTypeAffineGroupSchemeProperty_inverseImage R)

end TauCeti
