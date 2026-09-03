/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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
* `TauCeti.finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat.functorObjIso`:
  the corresponding object-level isomorphism with the bundled Hopf spectrum.
* `TauCeti.finiteType_objectProperty_iff_coordinate`: transport of an isomorphism-invariant
  object property through the finite-type anti-equivalence.

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
abbrev FiniteTypeAffineGroupSchemeCat (S : CommRingCat.{u}) : Type _ :=
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
  ext H
  let G : AffineGroupSchemeCat (CommRingCat.of R) :=
    ⟨(hopfSpec (CommRingCat.of R)).obj H, by
      apply (affineGroupSchemeProperty_iff _).mpr
      rw [← essImage_hopfSpec]
      exact ⟨H, ⟨Iso.refl _⟩⟩⟩
  let e : (commHopfAlgCatOpEquivAffineGroupSchemeCat
      (CommRingCat.of R)).functor.obj H ≅ G :=
    (affineGroupSchemeProperty (CommRingCat.of R)).ι.preimageIso
      ((commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
        (CommRingCat.of R)).app H)
  rw [ObjectProperty.prop_inverseImage_iff,
    finiteTypeAffineGroupSchemeProperty_iff, ObjectProperty.op_iff,
    finiteTypeCommHopfAlgProperty_iff]
  constructor
  · intro h
    have hG : finiteTypeAffineGroupSchemeProperty (CommRingCat.of R) G :=
      (finiteTypeAffineGroupSchemeProperty (CommRingCat.of R)).prop_of_iso e h
    exact (algebraFiniteType_iff_locallyOfFiniteType_hopfSpec R H.unop).mpr hG
  · intro h
    apply (finiteTypeAffineGroupSchemeProperty (CommRingCat.of R)).prop_of_iso e.symm
    exact (algebraFiniteType_iff_locallyOfFiniteType_hopfSpec R H.unop).mp h

/-- `Spec` as an anti-equivalence from finite-type commutative `R`-Hopf algebras to affine
group schemes of finite type over `Spec R`.

This is the restriction of `commHopfAlgCatOpEquivAffineGroupSchemeCat` along
`finiteTypeAffineGroupSchemeProperty_inverseImage`. -/
noncomputable def finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat
    (R : Type u) [CommRing R] :
    (FiniteTypeCommHopfAlgCat.{u, u} R)ᵒᵖ ≌
      FiniteTypeAffineGroupSchemeCat (CommRingCat.of R) :=
  (ObjectProperty.opEquivalence (finiteTypeCommHopfAlgProperty R)).symm.trans <|
    (commHopfAlgCatOpEquivAffineGroupSchemeCat
      (CommRingCat.of R)).congrFullSubcategory
        (finiteTypeAffineGroupSchemeProperty_inverseImage R)

/-- The forward restricted equivalence followed by the finite-type inclusion is definitionally
the unrestricted equivalence applied after forgetting the finite-type proof. This private
isomorphism isolates the representation boundary of `opEquivalence`, `trans`, and
`congrFullSubcategory` from the public compatibility isomorphism below. -/
private noncomputable def
    finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCatFunctorCompιIso
    (R : Type u) [CommRing R] :
    (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat R).functor ⋙
        (finiteTypeAffineGroupSchemeProperty (CommRingCat.of R)).ι ≅
      (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} R)
          (CommHopfAlgCat.{u} R)).op ⋙
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).functor :=
  Iso.refl _

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
  Functor.isoWhiskerRight
      (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCatFunctorCompιIso R)
      (affineGroupSchemeProperty (CommRingCat.of R)).ι ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} R)
        (CommHopfAlgCat.{u} R)).op
      (commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
        (CommRingCat.of R))

/-- The object produced by the finite-type Hopf/group-scheme anti-equivalence is the bundled
finite-type Hopf spectrum. -/
noncomputable def
    finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat.functorObjIso
    (R : Type u) [CommRing R] (H : (FiniteTypeCommHopfAlgCat.{u, u} R)ᵒᵖ) :
    (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat R).functor.obj H ≅
      ⟨⟨(hopfSpec (CommRingCat.of R)).obj (op H.unop.obj), by
          rw [affineGroupSchemeProperty_iff, hopfSpec_obj_X_left]
          infer_instance⟩,
        by
          rw [finiteTypeAffineGroupSchemeProperty_iff]
          exact (algebraFiniteType_iff_locallyOfFiniteType_hopfSpec R H.unop.obj).mp
            H.unop.property⟩ :=
  (finiteTypeAffineGroupSchemeProperty (CommRingCat.of R)).ι.preimageIso
    ((affineGroupSchemeProperty (CommRingCat.of R)).ι.preimageIso
      ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat.functorCompιIso R).app H))

/-- An isomorphism-invariant property of affine group schemes can be tested on the coordinate
Hopf algebra of a finite-type affine group scheme whenever the unrestricted anti-equivalence
identifies it with a coordinate-side property. -/
theorem finiteType_objectProperty_iff_coordinate
    (R : Type u) [CommRing R]
    (P : ObjectProperty (AffineGroupSchemeCat (CommRingCat.of R)))
    [P.IsClosedUnderIsomorphisms]
    (Q : ObjectProperty (CommHopfAlgCat.{u} R))
    (hPQ : P.inverseImage
      (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).functor = Q.op)
    (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of R)) :
    P G.obj ↔
      Q ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat R).inverse.obj
        G).unop.obj := by
  let E := finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat R
  let H := E.inverse.obj G
  let H₀ := (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} R)
    (CommHopfAlgCat.{u} R)).op.obj H
  let eSpec :
      (finiteTypeAffineGroupSchemeProperty (CommRingCat.of R)).ι.obj (E.functor.obj H) ≅
        (commHopfAlgCatOpEquivAffineGroupSchemeCat
          (CommRingCat.of R)).functor.obj H₀ :=
    (finiteTypeAffineGroupSchemeProperty (CommRingCat.of R)).ι.mapIso
        (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat.functorObjIso R H) ≪≫
      (commHopfAlgCatOpEquivAffineGroupSchemeCat.functorObjIso R H₀).symm
  let eG :
      (finiteTypeAffineGroupSchemeProperty (CommRingCat.of R)).ι.obj (E.functor.obj H) ≅
        G.obj :=
    (finiteTypeAffineGroupSchemeProperty (CommRingCat.of R)).ι.mapIso (E.counitIso.app G)
  calc
    P G.obj ↔ P
        ((finiteTypeAffineGroupSchemeProperty (CommRingCat.of R)).ι.obj (E.functor.obj H)) :=
      (P.prop_iff_of_iso eG).symm
    _ ↔ P ((commHopfAlgCatOpEquivAffineGroupSchemeCat
          (CommRingCat.of R)).functor.obj H₀) :=
      P.prop_iff_of_iso eSpec
    _ ↔ Q.op H₀ := by
      exact Iff.of_eq <| congrArg
        (fun T : ObjectProperty (CommHopfAlgCat.{u} R)ᵒᵖ ↦ T H₀) hPQ
    _ ↔ Q ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat R).inverse.obj
        G).unop.obj := by
      rw [ObjectProperty.op_iff]
      simp only [H₀, H, E, Functor.op_obj,
        FiniteTypeCommHopfAlgCat.forget₂_commHopfAlgCat_obj]

end TauCeti
