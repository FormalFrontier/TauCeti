/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Equivalence
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec

/-!
# Geometric connectedness of affine group schemes

This file compares geometric connectedness of a commutative Hopf algebra with Mathlib's
scheme-theoretic `GeometricallyConnected` predicate on its Hopf spectrum. It then restricts the
affine Hopf/group-scheme anti-equivalence to geometrically connected objects:

```text
(GeometricallyConnectedCommHopfAlgCat k)ᵒᵖ ≌
  GeometricallyConnectedAffineGroupSchemeCat (Spec k).
```

## Main declarations

* `TauCeti.geometricallyConnectedCommHopfAlg_iff_geometricallyConnected_hopfSpec`: compatibility
  of the coordinate-ring and scheme-theoretic predicates.
* `TauCeti.geometricallyConnected_hopfSpec_iff_idempotent_eq_zero_or_one`: the idempotent
  characterization of geometric connectedness for a Hopf spectrum.
* `TauCeti.geometricallyConnectedCommHopfAlgCatOpEquivAffineGroupSchemeCat`: the restricted
  anti-equivalence.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.a.

This is the geometric-connectedness prerequisite for Layer 3, "Identity component and component
group", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

open AlgebraicGeometry

universe u

private instance geometricallyConnected_respectsIso :
    MorphismProperty.RespectsIso @GeometricallyConnected :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- The object property on affine group schemes selecting those whose structural morphism is
geometrically connected. -/
def geometricallyConnectedAffineGroupSchemeProperty (S : CommRingCat.{u}) :
    ObjectProperty (AffineGroupSchemeCat S) :=
  fun G => GeometricallyConnected G.obj.X.hom

/-- Membership in the geometrically connected affine-group-scheme object property. -/
@[simp]
lemma geometricallyConnectedAffineGroupSchemeProperty_iff (S : CommRingCat.{u})
    (G : AffineGroupSchemeCat S) :
    geometricallyConnectedAffineGroupSchemeProperty S G ↔
      GeometricallyConnected G.obj.X.hom :=
  Iff.rfl

/-- Geometric connectedness of the structural morphism is invariant under isomorphism of affine
group schemes. -/
instance (S : CommRingCat.{u}) :
    (geometricallyConnectedAffineGroupSchemeProperty S).IsClosedUnderIsomorphisms where
  of_iso e hG :=
    (MorphismProperty.over_iso_iff (@GeometricallyConnected)
      ((Grp.forget _).mapIso ((affineGroupSchemeProperty S).ι.mapIso e))).mp hG

/-- The category of geometrically connected affine group schemes over the affine base `Spec S`. -/
abbrev GeometricallyConnectedAffineGroupSchemeCat (S : CommRingCat.{u}) :=
  (geometricallyConnectedAffineGroupSchemeProperty S).FullSubcategory

/-- An object of `GeometricallyConnectedAffineGroupSchemeCat S` has geometrically connected
structural morphism by construction. -/
instance (G : GeometricallyConnectedAffineGroupSchemeCat S) :
    GeometricallyConnected G.obj.obj.X.hom :=
  G.property

/-- **Geometric connectedness agrees across the affine-group-scheme and coordinate-ring
models.** The structural morphism of a Hopf spectrum is geometrically connected if and only if
its coordinate algebra is geometrically connected after every field extension. -/
theorem geometricallyConnectedCommHopfAlg_iff_geometricallyConnected_hopfSpec
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    geometricallyConnectedCommHopfAlgProperty k H ↔
      GeometricallyConnected
        (((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.hom) := by
  -- This witness is not a global instance, but `cancel_left_of_respectsIso` needs it below.
  let : MorphismProperty.RespectsIso @GeometricallyConnected :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [geometricallyConnectedCommHopfAlgProperty_iff, hopfSpec_obj_X_hom]
  rw [MorphismProperty.cancel_left_of_respectsIso
    (P := @GeometricallyConnected) (eqToHom (hopfSpec_obj_X_left k H))]
  rw [GeometricallyConnected.eq_geometrically,
    geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  constructor
  · intro h K _ _
    exact (pullbackSpecIso k H K).hom.homeomorph.connectedSpace_iff.mpr (h K)
  · intro h K _ _
    exact (pullbackSpecIso k H K).hom.homeomorph.connectedSpace_iff.mp (h K)

/-- The structural morphism of a Hopf spectrum is geometrically connected exactly when, after
every extension `K / k` of the base field, every idempotent of `H ⊗[k] K` is zero or one. -/
theorem geometricallyConnected_hopfSpec_iff_idempotent_eq_zero_or_one
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    GeometricallyConnected
        (((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.hom) ↔
      ∀ (K : Type u) [Field K] [Algebra k K] (e : (H : Type u) ⊗[k] K),
        IsIdempotentElem e → e = 0 ∨ e = 1 := by
  rw [← geometricallyConnectedCommHopfAlg_iff_geometricallyConnected_hopfSpec,
    geometricallyConnectedCommHopfAlgProperty_iff_idempotent_eq_zero_or_one]

/-- Under the affine Hopf/group-scheme anti-equivalence, the inverse image of geometric
connectedness is geometric connectedness of the coordinate Hopf algebra. -/
theorem geometricallyConnectedAffineGroupSchemeProperty_inverseImage
    (k : Type u) [Field k] :
    (geometricallyConnectedAffineGroupSchemeProperty (CommRingCat.of k)).inverseImage
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of k)).functor =
      (geometricallyConnectedCommHopfAlgProperty k).op := by
  ext H
  let G : AffineGroupSchemeCat (CommRingCat.of k) :=
    ⟨(hopfSpec (CommRingCat.of k)).obj H, by
      apply (affineGroupSchemeProperty_iff _).mpr
      rw [← essImage_hopfSpec]
      exact ⟨H, ⟨Iso.refl _⟩⟩⟩
  let e : (commHopfAlgCatOpEquivAffineGroupSchemeCat
      (CommRingCat.of k)).functor.obj H ≅ G :=
    (affineGroupSchemeProperty (CommRingCat.of k)).ι.preimageIso
      ((commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
        (CommRingCat.of k)).app H)
  rw [ObjectProperty.prop_inverseImage_iff,
    geometricallyConnectedAffineGroupSchemeProperty_iff, ObjectProperty.op_iff]
  constructor
  · intro h
    have hG : geometricallyConnectedAffineGroupSchemeProperty (CommRingCat.of k) G :=
      (geometricallyConnectedAffineGroupSchemeProperty (CommRingCat.of k)).prop_of_iso e h
    exact (geometricallyConnectedCommHopfAlg_iff_geometricallyConnected_hopfSpec k H.unop).mpr hG
  · intro h
    apply (geometricallyConnectedAffineGroupSchemeProperty
      (CommRingCat.of k)).prop_of_iso e.symm
    exact (geometricallyConnectedCommHopfAlg_iff_geometricallyConnected_hopfSpec k H.unop).mp h

/-- `Spec` as an anti-equivalence from geometrically connected commutative Hopf algebras to
geometrically connected affine group schemes over a field. -/
noncomputable def geometricallyConnectedCommHopfAlgCatOpEquivAffineGroupSchemeCat
    (k : Type u) [Field k] :
    (GeometricallyConnectedCommHopfAlgCat.{u} k)ᵒᵖ ≌
      GeometricallyConnectedAffineGroupSchemeCat (CommRingCat.of k) :=
  (ObjectProperty.opEquivalence (geometricallyConnectedCommHopfAlgProperty k)).symm.trans <|
    (commHopfAlgCatOpEquivAffineGroupSchemeCat
      (CommRingCat.of k)).congrFullSubcategory
        (geometricallyConnectedAffineGroupSchemeProperty_inverseImage k)

/-- The forward restricted equivalence followed by the geometrically connected inclusion is the
unrestricted affine Hopf/group-scheme equivalence after forgetting the connectedness proof. -/
private noncomputable def
    geometricallyConnectedCommHopfAlgCatOpEquivAffineGroupSchemeCatFunctorCompιIso
    (k : Type u) [Field k] :
    (geometricallyConnectedCommHopfAlgCatOpEquivAffineGroupSchemeCat k).functor ⋙
        (geometricallyConnectedAffineGroupSchemeProperty (CommRingCat.of k)).ι ≅
      (forget₂ (GeometricallyConnectedCommHopfAlgCat.{u} k)
          (CommHopfAlgCat.{u} k)).op ⋙
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of k)).functor :=
  Iso.refl _

/-- The forward geometrically connected anti-equivalence, followed by the inclusions into affine
group schemes and then all group schemes, is `hopfSpec` after forgetting the connectedness proof. -/
noncomputable def
    geometricallyConnectedCommHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
    (k : Type u) [Field k] :
    (geometricallyConnectedCommHopfAlgCatOpEquivAffineGroupSchemeCat k).functor ⋙
          (geometricallyConnectedAffineGroupSchemeProperty (CommRingCat.of k)).ι ⋙
        (affineGroupSchemeProperty (CommRingCat.of k)).ι ≅
      (forget₂ (GeometricallyConnectedCommHopfAlgCat.{u} k)
          (CommHopfAlgCat.{u} k)).op ⋙ hopfSpec (CommRingCat.of k) :=
  Functor.isoWhiskerRight
      (geometricallyConnectedCommHopfAlgCatOpEquivAffineGroupSchemeCatFunctorCompιIso k)
      (affineGroupSchemeProperty (CommRingCat.of k)).ι ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (forget₂ (GeometricallyConnectedCommHopfAlgCat.{u} k)
        (CommHopfAlgCat.{u} k)).op
      (commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
        (CommRingCat.of k))

end TauCeti
