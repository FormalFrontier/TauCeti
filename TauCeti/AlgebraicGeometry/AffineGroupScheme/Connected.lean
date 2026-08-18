/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.FiniteType

/-!
# Geometric connectedness of affine group schemes

This file compares geometric connectedness of a commutative Hopf algebra with Mathlib's
scheme-theoretic `GeometricallyConnected` predicate on its Hopf spectrum.

## Main declarations

* `TauCeti.geometricallyConnectedAffineGroupSchemeProperty`: geometric connectedness of the
  structural morphism as an object property on affine group schemes.
* `TauCeti.geometricallyConnectedCommHopfAlg_iff_geometricallyConnected_hopfSpec`: compatibility
  of the coordinate-ring and scheme-theoretic predicates.
* `TauCeti.geometricallyConnected_iff_geometricallyConnected_coordinate`: geometric
  connectedness of a finite-type affine group scheme in terms of its coordinate algebra.
* `TauCeti.geometricallyConnected_hopfSpec_iff_idempotent_eq_zero_or_one`: the idempotent
  characterization of geometric connectedness for a Hopf spectrum.

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

/-- **Geometric connectedness agrees across the affine-group-scheme and coordinate-ring
models.** The structural morphism of a Hopf spectrum is geometrically connected if and only if
its coordinate algebra is geometrically connected after every field extension. -/
theorem geometricallyConnectedCommHopfAlg_iff_geometricallyConnected_hopfSpec
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    geometricallyConnectedCommHopfAlgProperty k H ↔
      GeometricallyConnected
        (((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.hom) := by
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

/-- Under the affine Hopf/group-scheme anti-equivalence, the inverse image of geometric
connectedness on affine group schemes is geometric connectedness of coordinate Hopf algebras. -/
theorem geometricallyConnectedAffineGroupSchemeProperty_inverseImage
    (k : Type u) [Field k] :
    (geometricallyConnectedAffineGroupSchemeProperty (CommRingCat.of k)).inverseImage
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of k)).functor =
      (geometricallyConnectedCommHopfAlgProperty k).op := by
  apply objectProperty_inverseImage_commHopfAlgCatOpEquiv
  intro H
  exact (geometricallyConnectedCommHopfAlg_iff_geometricallyConnected_hopfSpec k H).symm

/-- A finite-type affine group scheme has geometrically connected structural morphism exactly
when its coordinate algebra supplied by the affine anti-equivalence is geometrically connected. -/
theorem geometricallyConnected_iff_geometricallyConnected_coordinate
    (k : Type u) [Field k]
    (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k)) :
    GeometricallyConnected G.obj.obj.X.hom ↔
      geometricallyConnectedCommHopfAlgProperty k
        ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse.obj
          G).unop.obj := by
  let E := finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k
  let H := E.inverse.obj G
  let H₀ := (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
    (CommHopfAlgCat.{u} k)).op.obj H
  let eSpec :
      (finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι.obj (E.functor.obj H) ≅
        (commHopfAlgCatOpEquivAffineGroupSchemeCat
          (CommRingCat.of k)).functor.obj H₀ :=
    (affineGroupSchemeProperty (CommRingCat.of k)).ι.preimageIso
      ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat.functorCompιIso k).app H ≪≫
        ((commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
          (CommRingCat.of k)).app H₀).symm)
  let eG :
      (finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι.obj (E.functor.obj H) ≅ G.obj :=
    (finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι.mapIso (E.counitIso.app G)
  change geometricallyConnectedAffineGroupSchemeProperty (CommRingCat.of k) G.obj ↔
    (geometricallyConnectedCommHopfAlgProperty k).op H₀
  calc
    _ ↔ geometricallyConnectedAffineGroupSchemeProperty (CommRingCat.of k)
        ((finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι.obj (E.functor.obj H)) :=
      ((geometricallyConnectedAffineGroupSchemeProperty
        (CommRingCat.of k)).prop_iff_of_iso eG).symm
    _ ↔ geometricallyConnectedAffineGroupSchemeProperty (CommRingCat.of k)
        ((commHopfAlgCatOpEquivAffineGroupSchemeCat
          (CommRingCat.of k)).functor.obj H₀) :=
      (geometricallyConnectedAffineGroupSchemeProperty
        (CommRingCat.of k)).prop_iff_of_iso eSpec
    _ ↔ (geometricallyConnectedCommHopfAlgProperty k).op H₀ := by
      change ((geometricallyConnectedAffineGroupSchemeProperty
        (CommRingCat.of k)).inverseImage
          (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of k)).functor) H₀ ↔ _
      rw [geometricallyConnectedAffineGroupSchemeProperty_inverseImage]

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

end TauCeti
