/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Basic
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec

/-!
# Closed immersions of affine group schemes

The scheme morphism underlying the contravariant `hopfSpec` image of a morphism of commutative
Hopf algebras is a closed immersion exactly when the coordinate morphism is surjective. This
criterion requires no hypotheses beyond commutativity of the base and coordinate rings.

Mathlib's affine closed-immersion criterion identifies closed immersions between affine spectra
with surjective coordinate-ring morphisms. The result here specializes that criterion to the
underlying scheme morphism of `hopfSpec`.

The pinned `hopfSpec` construction requires the base ring and the Hopf-algebra carriers to lie in
the same universe, which is reflected in the declaration in this file.

## Main declarations

* `TauCeti.isIso_hom_hom_left_eqToHom`: equality transport between group schemes is an
  isomorphism on underlying schemes.
* `TauCeti.CommHopfAlgCat.isClosedImmersion_hopfSpec_map_iff`: the coordinate criterion for a
  morphism of Hopf spectra to be a closed immersion.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

open AlgebraicGeometry

/-- Equality transport between group schemes is an isomorphism on their underlying scheme
morphisms. -/
lemma isIso_hom_hom_left_eqToHom {S : Scheme.{u}} {G G' : Grp (Over S)} (h : G = G') :
    IsIso (eqToHom h).hom.hom.left :=
  ((Over.forget S).mapIso ((Grp.forget (Over S)).mapIso (eqToIso h))).isIso_hom

/-- Composition of group-scheme morphisms is composition on the underlying scheme morphisms. -/
@[simp]
lemma comp_hom_hom_left {S : Scheme.{u}} {G G' G'' : Grp (Over S)}
    (f : G ⟶ G') (g : G' ⟶ G'') :
    (f ≫ g).hom.hom.left = f.hom.hom.left ≫ g.hom.hom.left :=
  rfl

/-- Equality transport between group schemes becomes equality transport between their
underlying schemes. -/
@[simp]
lemma eqToHom_hom_hom_left {S : Scheme.{u}} {G G' : Grp (Over S)} (h : G = G') :
    (eqToHom h).hom.hom.left =
      eqToHom (congrArg (fun K : Grp (Over S) ↦ K.X.left) h) := by
  subst h
  rfl

/-- Pre- and postcomposing a scheme morphism with equality transports does not change whether
it is a closed immersion. -/
@[simp]
lemma isClosedImmersion_eqToHom_comp_comp_eqToHom_iff
    {W X Y Z : Scheme.{u}} (h : W = X) (h' : Y = Z) (f : X ⟶ Y) :
    IsClosedImmersion (eqToHom h ≫ (f ≫ eqToHom h')) ↔ IsClosedImmersion f := by
  rw [
    @MorphismProperty.cancel_left_of_respectsIso
      Scheme _ @IsClosedImmersion inferInstance _ _ _ (eqToHom h) (f ≫ eqToHom h')
        (inferInstance : IsIso (eqToHom h)),
    @MorphismProperty.cancel_right_of_respectsIso
      Scheme _ @IsClosedImmersion inferInstance _ _ _ f (eqToHom h')
        (inferInstance : IsIso (eqToHom h'))]

namespace CommHopfAlgCat

/-- A map of affine spectra induced by a Hopf-algebra morphism is a closed immersion exactly
when the Hopf-algebra morphism is surjective. -/
@[simp↓]
lemma isClosedImmersion_specMap_iff {S : CommRingCat.{u}}
    {A B : _root_.CommHopfAlgCat.{u} S} (f : A ⟶ B) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom)) ↔
      Function.Surjective f.hom :=
  IsClosedImmersion.hasAffineProperty.SpecMap_iff_of_affineAnd
    RingHom.surjective_respectsIso _

/-- The scheme morphism underlying the contravariant `hopfSpec` image of `f` is a closed
immersion if and only if the coordinate Hopf-algebra morphism `f` is surjective. -/
@[simp↓]
lemma isClosedImmersion_hopfSpec_map_iff {S : CommRingCat.{u}}
    {A B : _root_.CommHopfAlgCat.{u} S} (f : A ⟶ B) :
    IsClosedImmersion ((AlgebraicGeometry.hopfSpec S).map f.op).hom.hom.left ↔
      Function.Surjective f.hom := by
  rw [hopfSpec_map_hom_hom_left]
  exact isClosedImmersion_specMap_iff f

end CommHopfAlgCat

end TauCeti
