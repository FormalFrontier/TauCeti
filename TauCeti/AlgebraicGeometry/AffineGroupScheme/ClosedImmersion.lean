/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Basic

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

* `TauCeti.CommHopfAlgCat.isClosedImmersion_hopfSpec_map_iff`: the coordinate criterion for a
  morphism of Hopf spectra to be a closed immersion.
* `TauCeti.CommHopfAlgCat.isClosedImmersion_hopfSpec_map_comp_eqToHom_iff`: the same criterion
  after identifying the target group scheme.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace CommHopfAlgCat

open AlgebraicGeometry

private lemma hopfSpec_map_left {S : CommRingCat.{u}}
    {A B : _root_.CommHopfAlgCat.{u} S} (f : A ⟶ B) :
    ((AlgebraicGeometry.hopfSpec S).map f.op).hom.hom.left =
      Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom) :=
  rfl

/-- The scheme morphism underlying the contravariant `hopfSpec` image of `f` is a closed
immersion if and only if the coordinate Hopf-algebra morphism `f` is surjective. -/
@[simp↓]
lemma isClosedImmersion_hopfSpec_map_iff {S : CommRingCat.{u}}
    {A B : _root_.CommHopfAlgCat.{u} S} (f : A ⟶ B) :
    IsClosedImmersion ((AlgebraicGeometry.hopfSpec S).map f.op).hom.hom.left ↔
      Function.Surjective f.hom := by
  rw [hopfSpec_map_left]
  exact IsClosedImmersion.hasAffineProperty.SpecMap_iff_of_affineAnd
    RingHom.surjective_respectsIso _

/-- Composing the `hopfSpec` image of a Hopf-algebra morphism with an identification of its
target group scheme does not change the closed-immersion criterion. -/
@[simp↓]
lemma isClosedImmersion_hopfSpec_map_comp_eqToHom_iff {S : CommRingCat.{u}}
    {A B : _root_.CommHopfAlgCat.{u} S}
    {G : Grp (Over (AlgebraicGeometry.Spec S))}
    (hG : G = (AlgebraicGeometry.hopfSpec S).obj (Opposite.op A)) (f : A ⟶ B) :
    IsClosedImmersion
        (((AlgebraicGeometry.hopfSpec S).map f.op ≫ eqToHom hG.symm).hom.hom.left) ↔
      Function.Surjective f.hom := by
  let _ : IsIso (eqToHom hG.symm).hom.hom.left :=
    ((Over.forget (AlgebraicGeometry.Spec S)).mapIso
      ((Grp.forget (Over (AlgebraicGeometry.Spec S))).mapIso
        (eqToIso hG.symm))).isIso_hom
  simp only [Grp.comp', Mon.comp_hom', Over.comp_left]
  rw [MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)]
  exact isClosedImmersion_hopfSpec_map_iff f

end CommHopfAlgCat

end TauCeti
