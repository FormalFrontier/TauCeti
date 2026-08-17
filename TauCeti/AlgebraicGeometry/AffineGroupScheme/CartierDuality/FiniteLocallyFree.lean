/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.HopfAlgebra.FiniteDual.CartierDuality
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Equivalence
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec
public import TauCeti.CategoryTheory.Monoidal.Mon

/-!
# Cartier duality over an affine base

This file transports finite locally free Cartier duality from coordinate Hopf algebras to
commutative affine group schemes over an arbitrary commutative ring. A morphism to an affine base
is finite locally free when it is finite, flat, and locally of finite presentation. For a Hopf
spectrum these three conditions say exactly that its coordinate algebra is finite projective over
the base. Commutativity of the group object is, as before, cocommutativity of the coordinate Hopf
algebra.

The resulting anti-equivalence is Cartier duality over an arbitrary affine base. Its objects
explicitly include flatness and finite presentation; these hypotheses cannot be omitted over a
general ring.

## Main declarations

* `TauCeti.moduleProjective_iff_flat_and_locallyOfFinitePresentation_hopfSpec`: finite
  projectivity of a coordinate algebra is the flat, finitely presented condition on its Hopf
  spectrum.
* `TauCeti.finiteLocallyFreeCommAffineGroupSchemeProperty`: the object property selecting finite
  locally free commutative affine group schemes over an affine base.
* `TauCeti.FiniteLocallyFreeCommAffineGroupSchemeCat`: the category selected by that property.
* `finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat`:
  the restricted anti-equivalence over a commutative ring.
  Its `functorCompιIso`, `inverseCompιIso`, and `rightOpInverseCompιIso` describe the two
  functors after forgetting the property proofs.
* `TauCeti.FiniteLocallyFreeCommAffineGroupSchemeCat.cartierDuality`: Cartier duality over an
  arbitrary affine base.
* `TauCeti.FiniteLocallyFreeCommAffineGroupSchemeCat.cartierDuality_functor`: its computation as
  transported finite dualization.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
* J. S. Milne, *Algebraic Groups* (2017), Section 12.e.

This completes the affine-base case of the Cartier-duality target in Layer 4 of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace TauCeti

universe u

/-- The object property selecting finite locally free commutative affine group schemes over an
affine base. Finite local freeness is expressed by the standard scheme-theoretic conjunction of
finiteness, flatness, and local finite presentation. -/
def finiteLocallyFreeCommAffineGroupSchemeProperty (S : CommRingCat.{u}) :
    ObjectProperty (AffineGroupSchemeCat S) :=
  fun G => IsFinite G.obj.X.hom ∧ Flat G.obj.X.hom ∧
    LocallyOfFinitePresentation G.obj.X.hom ∧ IsCommMonObj G.obj.X

/-- Membership in the finite-locally-free commutative affine-group-scheme property. -/
@[simp]
theorem finiteLocallyFreeCommAffineGroupSchemeProperty_iff
    (S : CommRingCat.{u}) (G : AffineGroupSchemeCat S) :
    finiteLocallyFreeCommAffineGroupSchemeProperty S G ↔
      IsFinite G.obj.X.hom ∧ Flat G.obj.X.hom ∧
        LocallyOfFinitePresentation G.obj.X.hom ∧ IsCommMonObj G.obj.X :=
  Iff.rfl

instance (S : CommRingCat.{u}) :
    (finiteLocallyFreeCommAffineGroupSchemeProperty S).IsClosedUnderIsomorphisms where
  of_iso e hG := by
    let e' := (affineGroupSchemeProperty S).ι.mapIso e
    constructor
    · exact (MorphismProperty.over_iso_iff (@IsFinite) ((Grp.forget _).mapIso e')).mp hG.1
    · constructor
      · exact (MorphismProperty.over_iso_iff (@Flat) ((Grp.forget _).mapIso e')).mp hG.2.1
      · constructor
        · exact (MorphismProperty.over_iso_iff (@LocallyOfFinitePresentation)
            ((Grp.forget _).mapIso e')).mp hG.2.2.1
        · exact isCommMonObj_of_grp_iso e' hG.2.2.2

/-- Under the affine Hopf/group-scheme anti-equivalence over a commutative ring, finite
projectivity and cocommutativity of the coordinate Hopf algebra correspond to finite local
freeness and commutativity of the affine group scheme. -/
theorem finiteLocallyFreeCommAffineGroupSchemeProperty_inverseImage
    (R : Type u) [CommRing R] :
    (finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).inverseImage
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).functor =
      (finiteLocallyFreeBicommutativeHopfAlgProperty R).op := by
  apply objectProperty_inverseImage_commHopfAlgCatOpEquiv R
  intro H
  rw [finiteLocallyFreeCommAffineGroupSchemeProperty_iff,
    finiteLocallyFreeBicommutativeHopfAlgProperty_iff]
  constructor
  · intro h
    have hfinite : Module.Finite R H :=
      (moduleFinite_iff_isFinite_hopfSpec R H).mpr h.1
    let _ : Module.Finite R H := hfinite
    exact ⟨hfinite,
      (moduleProjective_iff_flat_and_locallyOfFinitePresentation_hopfSpec R H).mpr
        ⟨h.2.1, h.2.2.1⟩,
      (isCocomm_iff_isCommMonObj_hopfSpec R H).mpr h.2.2.2⟩
  · intro h
    let _ : Module.Finite R H := h.1
    have hprojective :=
      (moduleProjective_iff_flat_and_locallyOfFinitePresentation_hopfSpec R H).mp h.2.1
    exact ⟨(moduleFinite_iff_isFinite_hopfSpec R H).mp h.1,
      hprojective.1, hprojective.2,
      (isCocomm_iff_isCommMonObj_hopfSpec R H).mp h.2.2⟩

/-- The category of finite locally free commutative affine group schemes over an affine base. -/
abbrev FiniteLocallyFreeCommAffineGroupSchemeCat (S : CommRingCat.{u}) :=
  (finiteLocallyFreeCommAffineGroupSchemeProperty S).FullSubcategory

instance {S : CommRingCat.{u}} (G : FiniteLocallyFreeCommAffineGroupSchemeCat S) :
    IsFinite G.obj.obj.X.hom := G.property.1

instance {S : CommRingCat.{u}} (G : FiniteLocallyFreeCommAffineGroupSchemeCat S) :
    Flat G.obj.obj.X.hom := G.property.2.1

instance {S : CommRingCat.{u}} (G : FiniteLocallyFreeCommAffineGroupSchemeCat S) :
    LocallyOfFinitePresentation G.obj.obj.X.hom := G.property.2.2.1

instance {S : CommRingCat.{u}} (G : FiniteLocallyFreeCommAffineGroupSchemeCat S) :
    IsCommMonObj G.obj.obj.X := G.property.2.2.2

/-- `Spec` as an anti-equivalence from finite locally free bicommutative Hopf algebras to finite
locally free commutative affine group schemes over an arbitrary commutative ring. -/
noncomputable def
    finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
    (R : Type u) [CommRing R] :
    (FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R)ᵒᵖ ≌
      FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R) :=
  (ObjectProperty.opEquivalence
    (finiteLocallyFreeBicommutativeHopfAlgProperty R)).symm.trans <|
    (commHopfAlgCatOpEquivAffineGroupSchemeCat
      (CommRingCat.of R)).congrFullSubcategory
        (finiteLocallyFreeCommAffineGroupSchemeProperty_inverseImage R)

namespace
  finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat

/-- The restricted equivalence followed by the finite-locally-free inclusion is definitionally
the unrestricted equivalence applied after forgetting the property proofs. This private
isomorphism isolates the implementation of the object-property restrictions. -/
private noncomputable def functorCompιIsoAux (R : Type u) [CommRing R] :
    (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          R).functor ⋙
        (finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).ι ≅
      (forget₂ (FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R)
          (CommHopfAlgCat.{u} R)).op ⋙
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).functor :=
  Iso.refl _

/-- The restricted anti-equivalence followed by the inclusions into affine group schemes and all
group schemes is Mathlib's `hopfSpec` after forgetting the finiteness, projectivity, and
cocommutativity proofs. -/
noncomputable def functorCompιIso (R : Type u) [CommRing R] :
    (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          R).functor ⋙
        (finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).ι ⋙
        (affineGroupSchemeProperty (CommRingCat.of R)).ι ≅
      (forget₂ (FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R)
          (CommHopfAlgCat.{u} R)).op ⋙ hopfSpec (CommRingCat.of R) :=
  Functor.isoWhiskerRight
      (functorCompιIsoAux R)
      (affineGroupSchemeProperty (CommRingCat.of R)).ι ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (forget₂ (FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R)
        (CommHopfAlgCat.{u} R)).op
      (commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso (CommRingCat.of R))

/-- The inverse restricted anti-equivalence computes as the unrestricted coordinate-Hopf-algebra
functor after forgetting finite local freeness and commutativity. -/
noncomputable def inverseCompιIso (R : Type u) [CommRing R] :
    (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          R).inverse ⋙
        (forget₂ (FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R)
          (CommHopfAlgCat.{u} R)).op ≅
      (finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).ι ⋙
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).inverse :=
  Iso.refl _

/-- The `rightOp` inverse used in scheme-level Cartier duality computes, after forgetting
module-finiteness and cocommutativity, as the opposite of the unrestricted coordinate Hopf-algebra
functor. -/
noncomputable def rightOpInverseCompιIso (R : Type u) [CommRing R] :
    (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
      R).rightOp.inverse ⋙
        forget₂ (FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R) (CommHopfAlgCat.{u} R) ≅
      ((finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).ι ⋙
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).inverse).leftOp := by
  let e := inverseCompιIso R
  exact
    { hom := e.inv.leftOp
      inv := e.hom.leftOp }

end
  finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat

namespace FiniteLocallyFreeCommAffineGroupSchemeCat

/-- **Cartier duality for finite locally free commutative affine group schemes over an arbitrary
commutative base ring.** -/
noncomputable def cartierDuality
    (R : Type u) [CommRing R] :
    (FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R))ᵒᵖ ≌
      FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R) :=
  ((finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
    R).rightOp).symm.trans <|
    ((FiniteLocallyFreeBicommutativeHopfAlgCat.dualFunctor
      (k := R)).rightOp).asEquivalence |>.trans
      (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat R)

/-- The forward functor of Cartier duality over an arbitrary affine base is finite dualization
transported through the finite-locally-free Hopf--spectrum anti-equivalence. -/
@[simp]
theorem cartierDuality_functor (R : Type u) [CommRing R] :
    (cartierDuality R).functor =
      (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
        R).rightOp.inverse ⋙
        (FiniteLocallyFreeBicommutativeHopfAlgCat.dualFunctor (k := R)).rightOp ⋙
        (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          R).functor := by
  simp [cartierDuality]

end FiniteLocallyFreeCommAffineGroupSchemeCat

end TauCeti
