/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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
general ring. Because the Hopf-algebra equivalence being transported already knows its own
inverse, so does this one: the inverse is Cartier dualization again, and the counit is the
double-dual isomorphism `cartierDualDualIso`.

## Main declarations

* `TauCeti.moduleProjective_iff_flat_and_locallyOfFinitePresentation_hopfSpec`: finite
  projectivity of a coordinate algebra is the flat, finitely presented condition on its Hopf
  spectrum.
* `TauCeti.finiteLocallyFreeCommAffineGroupSchemeProperty`: the object property selecting finite
  locally free commutative affine group schemes over an affine base.
* `TauCeti.FiniteLocallyFreeCommAffineGroupSchemeCat`: the category selected by that property.
* `finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat`:
  the restricted anti-equivalence over a commutative ring.
  Its `functorCompFullSubcategoryιIso`, `functorCompιIso`, `inverseCompιIso`, and
  `rightOpInverseCompιIso` describe the two functors after forgetting the property proofs.
* `TauCeti.FiniteLocallyFreeCommAffineGroupSchemeCat.cartierDuality`: Cartier duality over an
  arbitrary affine base, with `cartierDuality_functor` and `cartierDuality_inverse` computing
  both of its directions as transported finite dualization.
* `TauCeti.FiniteLocallyFreeCommAffineGroupSchemeCat.cartierDual` and
  `TauCeti.FiniteLocallyFreeCommAffineGroupSchemeCat.coordHopfAlgebra`: the Cartier dual of a
  group scheme and its coordinate Hopf algebra, related by `cartierDual_eq`.
* `TauCeti.FiniteLocallyFreeCommAffineGroupSchemeCat.cartierDualDualIso`: the double-dual
  isomorphism `G ≅ D(D(G))`, natural by `cartierDualDualIso_hom_naturality`.

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
abbrev FiniteLocallyFreeCommAffineGroupSchemeCat (S : CommRingCat.{u}) : Type _ :=
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

/-- The restricted equivalence followed by the finite-locally-free inclusion is the unrestricted
equivalence applied after forgetting the property proofs. This isomorphism isolates the
implementation of the object-property restrictions, so that downstream files never have to unfold
them. -/
noncomputable def functorCompFullSubcategoryιIso (R : Type u) [CommRing R] :
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
      (functorCompFullSubcategoryιIso R)
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
commutative base ring.**

Transporting `FiniteLocallyFreeBicommutativeHopfAlgCat.cartierDuality` rather than the bare
dualization functor keeps the inverse computable: it is again Cartier dualization, and the counit
is the double-dual evaluation isomorphism `cartierDualDualIso`. -/
@[expose]
noncomputable def cartierDuality
    (R : Type u) [CommRing R] :
    (FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R))ᵒᵖ ≌
      FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R) :=
  ((finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
    R).rightOp).symm.trans <|
    (FiniteLocallyFreeBicommutativeHopfAlgCat.cartierDuality (k := R)).rightOp.trans
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
          R).functor :=
  (rfl)

/-- Cartier dualization as a contravariant endofunctor on finite locally free commutative affine
group schemes. -/
noncomputable abbrev cartierDualFunctor (R : Type u) [CommRing R] :
    (FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R))ᵒᵖ ⥤
      FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R) :=
  (cartierDuality R).functor

/-- The inverse of Cartier duality is Cartier dualization again. This is the identification that
`CategoryTheory.Functor.asEquivalence` cannot provide. -/
@[simp]
theorem cartierDuality_inverse (R : Type u) [CommRing R] :
    (cartierDuality R).inverse = (cartierDualFunctor R).rightOp :=
  (rfl)

/-- The coordinate Hopf algebra of a finite locally free commutative affine group scheme. -/
noncomputable abbrev coordHopfAlgebra (R : Type u) [CommRing R]
    (G : FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R)) :
    FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R :=
  (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
    R).rightOp.inverse.obj (op G)

/-- The Cartier dual of a finite locally free commutative affine group scheme. -/
noncomputable abbrev cartierDual (R : Type u) [CommRing R]
    (G : FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R)) :
    FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R) :=
  (cartierDualFunctor R).obj (op G)

/-- The Cartier dual is represented by the finite dual of the coordinate Hopf algebra. -/
theorem cartierDual_eq (R : Type u) [CommRing R]
    (G : FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R)) :
    cartierDual R G =
      (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
        R).functor.obj
          (op (FiniteLocallyFreeBicommutativeHopfAlgCat.dual (coordHopfAlgebra R G))) :=
  (rfl)

/-- **Cartier duality is involutive.** Every finite locally free commutative affine group scheme
is naturally isomorphic to its Cartier double dual. -/
noncomputable def cartierDualDualNatIso (R : Type u) [CommRing R] :
    𝟭 (FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R)) ≅
      (cartierDualFunctor R).rightOp ⋙ cartierDualFunctor R :=
  (cartierDuality R).counitIso.symm

/-- The double-dual isomorphism of a single finite locally free commutative affine group
scheme. -/
noncomputable abbrev cartierDualDualIso (R : Type u) [CommRing R]
    (G : FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R)) :
    G ≅ cartierDual R (cartierDual R G) :=
  (cartierDualDualNatIso R).app G

/-- The double-dual isomorphism is the inverse counit of `cartierDuality`. -/
@[simp]
theorem cartierDualDualNatIso_hom_app (R : Type u) [CommRing R]
    (G : FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R)) :
    (cartierDualDualNatIso R).hom.app G = (cartierDuality R).counitIso.inv.app G :=
  (rfl)

/-- The double-dual isomorphism is natural in the group scheme. -/
@[reassoc]
theorem cartierDualDualIso_hom_naturality (R : Type u) [CommRing R]
    {G H : FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R)} (f : G ⟶ H) :
    f ≫ (cartierDualDualIso R H).hom =
      (cartierDualDualIso R G).hom ≫
        (cartierDualFunctor R).map ((cartierDualFunctor R).map f.op).op :=
  (cartierDualDualNatIso R).hom.naturality f

end FiniteLocallyFreeCommAffineGroupSchemeCat

end TauCeti
