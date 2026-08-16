/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.CartierDuality.Basic

/-!
# Cartier duality over an affine base

This file transports finite locally free Cartier duality from coordinate Hopf algebras to
commutative affine group schemes over an arbitrary commutative ring. A morphism to an affine base
is finite locally free when it is finite, flat, and locally of finite presentation. For a Hopf
spectrum these three conditions say exactly that its coordinate algebra is finite projective over
the base. Commutativity of the group object is, as before, cocommutativity of the coordinate Hopf
algebra.

The resulting anti-equivalence is the general-base form of Cartier duality. Unlike the
field-specialized category in `CartierDuality.Basic`, its objects explicitly include flatness and
finite presentation; these hypotheses cannot be omitted over a general ring.

## Main declarations

* `TauCeti.moduleProjective_iff_flat_and_locallyOfFinitePresentation_hopfSpec`: finite
  projectivity of a coordinate algebra is the flat, finitely presented condition on its Hopf
  spectrum.
* `TauCeti.finiteLocallyFreeCommAffineGroupSchemeProperty`: finite locally free commutative affine
  group schemes over an affine base.
* `finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat`:
  the restricted anti-equivalence over a commutative ring.
* `TauCeti.FiniteLocallyFreeCommAffineGroupSchemeCat.cartierDuality`: Cartier duality over an
  arbitrary affine base.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
* J. S. Milne, *Algebraic Groups* (2017), Section 12.e.

This completes the general-base Cartier-duality target in Layer 4 of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace TauCeti

universe u

private instance isFinite_respectsIso :
    MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) ↦ inferInstance)

private instance flat_respectsIso :
    MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) ↦ inferInstance)

private instance locallyOfFinitePresentation_respectsIso :
    MorphismProperty.RespectsIso
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) ↦ inferInstance)

private theorem flat_hopfSpec_iff_moduleFlat
    (R : Type u) [CommRing R] (H : CommHopfAlgCat.{u} R) :
    Flat (((hopfSpec (CommRingCat.of R)).obj (op H)).X.hom) ↔ Module.Flat R H := by
  rw [hopfSpec_obj_X_hom]
  rw [MorphismProperty.cancel_left_of_respectsIso
    (P := @Flat) (eqToHom (hopfSpec_obj_X_left R H))]
  rw [Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff

private theorem locallyOfFinitePresentation_hopfSpec_iff_algebraFinitePresentation
    (R : Type u) [CommRing R] (H : CommHopfAlgCat.{u} R) :
    LocallyOfFinitePresentation
        (((hopfSpec (CommRingCat.of R)).obj (op H)).X.hom) ↔
      Algebra.FinitePresentation R H := by
  rw [hopfSpec_obj_X_hom]
  rw [MorphismProperty.cancel_left_of_respectsIso
    (P := @LocallyOfFinitePresentation) (eqToHom (hopfSpec_obj_X_left R H))]
  rw [LocallyOfFinitePresentation.SpecMap_iff]
  exact RingHom.finitePresentation_algebraMap

/-- For a finite Hopf algebra over a commutative ring, projectivity of the coordinate algebra is
equivalent to flatness and local finite presentation of its Hopf spectrum over the base.

The finiteness hypothesis is essential in the reverse direction: it converts finite presentation
as an algebra into finite presentation as a module, after which finite-presentation flatness is
equivalent to projectivity. -/
theorem moduleProjective_iff_flat_and_locallyOfFinitePresentation_hopfSpec
    (R : Type u) [CommRing R] (H : CommHopfAlgCat.{u} R) [Module.Finite R H] :
    Module.Projective R H ↔
      Flat (((hopfSpec (CommRingCat.of R)).obj (op H)).X.hom) ∧
        LocallyOfFinitePresentation
          (((hopfSpec (CommRingCat.of R)).obj (op H)).X.hom) := by
  rw [flat_hopfSpec_iff_moduleFlat,
    locallyOfFinitePresentation_hopfSpec_iff_algebraFinitePresentation]
  constructor
  · intro h
    let _ : Module.Projective R H := h
    let _ : Module.FinitePresentation R H :=
      Module.finitePresentation_of_projective R H
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hflat, hfp⟩
    let _ : Module.Flat R H := hflat
    let _ : Algebra.FinitePresentation R H := hfp
    let _ : Module.FinitePresentation R H :=
      Module.FinitePresentation.of_finite_of_finitePresentation R H
    exact Module.Flat.projective_of_finitePresentation

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

private theorem isCommMonObj_of_grp_iso'
    {C : Type u} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
    {G H : Grp C} (e : G ≅ H) (hG : IsCommMonObj G.X) : IsCommMonObj H.X := by
  let _ := hG
  constructor
  apply (cancel_mono e.inv.hom.hom).1
  simp only [Category.assoc, IsMonHom.mul_hom]
  rw [← Category.assoc, ← BraidedCategory.braiding_naturality]
  simp only [Category.assoc, IsCommMonObj.mul_comm]

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
        · exact isCommMonObj_of_grp_iso' e' hG.2.2.2

/-- Under the affine Hopf/group-scheme anti-equivalence over a commutative ring, finite
projectivity and cocommutativity of the coordinate Hopf algebra correspond to finite local
freeness and commutativity of the affine group scheme. -/
theorem finiteLocallyFreeCommAffineGroupSchemeProperty_inverseImage
    (R : Type u) [CommRing R] :
    (finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).inverseImage
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).functor =
      (finiteLocallyFreeBicommutativeHopfAlgProperty R).op := by
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
    finiteLocallyFreeCommAffineGroupSchemeProperty_iff, ObjectProperty.op_iff,
    finiteLocallyFreeBicommutativeHopfAlgProperty_iff]
  constructor
  · intro h
    have hG : finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R) G :=
      (finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).prop_of_iso e h
    have hfinite : Module.Finite R H.unop :=
      (moduleFinite_iff_isFinite_hopfSpec R H.unop).mpr hG.1
    let _ : Module.Finite R H.unop := hfinite
    exact ⟨hfinite,
      (moduleProjective_iff_flat_and_locallyOfFinitePresentation_hopfSpec R H.unop).mpr
        ⟨hG.2.1, hG.2.2.1⟩,
      (isCocomm_iff_isCommMonObj_hopfSpec R H.unop).mpr hG.2.2.2⟩
  · intro h
    apply (finiteLocallyFreeCommAffineGroupSchemeProperty
      (CommRingCat.of R)).prop_of_iso e.symm
    let _ : Module.Finite R H.unop := h.1
    have hprojective :=
      (moduleProjective_iff_flat_and_locallyOfFinitePresentation_hopfSpec R H.unop).mp h.2.1
    exact ⟨(moduleFinite_iff_isFinite_hopfSpec R H.unop).mp h.1,
      hprojective.1, hprojective.2,
      (isCocomm_iff_isCommMonObj_hopfSpec R H.unop).mp h.2.2⟩

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

/-- The forward functor of general-base Cartier duality is finite dualization transported through
the finite-locally-free Hopf--spectrum anti-equivalence. -/
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
