/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import TauCeti.Algebra.HopfAlgebra.FiniteDual.Equivalence
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Equivalence
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec

/-!
# Cartier duality for finite commutative affine group schemes

This file transports finite-dimensional Cartier duality from coordinate Hopf algebras to affine
group schemes over a field. A Hopf spectrum is finite over the base precisely when its coordinate
algebra is finite-dimensional, and it is a commutative group object precisely when its coordinate
Hopf algebra is cocommutative.

## Main declarations

* `TauCeti.finiteCommAffineGroupSchemeProperty`: the object property selecting finite
  commutative affine group schemes over a base ring.
* `TauCeti.finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat`: the restricted
  Hopf--`Spec` anti-equivalence.
* `TauCeti.finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat.functorCompιIso`:
  after both inclusions, the restricted equivalence is Mathlib's `hopfSpec`.
* `TauCeti.finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat.inverseCompιIso`:
  after inclusion, the restricted inverse is the unrestricted inverse.
* `TauCeti.FiniteCommAffineGroupSchemeCat.cartierDuality`: Cartier duality transported to finite
  commutative affine group schemes over a field.
* `TauCeti.FiniteCommAffineGroupSchemeCat.cartierDuality_functor`: its computation as transported
  finite dualization.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
* J. S. Milne, *Algebraic Groups* (2017), Section 12.e.

This completes the field-level scheme transport in Layer 4, "Cartier duality", of the
ReductiveGroups roadmap. Extension to finite locally free group schemes over a general base is a
separate step.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace TauCeti

universe u

/-- The object property selecting finite commutative affine group schemes over a base ring. -/
def finiteCommAffineGroupSchemeProperty (S : CommRingCat.{u}) :
    ObjectProperty (AffineGroupSchemeCat S) :=
  fun G => IsFinite G.obj.X.hom ∧ IsCommMonObj G.obj.X

/-- Membership in the finite-commutative affine-group-scheme property. -/
@[simp]
theorem finiteCommAffineGroupSchemeProperty_iff
    (S : CommRingCat.{u}) (G : AffineGroupSchemeCat S) :
    finiteCommAffineGroupSchemeProperty S G ↔
      IsFinite G.obj.X.hom ∧ IsCommMonObj G.obj.X :=
  Iff.rfl

private theorem isCommMonObj_of_grp_iso
    {C : Type u} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
    {G H : Grp C} (e : G ≅ H) (hG : IsCommMonObj G.X) : IsCommMonObj H.X := by
  let _ := hG
  constructor
  apply (cancel_mono e.inv.hom.hom).1
  simp only [Category.assoc, IsMonHom.mul_hom]
  rw [← Category.assoc, ← BraidedCategory.braiding_naturality]
  simp only [Category.assoc, IsCommMonObj.mul_comm]

instance (S : CommRingCat.{u}) :
    (finiteCommAffineGroupSchemeProperty S).IsClosedUnderIsomorphisms where
  of_iso e hG := by
    constructor
    · exact (MorphismProperty.over_iso_iff (@IsFinite)
        ((Grp.forget _).mapIso
          ((affineGroupSchemeProperty S).ι.mapIso e))).mp hG.1
    · exact isCommMonObj_of_grp_iso
        ((affineGroupSchemeProperty S).ι.mapIso e) hG.2

/-- Under the affine Hopf/group-scheme anti-equivalence, module-finiteness and
cocommutativity of the coordinate Hopf algebra correspond to finiteness and commutativity of the
affine group scheme. -/
theorem finiteCommAffineGroupSchemeProperty_inverseImage
    (R : Type u) [CommRing R] :
    (finiteCommAffineGroupSchemeProperty (CommRingCat.of R)).inverseImage
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).functor =
      (finiteBicommutativeHopfAlgProperty R).op := by
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
    finiteCommAffineGroupSchemeProperty_iff, ObjectProperty.op_iff,
    finiteBicommutativeHopfAlgProperty_iff]
  constructor
  · intro h
    have hG : finiteCommAffineGroupSchemeProperty (CommRingCat.of R) G :=
      (finiteCommAffineGroupSchemeProperty (CommRingCat.of R)).prop_of_iso e h
    exact ⟨(moduleFinite_iff_isFinite_hopfSpec R H.unop).mpr hG.1,
      (isCocomm_iff_isCommMonObj_hopfSpec R H.unop).mpr hG.2⟩
  · intro h
    apply (finiteCommAffineGroupSchemeProperty (CommRingCat.of R)).prop_of_iso e.symm
    exact ⟨(moduleFinite_iff_isFinite_hopfSpec R H.unop).mp h.1,
      (isCocomm_iff_isCommMonObj_hopfSpec R H.unop).mp h.2⟩

/-- The category of finite commutative affine group schemes over a base ring. -/
abbrev FiniteCommAffineGroupSchemeCat (S : CommRingCat.{u}) :=
  (finiteCommAffineGroupSchemeProperty S).FullSubcategory

instance {S : CommRingCat.{u}} (G : FiniteCommAffineGroupSchemeCat S) :
    IsFinite G.obj.obj.X.hom :=
  G.property.1

instance {S : CommRingCat.{u}} (G : FiniteCommAffineGroupSchemeCat S) :
    IsCommMonObj G.obj.obj.X :=
  G.property.2

/-- `Spec` as an anti-equivalence from module-finite bicommutative Hopf algebras to finite
commutative affine group schemes over a commutative ring. -/
noncomputable def finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat
    (R : Type u) [CommRing R] :
    (FiniteBicommutativeHopfAlgCat.{u} R)ᵒᵖ ≌
      FiniteCommAffineGroupSchemeCat (CommRingCat.of R) :=
  (ObjectProperty.opEquivalence (finiteBicommutativeHopfAlgProperty R)).symm.trans <|
    (commHopfAlgCatOpEquivAffineGroupSchemeCat
      (CommRingCat.of R)).congrFullSubcategory
        (finiteCommAffineGroupSchemeProperty_inverseImage R)

/-- The restricted equivalence followed by the finite-commutative inclusion is definitionally
the unrestricted equivalence applied after forgetting the finiteness and cocommutativity proofs.
This private isomorphism isolates the implementation of the object-property restrictions. -/
private noncomputable def
    finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCatFunctorCompιIso
    (R : Type u) [CommRing R] :
    (finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat R).functor ⋙
        (finiteCommAffineGroupSchemeProperty (CommRingCat.of R)).ι ≅
      (forget₂ (FiniteBicommutativeHopfAlgCat.{u} R)
          (CommHopfAlgCat.{u} R)).op ⋙
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).functor :=
  Iso.refl _

/-- The forward restricted anti-equivalence, followed by the inclusions into affine group schemes
and all group schemes, is `hopfSpec` applied after forgetting the finiteness and cocommutativity
proofs. This is the computation interface for the restricted equivalence. -/
noncomputable def
    finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat.functorCompιIso
    (R : Type u) [CommRing R] :
    (finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat R).functor ⋙
          (finiteCommAffineGroupSchemeProperty (CommRingCat.of R)).ι ⋙
        (affineGroupSchemeProperty (CommRingCat.of R)).ι ≅
      (forget₂ (FiniteBicommutativeHopfAlgCat.{u} R)
          (CommHopfAlgCat.{u} R)).op ⋙ hopfSpec (CommRingCat.of R) :=
  Functor.isoWhiskerRight
      (finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCatFunctorCompιIso R)
      (affineGroupSchemeProperty (CommRingCat.of R)).ι ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (forget₂ (FiniteBicommutativeHopfAlgCat.{u} R)
        (CommHopfAlgCat.{u} R)).op
      (commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
        (CommRingCat.of R))

/-- The inverse restricted anti-equivalence, followed by the inclusion into commutative Hopf
algebras, is the unrestricted inverse applied after including finite commutative affine group
schemes into affine group schemes. -/
noncomputable def
    finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat.inverseCompιIso
    (R : Type u) [CommRing R] :
    (finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat R).inverse ⋙
        (forget₂ (FiniteBicommutativeHopfAlgCat.{u} R)
          (CommHopfAlgCat.{u} R)).op ≅
      (finiteCommAffineGroupSchemeProperty (CommRingCat.of R)).ι ⋙
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).inverse :=
  Iso.refl _

/-- The `rightOp` inverse used in scheme-level Cartier duality computes, after forgetting
module-finiteness and cocommutativity, as the opposite of the unrestricted coordinate Hopf-algebra
functor. -/
noncomputable def
    finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat.rightOpInverseCompιIso
    (R : Type u) [CommRing R] :
    (finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat R).rightOp.inverse ⋙
        forget₂ (FiniteBicommutativeHopfAlgCat.{u} R) (CommHopfAlgCat.{u} R) ≅
      ((finiteCommAffineGroupSchemeProperty (CommRingCat.of R)).ι ⋙
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).inverse).leftOp := by
  let e :=
    finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat.inverseCompιIso R
  exact
    { hom := e.inv.leftOp
      inv := e.hom.leftOp }

namespace FiniteCommAffineGroupSchemeCat

/-- **Cartier duality for finite commutative affine group schemes over a field.** -/
noncomputable def cartierDuality
    (k : Type u) [Field k] :
    (FiniteCommAffineGroupSchemeCat (CommRingCat.of k))ᵒᵖ ≌
      FiniteCommAffineGroupSchemeCat (CommRingCat.of k) :=
  ((finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat k).rightOp).symm.trans <|
    ((FiniteBicommutativeHopfAlgCat.dualFunctor (k := k)).rightOp).asEquivalence |>.trans
      (finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat k)

/-- The forward functor of scheme-level Cartier duality is finite dualization transported through
the restricted Hopf--`Spec` equivalence. Together with `rightOpInverseCompιIso` and
`functorCompιIso`, this describes both coordinate-algebra extraction and reconstruction without
unfolding the restricted equivalence. -/
@[simp]
theorem cartierDuality_functor (k : Type u) [Field k] :
    (cartierDuality k).functor =
      (finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat k).rightOp.inverse ⋙
        (FiniteBicommutativeHopfAlgCat.dualFunctor (k := k)).rightOp ⋙
        (finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat k).functor :=
  by simp [cartierDuality]

end FiniteCommAffineGroupSchemeCat

end TauCeti
