/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.ObjectProperty
public import TauCeti.Algebra.AlgebraicGroup.LinearlyReductive
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Equivalence

/-!
# Linearly reductive affine group schemes

This file transports linear reductivity from commutative Hopf algebras to affine group schemes
over a field. The coordinate-ring predicate tests finite-dimensional comodules whose carriers
lie in `Type u`, the universe of the base field and coordinate ring; transport to a finite
standard basis shows that this implies complete reducibility in every carrier universe. The
affine Hopf/group-scheme anti-equivalence makes this an intrinsic, isomorphism-invariant property
of the represented group scheme.

The resulting full subcategories remain anti-equivalent. The compatibility isomorphism with
`hopfSpec` is provided so later comparison theorems can compute on coordinate rings without
unfolding either restricted equivalence.

## Main declarations

* `TauCeti.linearlyReductiveAffineGroupSchemeProperty`: linear reductivity of affine group
  schemes over a field.
* `TauCeti.LinearlyReductiveAffineGroupSchemeCat`: the corresponding full subcategory.
* `TauCeti.linearlyReductiveAffineGroupSchemeProperty_hopfSpec_iff`: the characterization on a
  canonical Hopf spectrum.
* `TauCeti.linearlyReductiveCommHopfAlgCatOpEquivLinearlyReductiveAffineGroupSchemeCat`: the
  restricted Hopf-algebra/group-scheme anti-equivalence.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 3.2.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.12.

This synchronizes the coordinate-ring and group-scheme views for the complete-reducibility
characterization in Layer 6 of the ReductiveGroups roadmap.

The organization follows `TauCeti/AlgebraicGeometry/AffineGroupScheme/Unipotent.lean`.
-/

public section

namespace TauCeti

open CategoryTheory AlgebraicGeometry Opposite

universe u

/-- The object property selecting affine group schemes whose finite-dimensional coordinate-ring
comodules with carriers in `Type u` are completely reducible.

The property is transported through the affine Hopf/group-scheme anti-equivalence and therefore
does not add smoothness, connectedness, or finite type to the ambient affine group. -/
def linearlyReductiveAffineGroupSchemeProperty (k : Type u) [Field k] :
    ObjectProperty (AffineGroupSchemeCat (CommRingCat.of k)) :=
  (linearlyReductiveCommHopfAlgProperty.{u, u} k).op.inverseImage
    (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of k)).inverse

/-- An affine group scheme is linearly reductive exactly when finite-dimensional comodules over
the coordinate Hopf algebra recovered by the affine anti-equivalence, with carriers in `Type u`,
are completely reducible. -/
@[simp]
theorem linearlyReductiveAffineGroupSchemeProperty_iff
    (k : Type u) [Field k] (G : AffineGroupSchemeCat (CommRingCat.of k)) :
    linearlyReductiveAffineGroupSchemeProperty k G ↔
      Coalgebra.IsLinearlyReductive.{u, u, u} k
        ((commHopfAlgCatOpEquivAffineGroupSchemeCat
          (CommRingCat.of k)).inverse.obj G).unop :=
  by
    rw [linearlyReductiveAffineGroupSchemeProperty,
      ObjectProperty.prop_inverseImage_iff, ObjectProperty.op_iff,
      linearlyReductiveCommHopfAlgProperty_iff]

/-- Linear reductivity of affine group schemes is invariant under isomorphism. -/
instance (k : Type u) [Field k] :
    (linearlyReductiveAffineGroupSchemeProperty k).IsClosedUnderIsomorphisms := by
  unfold linearlyReductiveAffineGroupSchemeProperty
  infer_instance

/-- The category of linearly reductive affine group schemes over a field. -/
abbrev LinearlyReductiveAffineGroupSchemeCat (k : Type u) [Field k] :=
  (linearlyReductiveAffineGroupSchemeProperty k).FullSubcategory

/-- Under the affine Hopf/group-scheme anti-equivalence, the inverse image of linear reductivity
on group schemes is linear reductivity of coordinate Hopf algebras. -/
theorem linearlyReductiveAffineGroupSchemeProperty_inverseImage
    (k : Type u) [Field k] :
    (linearlyReductiveAffineGroupSchemeProperty k).inverseImage
        (commHopfAlgCatOpEquivAffineGroupSchemeCat
          (CommRingCat.of k)).functor =
      (linearlyReductiveCommHopfAlgProperty.{u, u} k).op := by
  unfold linearlyReductiveAffineGroupSchemeProperty
  exact ObjectProperty.inverseImage_functor_inverseImage_inverse _ _

/-- A canonical Hopf spectrum is linearly reductive exactly when its coordinate Hopf algebra is
linearly reductive for finite-dimensional comodules with carriers in `Type u`. -/
theorem linearlyReductiveAffineGroupSchemeProperty_hopfSpec_iff
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    linearlyReductiveAffineGroupSchemeProperty k
        ⟨(hopfSpec (CommRingCat.of k)).obj (op H), by
          rw [affineGroupSchemeProperty_iff, hopfSpec_obj_X_left]
          infer_instance⟩ ↔
      Coalgebra.IsLinearlyReductive.{u, u, u} k H := by
  let E := commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of k)
  refine ((linearlyReductiveAffineGroupSchemeProperty k).prop_iff_of_iso
    (commHopfAlgCatOpEquivAffineGroupSchemeCat.functorObjIso k (op H))).symm.trans ?_
  rw [← ObjectProperty.prop_inverseImage_iff
      (linearlyReductiveAffineGroupSchemeProperty k) E.functor (op H),
    linearlyReductiveAffineGroupSchemeProperty_inverseImage,
    ObjectProperty.op_iff, linearlyReductiveCommHopfAlgProperty_iff]

/-- `Spec` restricts to an anti-equivalence from linearly reductive commutative Hopf algebras to
linearly reductive affine group schemes. -/
noncomputable def
    linearlyReductiveCommHopfAlgCatOpEquivLinearlyReductiveAffineGroupSchemeCat
    (k : Type u) [Field k] :
    (LinearlyReductiveCommHopfAlgCat.{u, u} k)ᵒᵖ ≌
      LinearlyReductiveAffineGroupSchemeCat k :=
  (ObjectProperty.opEquivalence
      (linearlyReductiveCommHopfAlgProperty.{u, u} k)).symm.trans <|
    (commHopfAlgCatOpEquivAffineGroupSchemeCat
      (CommRingCat.of k)).congrFullSubcategory
        (linearlyReductiveAffineGroupSchemeProperty_inverseImage k)

/-- The restricted anti-equivalence followed by the inclusion is the unrestricted
anti-equivalence after forgetting linear reductivity. This private isomorphism isolates the
definitional boundary of `opEquivalence` and `congrFullSubcategory`. -/
private noncomputable def
    linearlyReductiveCommHopfAlgCatOpEquivLinearlyReductiveAffineGroupSchemeCatFunctorCompιIso
    (k : Type u) [Field k] :
    (linearlyReductiveCommHopfAlgCatOpEquivLinearlyReductiveAffineGroupSchemeCat k).functor ⋙
        (linearlyReductiveAffineGroupSchemeProperty k).ι ≅
      (forget₂ (LinearlyReductiveCommHopfAlgCat.{u, u} k)
          (CommHopfAlgCat.{u} k)).op ⋙
        (commHopfAlgCatOpEquivAffineGroupSchemeCat
          (CommRingCat.of k)).functor :=
  Iso.refl _

/-- The restricted anti-equivalence followed by the inclusions into affine group schemes is
`hopfSpec` after forgetting the proof of linear reductivity. -/
noncomputable def
    linearlyReductiveCommHopfAlgCatOpEquivLinearlyReductiveAffineGroupSchemeCat.functorCompιIso
    (k : Type u) [Field k] :
    (linearlyReductiveCommHopfAlgCatOpEquivLinearlyReductiveAffineGroupSchemeCat k).functor ⋙
        (linearlyReductiveAffineGroupSchemeProperty k).ι ⋙
        (affineGroupSchemeProperty (CommRingCat.of k)).ι ≅
      (forget₂ (LinearlyReductiveCommHopfAlgCat.{u, u} k)
          (CommHopfAlgCat.{u} k)).op ⋙
        hopfSpec (CommRingCat.of k) :=
  Functor.isoWhiskerRight
      (linearlyReductiveCommHopfAlgCatOpEquivLinearlyReductiveAffineGroupSchemeCatFunctorCompιIso
        k)
      ((affineGroupSchemeProperty (CommRingCat.of k)).ι) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (forget₂ (LinearlyReductiveCommHopfAlgCat.{u, u} k)
        (CommHopfAlgCat.{u} k)).op
      (commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
        (CommRingCat.of k))

end TauCeti
