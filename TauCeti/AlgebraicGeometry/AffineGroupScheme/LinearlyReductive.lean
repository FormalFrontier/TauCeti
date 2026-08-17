/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.LinearlyReductive
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Basic
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Equivalence

/-!
# Linearly reductive affine group schemes

This file transports linear reductivity from commutative Hopf algebras to affine group schemes
over a field. The coordinate-ring predicate says that every finite-dimensional comodule is
completely reducible; the affine Hopf/group-scheme anti-equivalence makes this an intrinsic,
isomorphism-invariant property of the represented group scheme.

The resulting full subcategories remain anti-equivalent. The compatibility isomorphism with
`hopfSpec` is provided so later comparison theorems can compute on coordinate rings without
unfolding either restricted equivalence.

## Main declarations

* `TauCeti.linearlyReductiveAffineGroupSchemeProperty`: linear reductivity of affine group
  schemes over a field.
* `TauCeti.LinearlyReductiveAffineGroupSchemeCat`: the corresponding full subcategory.
* `TauCeti.linearlyReductiveCommHopfAlgCatOpEquivLinearlyReductiveAffineGroupSchemeCat`: the
  restricted Hopf-algebra/group-scheme anti-equivalence.
* `TauCeti.DiagonalizableGroup.linearlyReductiveAffineGroupSchemeProperty_groupScheme`: every
  finite-type diagonalizable group scheme is linearly reductive.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 3.2.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.12.

This synchronizes the coordinate-ring and group-scheme views for the complete-reducibility
characterization in Layer 6 of the ReductiveGroups roadmap.
-/

public section

namespace TauCeti

open CategoryTheory AlgebraicGeometry Opposite

universe u

/-- The object property selecting linearly reductive affine group schemes over a field.

The property is transported through the affine Hopf/group-scheme anti-equivalence and therefore
does not add smoothness, connectedness, or finite type to the ambient affine group. -/
def linearlyReductiveAffineGroupSchemeProperty (k : Type u) [Field k] :
    ObjectProperty (AffineGroupSchemeCat (CommRingCat.of k)) :=
  (linearlyReductiveCommHopfAlgProperty.{u, u, u} k).op.inverseImage
    (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of k)).inverse

/-- An affine group scheme is linearly reductive exactly when the coordinate Hopf algebra
recovered by the affine anti-equivalence is linearly reductive. -/
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
      (linearlyReductiveCommHopfAlgProperty.{u, u, u} k).op := by
  ext H
  exact ((linearlyReductiveCommHopfAlgProperty.{u, u, u} k).op.prop_iff_of_iso
    ((commHopfAlgCatOpEquivAffineGroupSchemeCat
      (CommRingCat.of k)).unitIso.app H)).symm

/-- `Spec` restricts to an anti-equivalence from linearly reductive commutative Hopf algebras to
linearly reductive affine group schemes. -/
noncomputable def
    linearlyReductiveCommHopfAlgCatOpEquivLinearlyReductiveAffineGroupSchemeCat
    (k : Type u) [Field k] :
    (LinearlyReductiveCommHopfAlgCat.{u, u, u} k)ᵒᵖ ≌
      LinearlyReductiveAffineGroupSchemeCat k :=
  (ObjectProperty.opEquivalence
      (linearlyReductiveCommHopfAlgProperty.{u, u, u} k)).symm.trans <|
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
      (forget₂ (LinearlyReductiveCommHopfAlgCat.{u, u, u} k)
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
      (forget₂ (LinearlyReductiveCommHopfAlgCat.{u, u, u} k)
          (CommHopfAlgCat.{u} k)).op ⋙
        hopfSpec (CommRingCat.of k) :=
  Functor.isoWhiskerRight
      (linearlyReductiveCommHopfAlgCatOpEquivLinearlyReductiveAffineGroupSchemeCatFunctorCompιIso
        k)
      ((affineGroupSchemeProperty (CommRingCat.of k)).ι) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (forget₂ (LinearlyReductiveCommHopfAlgCat.{u, u, u} k)
        (CommHopfAlgCat.{u} k)).op
      (commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
        (CommRingCat.of k))

namespace DiagonalizableGroup

/-- Every finite-type diagonalizable group scheme is linearly reductive. -/
theorem linearlyReductiveAffineGroupSchemeProperty_groupScheme
    (k : Type u) [Field k] (G : FGCommGrpCat.{u}) :
    linearlyReductiveAffineGroupSchemeProperty k
      ⟨groupScheme k G, (affineGroupSchemeProperty_iff _).2 inferInstance⟩ := by
  let H : CommHopfAlgCat.{u} k := (coordinateRing k G).obj
  let E := commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of k)
  have hE : linearlyReductiveAffineGroupSchemeProperty k (E.functor.obj (op H)) := by
    have h : ((linearlyReductiveAffineGroupSchemeProperty k).inverseImage E.functor) (op H) := by
      rw [linearlyReductiveAffineGroupSchemeProperty_inverseImage, ObjectProperty.op_iff]
      exact (linearlyReductiveCommHopfAlgProperty_iff k H).2
        (Coalgebra.isLinearlyReductive_monoidAlgebra k G)
    exact h
  let e : E.functor.obj (op H) ≅
      (⟨groupScheme k G, (affineGroupSchemeProperty_iff _).2 inferInstance⟩ :
        AffineGroupSchemeCat (CommRingCat.of k)) :=
    (affineGroupSchemeProperty (CommRingCat.of k)).ι.preimageIso
      ((commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
          (CommRingCat.of k)).app (op H) ≪≫
        (schemeFunctorIsoHopfSpec k).symm.app (op G) ≪≫
        eqToIso (schemeFunctor_obj k (op G)))
  exact (linearlyReductiveAffineGroupSchemeProperty k).prop_of_iso e hE

end DiagonalizableGroup

end TauCeti
