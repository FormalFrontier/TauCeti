/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

import TauCeti.CategoryTheory.ObjectProperty
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Basic
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Basic
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.FiniteType

/-!
# Affine group schemes of multiplicative type

This file transports the coordinate-Hopf-algebra definition of a group of multiplicative type to
finite-type affine group schemes over a field. A group scheme is of multiplicative type when its
coordinate Hopf algebra becomes diagonalizable after extension to an algebraic closure.

The resulting full subcategory is anti-equivalent to multiplicative-type coordinate Hopf
algebras. This synchronizes the coordinate and scheme models without requiring the group to split
over the ground field; finite diagonalizable groups and non-split tori both belong to the resulting
category.

## Main declarations

* `TauCeti.multiplicativeTypeAffineGroupSchemeProperty`: the multiplicative-type property for
  finite-type affine group schemes over a field.
* `TauCeti.MultiplicativeTypeAffineGroupSchemeCat`: the corresponding full subcategory.
* `TauCeti.DiagonalizableGroup.multiplicativeTypeAffineGroupSchemeProperty_groupScheme`: every
  canonical finite-type diagonalizable group scheme is of multiplicative type.
* `TauCeti.multiplicativeTypeCommHopfAlgCatOpEquivMultiplicativeTypeAffineGroupSchemeCat`: the
  restricted affine Hopf/group-scheme anti-equivalence.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definition 12.14 and Theorem 12.23.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.

This supplies the scheme-side model required by Layer 4, "Diagonalizable groups and groups of
multiplicative type", of the ReductiveGroups roadmap. The construction follows the transport
pattern of `TauCeti.AlgebraicGeometry.AffineGroupScheme.Torus`.
-/

public section

namespace TauCeti

open CategoryTheory AlgebraicGeometry Opposite

universe u

/-- The object property selecting affine group schemes of multiplicative type over a field.

The property is transported through the finite-type affine Hopf/group-scheme anti-equivalence,
so it retains the coordinate definition by diagonalizability after extension to an algebraic
closure. -/
def multiplicativeTypeAffineGroupSchemeProperty (k : Type u) [Field k] :
    ObjectProperty (FiniteTypeAffineGroupSchemeCat (CommRingCat.of k)) :=
  (multiplicativeTypeCommHopfAlgProperty k).op.inverseImage
    (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse

/-- A finite-type affine group scheme is of multiplicative type exactly when its coordinate Hopf
algebra, supplied by the affine anti-equivalence, is of multiplicative type. -/
@[simp]
theorem multiplicativeTypeAffineGroupSchemeProperty_iff
    (k : Type u) [Field k]
    (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k)) :
    multiplicativeTypeAffineGroupSchemeProperty k G ↔
      multiplicativeTypeCommHopfAlgProperty k
        ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse.obj G).unop :=
  Iff.rfl

/-- Being of multiplicative type is invariant under isomorphisms of finite-type affine group
schemes. -/
instance (k : Type u) [Field k] :
    (multiplicativeTypeAffineGroupSchemeProperty k).IsClosedUnderIsomorphisms := by
  unfold multiplicativeTypeAffineGroupSchemeProperty
  infer_instance

/-- The category of finite-type affine group schemes of multiplicative type over a field. -/
abbrev MultiplicativeTypeAffineGroupSchemeCat (k : Type u) [Field k] :=
  (multiplicativeTypeAffineGroupSchemeProperty k).FullSubcategory

namespace DiagonalizableGroup

/-- The canonical finite-type diagonalizable group scheme `D(G)` is of multiplicative type. -/
@[grind =>]
theorem multiplicativeTypeAffineGroupSchemeProperty_groupScheme
    (k : Type u) [Field k] (G : FGCommGrpCat.{u}) :
    multiplicativeTypeAffineGroupSchemeProperty k
      ⟨⟨groupScheme k G, (affineGroupSchemeProperty_iff _).2 inferInstance⟩,
        (finiteTypeAffineGroupSchemeProperty_iff _ _).2
          (locallyOfFiniteType_groupScheme k G)⟩ := by
  let E := finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k
  let H : FiniteTypeCommHopfAlgCat.{u, u} k := coordinateRing k G
  let D : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k) :=
    ⟨⟨groupScheme k G, (affineGroupSchemeProperty_iff _).2 inferInstance⟩,
      (finiteTypeAffineGroupSchemeProperty_iff _ _).2
        (locallyOfFiniteType_groupScheme k G)⟩
  have hE : multiplicativeTypeAffineGroupSchemeProperty k (E.functor.obj (op H)) := by
    rw [multiplicativeTypeAffineGroupSchemeProperty_iff]
    exact (multiplicativeTypeCommHopfAlgProperty k).prop_of_iso
      (Iso.unop (E.unitIso.app (op H))).symm (multiplicativeType_coordinateRing k G)
  let eGrp :
      ((affineGroupSchemeProperty (CommRingCat.of k)).ι.obj
        ((finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι.obj
          (E.functor.obj (op H)))) ≅ D.obj.obj :=
    (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat.functorCompιIso k).app
        (op H) ≪≫
      eqToIso (groupScheme_def k G).symm
  let eAffine :
      (finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι.obj
          (E.functor.obj (op H)) ≅ D.obj :=
    (affineGroupSchemeProperty (CommRingCat.of k)).ι.preimageIso eGrp
  let e : E.functor.obj (op H) ≅ D :=
    (finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι.preimageIso eAffine
  exact (multiplicativeTypeAffineGroupSchemeProperty k).prop_of_iso e hE

end DiagonalizableGroup

/-- Under the finite-type affine Hopf/group-scheme anti-equivalence, the inverse image of the
multiplicative-type property on group schemes is the multiplicative-type property on coordinate
Hopf algebras. -/
theorem multiplicativeTypeAffineGroupSchemeProperty_inverseImage
    (k : Type u) [Field k] :
    (multiplicativeTypeAffineGroupSchemeProperty k).inverseImage
        (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).functor =
      (multiplicativeTypeCommHopfAlgProperty k).op := by
  unfold multiplicativeTypeAffineGroupSchemeProperty
  exact ObjectProperty.inverseImage_functor_inverseImage_inverse _ _

/-- `Spec` restricts to an anti-equivalence from multiplicative-type coordinate Hopf algebras to
affine group schemes of multiplicative type. -/
noncomputable def
    multiplicativeTypeCommHopfAlgCatOpEquivMultiplicativeTypeAffineGroupSchemeCat
    (k : Type u) [Field k] :
    (MultiplicativeTypeCommHopfAlgCat.{u} k)ᵒᵖ ≌
      MultiplicativeTypeAffineGroupSchemeCat k :=
  (ObjectProperty.opEquivalence (multiplicativeTypeCommHopfAlgProperty k)).symm.trans <|
    (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).congrFullSubcategory
      (multiplicativeTypeAffineGroupSchemeProperty_inverseImage k)

/-- The forward multiplicative-type anti-equivalence followed by the inclusion into finite-type
affine group schemes is definitionally the finite-type anti-equivalence after forgetting the
multiplicative-type property. -/
private noncomputable def
    multiplicativeTypeCommHopfAlgCatOpEquivMultiplicativeTypeAffineGroupSchemeCatFunctorCompιIso
    (k : Type u) [Field k] :
    (multiplicativeTypeCommHopfAlgCatOpEquivMultiplicativeTypeAffineGroupSchemeCat k).functor ⋙
        (multiplicativeTypeAffineGroupSchemeProperty k).ι ≅
      (forget₂ (MultiplicativeTypeCommHopfAlgCat.{u} k)
          (FiniteTypeCommHopfAlgCat.{u, u} k)).op ⋙
        (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).functor :=
  Iso.refl _

/-- The forward multiplicative-type anti-equivalence, followed by the inclusions into finite-type
affine group schemes and affine group schemes, is Mathlib's `hopfSpec` after forgetting the
multiplicative-type and finite-type proofs. -/
noncomputable def
    multiplicativeTypeCommHopfAlgCatOpEquivMultiplicativeTypeAffineGroupSchemeCat.functorCompιIso
    (k : Type u) [Field k] :
    (multiplicativeTypeCommHopfAlgCatOpEquivMultiplicativeTypeAffineGroupSchemeCat k).functor ⋙
          (multiplicativeTypeAffineGroupSchemeProperty k).ι ⋙
          (finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι ⋙
        (affineGroupSchemeProperty (CommRingCat.of k)).ι ≅
      (forget₂ (MultiplicativeTypeCommHopfAlgCat.{u} k)
          (FiniteTypeCommHopfAlgCat.{u, u} k)).op ⋙
        (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
          (CommHopfAlgCat.{u} k)).op ⋙ hopfSpec (CommRingCat.of k) :=
  (Functor.isoWhiskerRight
    (multiplicativeTypeCommHopfAlgCatOpEquivMultiplicativeTypeAffineGroupSchemeCatFunctorCompιIso
      k)
    ((finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι ⋙
      (affineGroupSchemeProperty (CommRingCat.of k)).ι)).trans <|
  (Functor.associator _ _ _).trans <|
  Functor.isoWhiskerLeft
    (forget₂ (MultiplicativeTypeCommHopfAlgCat.{u} k)
      (FiniteTypeCommHopfAlgCat.{u, u} k)).op
    (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat.functorCompιIso k)

end TauCeti
