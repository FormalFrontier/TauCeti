/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

import TauCeti.CategoryTheory.ObjectProperty
public import TauCeti.Algebra.AlgebraicGroup.Torus.Reductive
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.MultiplicativeType
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Reductive

/-!
# Torus affine group schemes

This file transports the coordinate-Hopf-algebra definition of a torus to finite-type affine
group schemes over a field. A group scheme is a torus when its coordinate Hopf algebra becomes a
finite-rank split-torus coordinate ring after extension to an algebraic closure.

The resulting full subcategory is anti-equivalent to torus coordinate Hopf algebras. Every object
in it is of multiplicative type and reductive, synchronizing these structural theorems between the
coordinate and scheme models.

## Main declarations

* `TauCeti.torusAffineGroupSchemeProperty`: the torus property for finite-type affine group
  schemes over a field.
* `TauCeti.TorusAffineGroupSchemeCat`: the corresponding full subcategory.
* `TauCeti.torusAffineGroupSchemeProperty.multiplicativeType`: every torus affine group scheme is
  of multiplicative type.
* `TauCeti.torusAffineGroupSchemeProperty.reductive`: every torus affine group scheme is
  reductive.
* `TauCeti.smooth_of_torusAffineGroupSchemeProperty` and
  `TauCeti.geometricallyConnected_of_torusAffineGroupSchemeProperty`: structural properties of
  torus affine group schemes.
* `TauCeti.torusCommHopfAlgCatOpEquivTorusAffineGroupSchemeCat`: the restricted affine
  Hopf/group-scheme anti-equivalence.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17 and Corollary 12.41.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.

This supplies the scheme-side torus model and its reductivity theorem for Layers 4 and 6 of the
ReductiveGroups roadmap.
-/

public section

namespace TauCeti

open CategoryTheory AlgebraicGeometry Opposite

universe u

/-- The object property selecting torus affine group schemes of finite type over a field.

The property is transported through the finite-type affine Hopf/group-scheme anti-equivalence,
so it retains the coordinate definition by splitting over an algebraic closure. -/
def torusAffineGroupSchemeProperty (k : Type u) [Field k] :
    ObjectProperty (FiniteTypeAffineGroupSchemeCat (CommRingCat.of k)) :=
  (torusCommHopfAlgProperty k).op.inverseImage
    (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse

/-- A finite-type affine group scheme is a torus exactly when its coordinate Hopf algebra,
supplied by the affine anti-equivalence, is a torus. -/
@[simp]
theorem torusAffineGroupSchemeProperty_iff
    (k : Type u) [Field k]
    (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k)) :
    torusAffineGroupSchemeProperty k G ↔
      torusCommHopfAlgProperty k
        ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse.obj G).unop :=
  Iff.rfl

/-- Being a torus is invariant under isomorphisms of finite-type affine group schemes. -/
instance (k : Type u) [Field k] :
    (torusAffineGroupSchemeProperty k).IsClosedUnderIsomorphisms := by
  unfold torusAffineGroupSchemeProperty
  infer_instance

/-- The category of torus affine group schemes of finite type over a field. -/
abbrev TorusAffineGroupSchemeCat (k : Type u) [Field k] :=
  (torusAffineGroupSchemeProperty k).FullSubcategory

namespace torusAffineGroupSchemeProperty

/-- Every torus affine group scheme over a field is of multiplicative type. -/
@[grind →]
theorem multiplicativeType
    (k : Type u) [Field k]
    (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k))
    (hG : torusAffineGroupSchemeProperty k G) :
    multiplicativeTypeAffineGroupSchemeProperty k G := by
  rw [multiplicativeTypeAffineGroupSchemeProperty_iff]
  exact ((torusAffineGroupSchemeProperty_iff k G).mp hG).multiplicativeType k _

/-- **Every torus affine group scheme over a field is reductive.** -/
@[grind →]
theorem reductive
    (k : Type u) [Field k]
    (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k))
    (hG : torusAffineGroupSchemeProperty k G) :
    reductiveAffineGroupSchemeProperty k G := by
  rw [reductiveAffineGroupSchemeProperty_iff]
  exact ((torusAffineGroupSchemeProperty_iff k G).mp hG).reductive

end torusAffineGroupSchemeProperty

/-- A finite-type affine group scheme satisfying the torus property has smooth structural
morphism. -/
theorem smooth_of_torusAffineGroupSchemeProperty
    (k : Type u) [Field k]
    (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k))
    (hG : torusAffineGroupSchemeProperty k G) :
    Smooth G.obj.obj.X.hom :=
  smooth_of_reductiveAffineGroupSchemeProperty k G
    (torusAffineGroupSchemeProperty.reductive k G hG)

/-- Objects of `TorusAffineGroupSchemeCat k` have smooth structural morphism. -/
instance (k : Type u) [Field k] (G : TorusAffineGroupSchemeCat k) :
    Smooth G.obj.obj.obj.X.hom :=
  smooth_of_torusAffineGroupSchemeProperty k G.obj G.property

/-- A finite-type affine group scheme satisfying the torus property has geometrically connected
structural morphism. -/
theorem geometricallyConnected_of_torusAffineGroupSchemeProperty
    (k : Type u) [Field k]
    (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k))
    (hG : torusAffineGroupSchemeProperty k G) :
    GeometricallyConnected G.obj.obj.X.hom :=
  geometricallyConnected_of_reductiveAffineGroupSchemeProperty k G
    (torusAffineGroupSchemeProperty.reductive k G hG)

/-- Objects of `TorusAffineGroupSchemeCat k` have geometrically connected structural morphism. -/
instance (k : Type u) [Field k] (G : TorusAffineGroupSchemeCat k) :
    GeometricallyConnected G.obj.obj.obj.X.hom :=
  geometricallyConnected_of_torusAffineGroupSchemeProperty k G.obj G.property

/-- Under the finite-type affine Hopf/group-scheme anti-equivalence, the inverse image of the
torus property on group schemes is the torus property on coordinate Hopf algebras. -/
theorem torusAffineGroupSchemeProperty_inverseImage
    (k : Type u) [Field k] :
    (torusAffineGroupSchemeProperty k).inverseImage
        (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).functor =
      (torusCommHopfAlgProperty k).op := by
  unfold torusAffineGroupSchemeProperty
  exact ObjectProperty.inverseImage_functor_inverseImage_inverse _ _

/-- `Spec` restricts to an anti-equivalence from torus coordinate Hopf algebras to torus affine
group schemes. -/
noncomputable def torusCommHopfAlgCatOpEquivTorusAffineGroupSchemeCat
    (k : Type u) [Field k] :
    (TorusCommHopfAlgCat.{u} k)ᵒᵖ ≌ TorusAffineGroupSchemeCat k :=
  (ObjectProperty.opEquivalence (torusCommHopfAlgProperty k)).symm.trans <|
    (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).congrFullSubcategory
      (torusAffineGroupSchemeProperty_inverseImage k)

/-- The forward torus anti-equivalence followed by the inclusions into finite-type affine group
schemes is definitionally the finite-type anti-equivalence after forgetting the torus property. -/
private noncomputable def torusCommHopfAlgCatOpEquivTorusAffineGroupSchemeCatFunctorCompιIso
    (k : Type u) [Field k] :
    (torusCommHopfAlgCatOpEquivTorusAffineGroupSchemeCat k).functor ⋙
        (torusAffineGroupSchemeProperty k).ι ≅
      (forget₂ (TorusCommHopfAlgCat.{u} k)
          (FiniteTypeCommHopfAlgCat.{u, u} k)).op ⋙
        (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).functor :=
  Iso.refl _

/-- The forward torus anti-equivalence, followed by the inclusions into finite-type affine group
schemes and affine group schemes, is Mathlib's `hopfSpec` after forgetting the torus and
finite-type proofs. This is the computation interface for the restricted equivalence. -/
noncomputable def torusCommHopfAlgCatOpEquivTorusAffineGroupSchemeCat.functorCompιIso
    (k : Type u) [Field k] :
    (torusCommHopfAlgCatOpEquivTorusAffineGroupSchemeCat k).functor ⋙
          (torusAffineGroupSchemeProperty k).ι ⋙
          (finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι ⋙
        (affineGroupSchemeProperty (CommRingCat.of k)).ι ≅
      (forget₂ (TorusCommHopfAlgCat.{u} k)
          (FiniteTypeCommHopfAlgCat.{u, u} k)).op ⋙
        (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
          (CommHopfAlgCat.{u} k)).op ⋙ hopfSpec (CommRingCat.of k) :=
  Functor.isoWhiskerRight
      (torusCommHopfAlgCatOpEquivTorusAffineGroupSchemeCatFunctorCompιIso k)
      ((finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι ⋙
        (affineGroupSchemeProperty (CommRingCat.of k)).ι) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (forget₂ (TorusCommHopfAlgCat.{u} k)
        (FiniteTypeCommHopfAlgCat.{u, u} k)).op
      (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat.functorCompιIso k)

end TauCeti
