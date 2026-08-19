/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.CategoryTheory.ObjectProperty
public import TauCeti.Algebra.AlgebraicGroup.Radical.Basic
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Connected
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Smooth

/-!
# Geometric normal-subgroup-freeness for affine group schemes

This file transports the generic coordinate-Hopf property
`geometricNormalSubgroupFreeCommHopfAlgProperty` across the finite-type affine
Hopf/group-scheme anti-equivalence. It packages the common scheme-side construction used by
reductive and semisimple affine group schemes, including their smoothness, geometric
connectedness, restricted anti-equivalence, and `hopfSpec` computation interface.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§6.46 and 19.b.
* T. A. Springer, *Linear Algebraic Groups*, Chapter 8.
* B. Conrad, *Reductive Group Schemes*, Section 3.
* The categorical restriction and smoothness transport follow the formal pattern in
  `TauCeti.AlgebraicGeometry.AffineGroupScheme.Unipotent`.

## Main declarations

* `TauCeti.geometricNormalSubgroupFreeAffineGroupSchemeProperty`: the transported object
  property on finite-type affine group schemes.
* `TauCeti.smooth_of_geometricNormalSubgroupFreeAffineGroupSchemeProperty` and
  `TauCeti.geometricallyConnected_of_geometricNormalSubgroupFreeAffineGroupSchemeProperty`:
  structural consequences of the transported property.
* `TauCeti.geometricNormalSubgroupFreeCommHopfAlgCatOpEquivAffineGroupSchemeCat`: the restricted
  affine Hopf/group-scheme anti-equivalence.
* `TauCeti.geometricNormalSubgroupFreeCommHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso`:
  its `hopfSpec` computation interface.

This is shared infrastructure for the reductive and semisimple definitions in Layer 6,
"Reductive and semisimple groups", of the ReductiveGroups roadmap.
-/

public section

namespace TauCeti

open CategoryTheory AlgebraicGeometry Opposite

universe u

/-- The scheme-side form of a geometric normal-subgroup-freeness property.

The candidate subgroup property `P` is imposed on finite-type coordinate Hopf algebras over an
algebraic closure. -/
def geometricNormalSubgroupFreeAffineGroupSchemeProperty
    (k : Type u) [Field k]
    (P : ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k))) :
    ObjectProperty (FiniteTypeAffineGroupSchemeCat (CommRingCat.of k)) :=
  (geometricNormalSubgroupFreeCommHopfAlgProperty k P).op.inverseImage
    (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse

/-- A finite-type affine group scheme has the transported normal-subgroup-freeness property
exactly when its coordinate Hopf algebra has the corresponding coordinate-side property. -/
@[simp]
theorem geometricNormalSubgroupFreeAffineGroupSchemeProperty_iff
    (k : Type u) [Field k]
    (P : ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k)))
    (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k)) :
    geometricNormalSubgroupFreeAffineGroupSchemeProperty k P G ↔
      geometricNormalSubgroupFreeCommHopfAlgProperty k P
        ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse.obj G).unop :=
  Iff.rfl

/-- Geometric normal-subgroup-freeness of finite-type affine group schemes is invariant under
isomorphism. -/
instance (k : Type u) [Field k]
    (P : ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k)))
    [P.IsClosedUnderIsomorphisms] :
    (geometricNormalSubgroupFreeAffineGroupSchemeProperty k P).IsClosedUnderIsomorphisms := by
  unfold geometricNormalSubgroupFreeAffineGroupSchemeProperty
  infer_instance

/-- A finite-type affine group scheme with a geometric normal-subgroup-freeness property has
smooth structural morphism. -/
theorem smooth_of_geometricNormalSubgroupFreeAffineGroupSchemeProperty
    (k : Type u) [Field k]
    (P : ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k)))
    (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k))
    (hG : geometricNormalSubgroupFreeAffineGroupSchemeProperty k P G) :
    Smooth G.obj.obj.X.hom := by
  exact (smooth_iff_algebraSmooth_coordinate k G).mpr
    ((geometricNormalSubgroupFreeAffineGroupSchemeProperty_iff k P G).mp hG).smooth

/-- A finite-type affine group scheme with a geometric normal-subgroup-freeness property has
geometrically connected structural morphism. -/
theorem geometricallyConnected_of_geometricNormalSubgroupFreeAffineGroupSchemeProperty
    (k : Type u) [Field k]
    (P : ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k)))
    (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k))
    (hG : geometricNormalSubgroupFreeAffineGroupSchemeProperty k P G) :
    GeometricallyConnected G.obj.obj.X.hom := by
  exact (geometricallyConnected_iff_geometricallyConnected_coordinate k G).mpr
    ((geometricNormalSubgroupFreeAffineGroupSchemeProperty_iff k P G).mp hG).geometricallyConnected

/-- Under the finite-type affine Hopf/group-scheme anti-equivalence, the inverse image of the
scheme-side property is the coordinate-side geometric normal-subgroup-freeness property. -/
theorem geometricNormalSubgroupFreeAffineGroupSchemeProperty_inverseImage
    (k : Type u) [Field k]
    (P : ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k)))
    (Q : ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} k))
    [Q.IsClosedUnderIsomorphisms]
    (hQ : Q = geometricNormalSubgroupFreeCommHopfAlgProperty k P) :
    (geometricNormalSubgroupFreeAffineGroupSchemeProperty k P).inverseImage
        (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).functor =
      Q.op := by
  subst Q
  unfold geometricNormalSubgroupFreeAffineGroupSchemeProperty
  exact ObjectProperty.inverseImage_functor_inverseImage_inverse _ _

/-- `Spec` restricts to an anti-equivalence for a geometric normal-subgroup-freeness property. -/
noncomputable def geometricNormalSubgroupFreeCommHopfAlgCatOpEquivAffineGroupSchemeCat
    (k : Type u) [Field k]
    (P : ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k)))
    (Q : ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} k))
    [P.IsClosedUnderIsomorphisms]
    (hQ : Q = geometricNormalSubgroupFreeCommHopfAlgProperty k P) :
    Q.FullSubcategoryᵒᵖ ≌
      (geometricNormalSubgroupFreeAffineGroupSchemeProperty k P).FullSubcategory := by
  letI : Q.IsClosedUnderIsomorphisms := by
    rw [hQ]
    infer_instance
  exact (ObjectProperty.opEquivalence Q).symm.trans <|
    (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).congrFullSubcategory
      (geometricNormalSubgroupFreeAffineGroupSchemeProperty_inverseImage k P Q hQ)

/-- The generic restricted anti-equivalence followed by the property inclusion is the
finite-type anti-equivalence after forgetting the property proof. -/
private noncomputable def
    geometricNormalSubgroupFreeCommHopfAlgCatOpEquivAffineGroupSchemeCatFunctorCompιIso
    (k : Type u) [Field k]
    (P : ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k)))
    (Q : ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} k))
    [P.IsClosedUnderIsomorphisms]
    (hQ : Q = geometricNormalSubgroupFreeCommHopfAlgProperty k P) :
    (geometricNormalSubgroupFreeCommHopfAlgCatOpEquivAffineGroupSchemeCat k P Q hQ).functor ⋙
        (geometricNormalSubgroupFreeAffineGroupSchemeProperty k P).ι ≅
      Q.ι.op ⋙ (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).functor := by
  letI : Q.IsClosedUnderIsomorphisms := by
    rw [hQ]
    infer_instance
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.opEquivalence Q).symm.functor
      ((geometricNormalSubgroupFreeAffineGroupSchemeProperty k P).liftCompιIso
        (Q.op.ι ⋙
          (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).functor) _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Q.op.liftCompιIso Q.ι.op (fun X => X.unop.property))
      (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).functor

/-- The restricted anti-equivalence followed by the inclusions into affine group schemes is
Mathlib's `hopfSpec` after forgetting the property and finite-type proofs. -/
noncomputable def
    geometricNormalSubgroupFreeCommHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
    (k : Type u) [Field k]
    (P : ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k)))
    (Q : ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} k))
    [P.IsClosedUnderIsomorphisms]
    (hQ : Q = geometricNormalSubgroupFreeCommHopfAlgProperty k P) :
    (geometricNormalSubgroupFreeCommHopfAlgCatOpEquivAffineGroupSchemeCat k P Q hQ).functor ⋙
          (geometricNormalSubgroupFreeAffineGroupSchemeProperty k P).ι ⋙
          (finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι ⋙
        (affineGroupSchemeProperty (CommRingCat.of k)).ι ≅
      Q.ι.op ⋙
        (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
          (CommHopfAlgCat.{u} k)).op ⋙ hopfSpec (CommRingCat.of k) := by
  letI : Q.IsClosedUnderIsomorphisms := by
    rw [hQ]
    infer_instance
  exact Functor.isoWhiskerRight
      (geometricNormalSubgroupFreeCommHopfAlgCatOpEquivAffineGroupSchemeCatFunctorCompιIso
        k P Q hQ)
      ((finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι ⋙
        (affineGroupSchemeProperty (CommRingCat.of k)).ι) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft Q.ι.op
      (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat.functorCompιIso k)

end TauCeti
