/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

import TauCeti.CategoryTheory.ObjectProperty
public import TauCeti.Algebra.AlgebraicGroup.Adjoint.Basic
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Semisimple.Basic

/-!
# Adjoint semisimple affine group schemes

A semisimple affine group scheme over a field is **adjoint** when its scheme-theoretic center is
trivial.  This file transports the Hopf-coordinate property
`adjointSemisimpleCommHopfAlgProperty` across the anti-equivalence between semisimple finite-type
commutative Hopf algebras and semisimple affine group schemes.

The coordinate characterization says that the Hopf ideal defining the center is the augmentation
ideal defining the identity subgroup.  By
`adjointSemisimpleCommHopfAlgProperty_iff_forall_isCentralPoint_eq_one`, this is equivalently the
all-value-algebras statement that every universally central point is the identity.  In
particular, adjointness here detects infinitesimal centers and is stronger than triviality of the
center on points over the ground field alone.

## Main declarations

* `TauCeti.adjointSemisimpleAffineGroupSchemeProperty`: adjointness for semisimple affine group
  schemes over a field.
* `TauCeti.AdjointSemisimpleAffineGroupSchemeCat`: the corresponding full subcategory.
* `TauCeti.adjointSemisimpleAffineGroupSchemeProperty_iff`: the coordinate-Hopf
  characterization.
* `TauCeti.adjointSemisimpleCommHopfAlgCatOpEquivAdjointSemisimpleAffineGroupSchemeCat`: the
  restricted anti-equivalence between the coordinate and scheme models.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§1.k and 21.4.
* T. A. Springer, *Linear Algebraic Groups*, §9.6.

This completes the definition-level interface for adjoint forms in Layer 6, "Reductive and
semisimple groups", of the ReductiveGroups roadmap.  Construction of the represented quotient by
the center, its adjointness, and the classification of adjoint forms remain downstream.
-/

public section

namespace TauCeti

open CategoryTheory Opposite

universe u

variable {k : Type u} [Field k]

/-- The object property selecting adjoint semisimple affine group schemes over a field.

It is transported from the condition that the center defining ideal of the coordinate Hopf
algebra is its augmentation ideal.  The ambient object is already semisimple by belonging to
`SemisimpleAffineGroupSchemeCat k`. -/
def adjointSemisimpleAffineGroupSchemeProperty (k : Type u) [Field k] :
    ObjectProperty (SemisimpleAffineGroupSchemeCat k) :=
  (adjointSemisimpleCommHopfAlgProperty k).op.inverseImage
    (semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat k).inverse

/-- A semisimple affine group scheme is adjoint exactly when its coordinate Hopf algebra has
center defining ideal equal to the augmentation ideal. -/
@[simp]
theorem adjointSemisimpleAffineGroupSchemeProperty_iff
    (G : SemisimpleAffineGroupSchemeCat k) :
    adjointSemisimpleAffineGroupSchemeProperty k G ↔
      adjointSemisimpleCommHopfAlgProperty k
        ((semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat k).inverse.obj G).unop :=
  Iff.rfl

/-- Adjointness of semisimple affine group schemes is invariant under isomorphism. -/
instance (k : Type u) [Field k] :
    (adjointSemisimpleAffineGroupSchemeProperty k).IsClosedUnderIsomorphisms := by
  unfold adjointSemisimpleAffineGroupSchemeProperty
  infer_instance

/-- The category of adjoint semisimple affine group schemes over a field. -/
abbrev AdjointSemisimpleAffineGroupSchemeCat (k : Type u) [Field k] :=
  (adjointSemisimpleAffineGroupSchemeProperty k).FullSubcategory

/-- Pulling adjointness on semisimple affine group schemes back along `Spec` recovers adjointness
of semisimple commutative Hopf algebras. -/
theorem adjointSemisimpleAffineGroupSchemeProperty_inverseImage
    (k : Type u) [Field k] :
    (adjointSemisimpleAffineGroupSchemeProperty k).inverseImage
        (semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat k).functor =
      (adjointSemisimpleCommHopfAlgProperty k).op := by
  unfold adjointSemisimpleAffineGroupSchemeProperty
  exact ObjectProperty.inverseImage_functor_inverseImage_inverse _ _

/-- `Spec` restricts to an anti-equivalence from adjoint semisimple finite-type commutative Hopf
algebras to adjoint semisimple affine group schemes. -/
noncomputable def adjointSemisimpleCommHopfAlgCatOpEquivAdjointSemisimpleAffineGroupSchemeCat
    (k : Type u) [Field k] :
    (AdjointSemisimpleCommHopfAlgCat.{u} k)ᵒᵖ ≌
      AdjointSemisimpleAffineGroupSchemeCat k :=
  (ObjectProperty.opEquivalence (adjointSemisimpleCommHopfAlgProperty k)).symm.trans <|
    (semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat k).congrFullSubcategory
      (adjointSemisimpleAffineGroupSchemeProperty_inverseImage k)

/-- After forgetting adjointness, the restricted anti-equivalence is the existing semisimple
Hopf/group-scheme anti-equivalence. -/
noncomputable def
    adjointSemisimpleCommHopfAlgCatOpEquivAdjointSemisimpleAffineGroupSchemeCat.functorCompιIso
    (k : Type u) [Field k] :
    (adjointSemisimpleCommHopfAlgCatOpEquivAdjointSemisimpleAffineGroupSchemeCat k).functor ⋙
        (adjointSemisimpleAffineGroupSchemeProperty k).ι ≅
      (forget₂ (AdjointSemisimpleCommHopfAlgCat.{u} k)
          (SemisimpleCommHopfAlgCat.{u} k)).op ⋙
        (semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat k).functor := by
  let P := adjointSemisimpleCommHopfAlgProperty k
  let Q := adjointSemisimpleAffineGroupSchemeProperty k
  let e := semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat k
  let h := adjointSemisimpleAffineGroupSchemeProperty_inverseImage k
  exact
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (ObjectProperty.opEquivalence P).symm.functor
        (Q.liftCompιIso (P.op.ι ⋙ e.functor) (fun X ↦
          (congrFun h X.obj).symm.mp X.property)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (P.op.liftCompιIso P.ι.op (fun X ↦ X.unop.property)) e.functor

end TauCeti
