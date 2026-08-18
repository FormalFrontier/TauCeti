/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.GradedObject
public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# Internal gradings and graded objects

This file compares the two presentations of a graded module used by the `DGAInfinity` roadmap.
An `InternalGrading R M` presents all degrees inside one total module `M`, while a
`CategoryTheory.GradedObject ℤ (ModuleCat R)` presents the homogeneous modules separately.

The categorical total of the graded-object presentation of an internal grading is
canonically isomorphic to the original module. Conversely, a graded object has a canonical
internal grading on the external direct sum of its components, and recovering its graded-object
presentation gives the original object degreewise.

## Main definitions

* `InternalGrading.toGradedObject`: the family of homogeneous pieces as a Mathlib graded object.
* `InternalGrading.totalIso`: the canonical isomorphism from its categorical total to the
  original module.
* `InternalGrading.ofGradedObject`: the canonical internal grading on the external direct sum of
  a graded object.
* `InternalGrading.ofGradedObjectToGradedObjectIso`: the degreewise comparison with the original
  graded object.
-/

public section

open CategoryTheory Limits
open scoped DirectSum

namespace TauCeti

universe u v

namespace InternalGrading

section ToGradedObject

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

/-- The homogeneous pieces of an internal grading, regarded as a Mathlib graded object. -/
abbrev toGradedObject (G : InternalGrading R M) :
    GradedObject ℤ (ModuleCat.{v} R) :=
  fun p ↦ ModuleCat.of R (G.piece p)

/-- The categorical total of the graded-object presentation is the original total module. -/
noncomputable def totalIso (G : InternalGrading R M) :
    ∐ G.toGradedObject ≅ ModuleCat.of R M :=
  ModuleCat.coprodIsoDirectSum G.toGradedObject ≪≫
    (DirectSum.decomposeLinearEquiv G.piece).symm.toModuleIso

/-- On a homogeneous piece, the total comparison is the inclusion into the original module. -/
@[reassoc (attr := simp)]
theorem ι_totalIso_hom (G : InternalGrading R M) (p : ℤ) :
    Sigma.ι G.toGradedObject p ≫ G.totalIso.hom = ModuleCat.ofHom (G.piece p).subtype := by
  rw [totalIso, Iso.trans_hom, ← Category.assoc, ModuleCat.ι_coprodIsoDirectSum_hom]
  ext x
  exact DirectSum.decomposeLinearEquiv_symm_lof G.piece p x

end ToGradedObject

section OfGradedObject

variable (R : Type u) [Ring R] (X : GradedObject ℤ (ModuleCat.{v} R))

/-- The copy of the degree-`p` component inside the external direct sum of a graded object. -/
abbrev gradedObjectPiece (p : ℤ) : Submodule R (⨁ q : ℤ, X q) :=
  LinearMap.range (DirectSum.lof R ℤ (fun q ↦ X q) p)

/-- A component of a graded object is linearly equivalent to its copy in the external direct sum. -/
noncomputable def gradedObjectPieceEquiv (p : ℤ) : X p ≃ₗ[R] gradedObjectPiece R X p :=
  LinearEquiv.ofInjective (DirectSum.lof R ℤ (fun q ↦ X q) p) (DirectSum.of_injective _)

/-- The canonical component equivalence agrees with the direct-sum inclusion. -/
@[simp]
theorem gradedObjectPieceEquiv_apply (p : ℤ) (x : X p) :
    ((gradedObjectPieceEquiv R X p x : gradedObjectPiece R X p) : ⨁ q : ℤ, X q) =
      DirectSum.lof R ℤ (fun q ↦ X q) p x := by
  rw [gradedObjectPieceEquiv]
  exact LinearEquiv.ofInjective_apply _ x

private noncomputable def gradedObjectPiecesEquiv :
    (⨁ p : ℤ, X p) ≃ₗ[R] (⨁ p : ℤ, gradedObjectPiece R X p) :=
  DirectSum.congrLinearEquiv fun p ↦ gradedObjectPieceEquiv R X p

private theorem gradedObjectPiecesEquiv_symm_eq_coeLinearMap :
    (gradedObjectPiecesEquiv R X).symm.toLinearMap =
      DirectSum.coeLinearMap (gradedObjectPiece R X) := by
  apply DirectSum.linearMap_ext R
  intro p
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof]
  apply (LinearEquiv.symm_apply_eq (gradedObjectPiecesEquiv R X)).2
  obtain ⟨y, hy⟩ := x.property
  have hx : x = gradedObjectPieceEquiv R X p y := by
    apply Subtype.ext
    rw [gradedObjectPieceEquiv_apply]
    exact hy.symm
  rw [← hy, hx]
  change _ = (DirectSum.congrLinearEquiv fun p ↦ gradedObjectPieceEquiv R X p).toLinearMap
    (DirectSum.lof R ℤ (fun q ↦ X q) p y)
  rw [DirectSum.congrLinearEquiv_toLinearMap, DirectSum.lmap_lof]
  rfl

/-- The external direct sum of a graded object carries the internal grading by its canonical
component copies. -/
noncomputable def ofGradedObject : InternalGrading R (⨁ p : ℤ, X p) where
  piece := gradedObjectPiece R X
  isInternal := by
    -- `IsInternal` uses additive recomposition; its linear version has the same underlying map.
    change Function.Bijective (DirectSum.coeLinearMap (gradedObjectPiece R X))
    rw [← gradedObjectPiecesEquiv_symm_eq_coeLinearMap]
    exact (gradedObjectPiecesEquiv R X).symm.bijective

@[simp]
theorem ofGradedObject_piece (p : ℤ) :
    (ofGradedObject R X).piece p = gradedObjectPiece R X p :=
  (rfl)

/-- Recovering the graded-object presentation of the canonical internal grading returns the
original graded object degreewise. -/
noncomputable def ofGradedObjectToGradedObjectIso :
    (ofGradedObject R X).toGradedObject ≅ X := by
  apply GradedObject.isoMk
  intro p
  exact (gradedObjectPieceEquiv R X p).symm.toModuleIso

/-- The forward component of the comparison is the inverse of the canonical equivalence onto the
corresponding copy in the external direct sum. -/
@[simp]
theorem ofGradedObjectToGradedObjectIso_hom_app (p : ℤ) :
    (ofGradedObjectToGradedObjectIso R X).hom p =
      eqToHom (show (ofGradedObject R X).toGradedObject p =
        ModuleCat.of R (gradedObjectPiece R X p) from
          congrArg (fun N : Submodule R (⨁ q : ℤ, X q) ↦ ModuleCat.of R N)
            (ofGradedObject_piece R X p)) ≫
        (gradedObjectPieceEquiv R X p).symm.toModuleIso.hom := by
  rfl

/-- The inverse component of the comparison is the canonical equivalence onto the corresponding
copy in the external direct sum. -/
@[simp]
theorem ofGradedObjectToGradedObjectIso_inv_app (p : ℤ) :
    (ofGradedObjectToGradedObjectIso R X).inv p =
      (gradedObjectPieceEquiv R X p).symm.toModuleIso.inv ≫
        eqToHom (show ModuleCat.of R (gradedObjectPiece R X p) =
          (ofGradedObject R X).toGradedObject p from
            (congrArg (fun N : Submodule R (⨁ q : ℤ, X q) ↦ ModuleCat.of R N)
              (ofGradedObject_piece R X p)).symm) := by
  rfl

end OfGradedObject

end InternalGrading

end TauCeti
