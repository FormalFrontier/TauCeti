/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import TauCeti.CategoryTheory.Preadditive.Indecomposable
public import TauCeti.RingTheory.KrullSchmidt.Indecomposable

/-!
# Indecomposable modules are the indecomposable objects of `ModuleCat`

`TauCeti.IsIndecomposableModule A M` says that `M` is nonzero and is not the internal direct sum of
two nonzero submodules; `CategoryTheory.Indecomposable X` says that `X` is not a zero object and
that in every decomposition `X ≅ Y ⊞ Z` one of `Y`, `Z` is zero. This file identifies the two for
objects of `ModuleCat A`, so that a client working with representations — where categorical
indecomposability is the natural interface — can reach Fitting's lemma and the Krull-Schmidt
theorem, which are stated for the module predicate.

## Main results

* `TauCeti.indecomposable_iff_isIndecomposableModule`: an object of `ModuleCat A` is indecomposable
  exactly when its underlying module is. A bare module `M` reads the same equivalence off as
  `indecomposable_iff_isIndecomposableModule (ModuleCat.of A M)`.
* `TauCeti.indecomposable_iff_isLocalRing_end`: an object of `ModuleCat A` whose underlying module
  has finite length is indecomposable exactly when `CategoryTheory.End` of it is local, which is
  Fitting's lemma stated categorically.

## Implementation notes

Both sides reduce to the triviality of the idempotent endomorphisms, by
`TauCeti.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem` on the module side and
`TauCeti.indecomposable_iff_idempotent_eq_zero_or_id` on the categorical side; the latter needs
idempotents to split, which holds because `ModuleCat A` is abelian
(`CategoryTheory.Idempotents.isIdempotentComplete_of_abelian`). The two idempotent conditions match
because `ModuleCat.Hom.hom` is a ring isomorphism `End M ≃+* Module.End A M`
(`ModuleCat.endRingEquiv`), and the remaining halves match because a module object is a zero object
exactly when its carrier is subsingleton (`ModuleCat.isZero_iff_subsingleton`).

## References

This supplies the categorical reading of Layer 2 ("the Krull-Schmidt theorem") of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, whose uniqueness bullet asks
for the module-level theory to be transported "to `QuiverRep k Q` and to categorical biproducts";
`QuiverRep k Q` is identified with `ModuleCat (pathAlgebra k Q)` there, so this equivalence is the
step that carries indecomposability across.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

variable {A : Type u} [Ring A]

/-- **An object of `ModuleCat A` is indecomposable exactly when its underlying module is.** Both
sides say that the object is nonzero and carries no idempotent endomorphism other than `0` and the
identity; on the categorical side that reformulation is
`TauCeti.indecomposable_iff_idempotent_eq_zero_or_id`, available because `ModuleCat A` is
abelian, hence idempotent complete. -/
theorem indecomposable_iff_isIndecomposableModule (M : ModuleCat.{v} A) :
    Indecomposable M ↔ IsIndecomposableModule A M := by
  rw [indecomposable_iff_idempotent_eq_zero_or_id,
    isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem,
    ← not_subsingleton_iff_nontrivial, ← ModuleCat.isZero_iff_subsingleton]
  refine and_congr_right fun _ ↦ ⟨fun h f hf ↦ ?_, fun h e he ↦ ?_⟩
  · exact (h (ModuleCat.ofHom f) (ModuleCat.hom_ext hf)).imp (congrArg ModuleCat.Hom.hom)
      (congrArg ModuleCat.Hom.hom)
  · exact (h e.hom (ModuleCat.hom_ext_iff.mp he)).imp ModuleCat.hom_ext ModuleCat.hom_ext

/-- **Fitting's lemma, categorically**: an object of `ModuleCat A` whose underlying module has
finite length is indecomposable exactly when its ring of endomorphisms in the category is local. -/
theorem indecomposable_iff_isLocalRing_end (M : ModuleCat.{v} A) (hM : IsFiniteLength A M) :
    Indecomposable M ↔ IsLocalRing (End M) := by
  rw [indecomposable_iff_isIndecomposableModule, isIndecomposableModule_iff_isLocalRing_end hM]
  exact ⟨fun _ ↦ IsLocalRing.of_ringEquiv M.endRingEquiv.symm,
    fun _ ↦ IsLocalRing.of_ringEquiv M.endRingEquiv⟩

end TauCeti
