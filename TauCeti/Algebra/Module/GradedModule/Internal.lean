/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Internally graded modules

This file packages a `ℤ`-graded module as a total module together with an internal direct-sum
decomposition. The total-module presentation is convenient for DG and `A∞` operations, while
`DirectSum.IsInternal` ensures that every element is a finite, uniquely determined sum of
homogeneous elements.

Mathlib already provides the direct-sum equivalence and its induction principle through
`DirectSum.Decomposition`.  An `InternalGrading` retains the family of homogeneous submodules and
the proof that it is internal; the instance below makes Mathlib's decomposition API available
without duplicating it.

## Main definitions

* `InternalGrading`: an internal `ℤ`-grading of a module.

## Main results

* `TauCeti.isInternal_comp_symm`: reindexing an internal decomposition along an equivalence
  preserves internality.
* `TauCeti.InternalGrading.ext`: internal gradings are determined by their homogeneous pieces.

This is the first graded-module target in Layer 0 of the `DGAInfinity` roadmap.  Later files use
Mathlib's decomposition API to define maps of nonzero degree, shifts, tensor-product gradings, and
signed multilinear operations.
-/

public section

open scoped DirectSum

namespace TauCeti

universe u v

/-- Reindexing an internal direct-sum decomposition along an equivalence of index types again
gives an internal decomposition: the reindexing only permutes the summands. -/
theorem isInternal_comp_symm {ι : Type*} {κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {M : Type*} {σ : Type*} [AddCommMonoid M] [SetLike σ M] [AddSubmonoidClass σ M]
    {A : ι → σ} (h : DirectSum.IsInternal A) (e : ι ≃ κ) :
    DirectSum.IsInternal fun k ↦ A (e.symm k) := by
  have hcomp : (DirectSum.coeAddMonoidHom A).comp
      (DirectSum.equivCongrLeft (β := fun i ↦ (A i : Type _)) e).symm.toAddMonoidHom =
      DirectSum.coeAddMonoidHom fun k ↦ A (e.symm k) := by
    refine DirectSum.addHom_ext' fun k ↦ AddMonoidHom.ext fun y ↦ ?_
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      DirectSum.coeAddMonoidHom_of]
    rw [← DirectSum.equivCongrLeft_of (β := fun i ↦ (A i : Type _)) e k y,
      AddEquiv.symm_apply_apply, DirectSum.coeAddMonoidHom_of]
  have hbij : Function.Bijective (DirectSum.coeAddMonoidHom fun k ↦ A (e.symm k)) := by
    rw [← hcomp]
    simpa only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom] using
      h.comp (AddEquiv.bijective _)
  exact hbij

variable (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]

/-- An internal integer grading of an `R`-module `M`.

The `isInternal` field says that the canonical map from the external direct sum of the `piece p`
to `M` is bijective.  Thus elements of `M` have unique finite homogeneous decompositions. -/
structure InternalGrading where
  /-- The submodule of elements of degree `p`. -/
  piece : ℤ → Submodule R M
  /-- The homogeneous pieces form an internal direct sum. -/
  isInternal : DirectSum.IsInternal piece

namespace InternalGrading

variable {R M}

/-- Two internal gradings of the same module are equal as soon as their homogeneous pieces
agree. -/
@[ext]
theorem ext : ∀ {G H : InternalGrading R M}, (∀ p, G.piece p = H.piece p) → G = H
  | ⟨_, _⟩, ⟨_, _⟩, h => by
    obtain rfl := funext h
    rfl

/-- The decomposition attached to an internal grading. -/
noncomputable instance (G : InternalGrading R M) : DirectSum.Decomposition G.piece :=
  G.isInternal.chooseDecomposition

end InternalGrading

end TauCeti
