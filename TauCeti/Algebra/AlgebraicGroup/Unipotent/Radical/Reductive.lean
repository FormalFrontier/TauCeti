/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction

/-!
# The unipotent radical and reductivity

This file connects the construction of the geometric unipotent radical to the definition of a
reductive finite-type affine group. It records that reductivity is equivalent to smoothness,
geometric connectedness, and triviality of the unipotent radical after base change to an
algebraic closure.

## Main declarations

* `reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_baseChange_eq_augmentation`:
  reductivity is equivalent to smoothness, geometric connectedness, and triviality of the
  geometric unipotent radical.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§6.45--6.46.
* A. Borel, *Linear Algebraic Groups*, §11.21.

This connects Layer 5, "The unipotent radical", to the definition of reductivity in Layer 6 of
the ReductiveGroups roadmap.
-/

public section

namespace TauCeti

universe u

noncomputable section

/-- A finite-type affine group is reductive exactly when it is smooth and geometrically
connected and its geometric unipotent radical is trivial. -/
theorem reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_baseChange_eq_augmentation
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    reductiveCommHopfAlgProperty k H ↔
      Algebra.Smooth k H ∧
        geometricallyConnectedCommHopfAlgProperty k H.obj ∧
          FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
              (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) =
            HopfIdeal.augmentation (AlgebraicClosure k)
              (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) := by
  rw [reductiveCommHopfAlgProperty_iff]
  constructor
  · rintro ⟨hsmooth, hconnected, htrivial⟩
    refine ⟨hsmooth, hconnected, ?_⟩
    rw [FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_eq_augmentation_iff]
    intro I hI
    exact htrivial I hI.isNormal hI.geometricallyConnected hI.smoothUnipotent
  · rintro ⟨hsmooth, hconnected, hradical⟩
    refine ⟨hsmooth, hconnected, ?_⟩
    intro I hnormal hIconnected hIunipotent
    exact (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_eq_augmentation_iff
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)).mp hradical I
        (HopfIdeal.IsUnipotentRadicalCandidate.mk hnormal hIconnected hIunipotent)

end

end TauCeti
