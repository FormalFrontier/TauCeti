/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Basic
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Construction

/-!
# The solvable radical and semisimplicity

This file connects the solvable-radical construction to the definition of a semisimple
finite-type affine group. Semisimplicity is equivalent to smoothness, geometric connectedness,
and triviality of the solvable radical after base change to an algebraic closure.

## Main declaration

* `semisimpleCommHopfAlgProperty_iff_solvableRadicalDefiningIdeal_baseChange_eq_augmentation`:
  semisimplicity is equivalent to smoothness, geometric connectedness, and triviality of the
  geometric solvable radical.

## References

* J. S. Milne, *Algebraic Groups* (2017), Sections 6.45--6.46 and 21.10.
* A. Borel, *Linear Algebraic Groups*, Section 11.21.

The equivalence follows the formal pattern of
`TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive`, applied to the existing universal
definition of semisimplicity.

This completes the connection between the solvable radical and semisimplicity in Layer 6,
"Reductive and semisimple groups", of the ReductiveGroups roadmap.
-/

public section

namespace TauCeti

universe u

noncomputable section

/-- A finite-type affine group is semisimple exactly when it is smooth and geometrically
connected and its geometric solvable radical is trivial. -/
theorem semisimpleCommHopfAlgProperty_iff_solvableRadicalDefiningIdeal_baseChange_eq_augmentation
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    semisimpleCommHopfAlgProperty k H ↔
      Algebra.Smooth k H ∧
        geometricallyConnectedCommHopfAlgProperty k H.obj ∧
          FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal
              (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) =
            HopfIdeal.augmentation (AlgebraicClosure k)
              (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) := by
  rw [semisimpleCommHopfAlgProperty_iff]
  constructor
  · rintro ⟨hsmooth, hconnected, htrivial⟩
    refine ⟨hsmooth, hconnected, ?_⟩
    rw [FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal_eq_augmentation_iff]
    intro I hI
    exact htrivial I hI.isNormal hI.geometricallyConnected hI.smooth hI.geometricallySolvable
  · rintro ⟨hsmooth, hconnected, hradical⟩
    refine ⟨hsmooth, hconnected, ?_⟩
    intro I hnormal hIconnected hIsmooth hIsolvable
    exact (FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal_eq_augmentation_iff
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)).mp hradical I
        (HopfIdeal.IsSolvableRadicalCandidate.mk hnormal hIconnected hIsmooth hIsolvable)

end

end TauCeti
