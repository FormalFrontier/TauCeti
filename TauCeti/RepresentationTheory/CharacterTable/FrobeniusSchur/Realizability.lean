/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.RealForm
public import TauCeti.RepresentationTheory.InvariantForm.RealStructure

/-!
# Frobenius-Schur indicator `1` means realizable over the reals

`TauCeti/RepresentationTheory/CharacterTable/FrobeniusSchur/RealForm.lean` proves that an
irreducible complex representation with a real form has Frobenius-Schur indicator `1`.  This file
proves the converse, completing the orthogonality criterion: **an irreducible representation of a
finite group with `ν₂(ρ) = 1` is realizable over `ℝ`**.

The indicator only supplies a nondegenerate invariant *symmetric bilinear* form `B`
(`TauCeti.Representation.frobeniusSchurIndicator_eq_one_iff`), and that is strictly weaker than a
real form.  The missing ingredient is a positive definite invariant *Hermitian* form `H`
(`Representation.exists_isInvariantSesqForm_isPosSemidef_apply_self_ne_zero`), which is where
finiteness of the group is used; comparing the two forms then produces a real structure
(`Representation.exists_isRealStructure_of_isInvariantForm_of_isInvariantSesqForm`, in
`TauCeti/RepresentationTheory/InvariantForm/RealStructure.lean`), whose real points are a real
form.  All that is left here is to assemble the three steps, and to record the criterion in its
`↔` form.

## Main results

* `Representation.isRealizableOverReal_of_frobeniusSchurIndicator_eq_one`: **an irreducible
  representation of a finite group with Frobenius-Schur indicator `1` is realizable over `ℝ`.**
* `Representation.frobeniusSchurIndicator_eq_one_iff_isRealizableOverReal`: the two directions
  assembled, the orthogonality criterion in its realizability form.

## References

This is the milestone `frobeniusSchurIndicatorRep_eq_one_realizable` of Layer 7 of
`TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md`, whose other direction is in
`TauCeti/RepresentationTheory/CharacterTable/FrobeniusSchur/RealForm.lean`.

* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2, Theorem 31.
* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Theorems 4.14 and 4.19; the invariant
  Hermitian form the construction is fed with is Theorem 4.17.
-/

public section

open scoped ComplexOrder

open TauCeti

namespace Representation

open TauCeti.Representation

/-! ### The Frobenius-Schur criterion -/

section Criterion

variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V} [ρ.IsIrreducible]

/-- **An irreducible representation of a finite group with Frobenius-Schur indicator `1` is
realizable over `ℝ`.**  The indicator supplies a nondegenerate invariant symmetric form, finiteness
of the group supplies a positive definite invariant Hermitian form, and comparing the two produces
a real structure, whose real points are a real form. -/
theorem isRealizableOverReal_of_frobeniusSchurIndicator_eq_one
    (h : frobeniusSchurIndicator ρ = 1) : IsRealizableOverReal ρ := by
  have : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional ‹ρ.IsIrreducible›
  obtain ⟨B, hBinv, hBsymm, hBnd⟩ := (frobeniusSchurIndicator_eq_one_iff ρ).mp h
  obtain ⟨H, hHinv, hHpos, hdef⟩ :=
    exists_isInvariantSesqForm_isPosSemidef_apply_self_ne_zero ρ
  obtain ⟨K, hK⟩ := exists_isRealStructure_of_isInvariantForm_of_isInvariantSesqForm hBinv
    hBsymm hBnd hHinv hHpos.isNonneg hdef
  exact isRealizableOverReal_iff_exists_isRealStructure.mpr ⟨K, hK⟩

/-- **The orthogonality criterion in its realizability form**: an irreducible complex
representation of a finite group has Frobenius-Schur indicator `1` exactly when it is realizable
over `ℝ`.  The two halves are genuinely different theorems: one direction only transports an
invariant symmetric form along a real form, while the other has to *build* the real structure out
of an invariant symmetric form and an invariant Hermitian one. -/
theorem frobeniusSchurIndicator_eq_one_iff_isRealizableOverReal :
    frobeniusSchurIndicator ρ = 1 ↔ IsRealizableOverReal ρ :=
  ⟨isRealizableOverReal_of_frobeniusSchurIndicator_eq_one,
    frobeniusSchurIndicator_eq_one_of_isRealizableOverReal⟩

end Criterion

end Representation
