/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Mathlib.Analysis.Complex.Polynomial.Basic` supplies the `IsAlgClosed ℂ` instance the
-- Frobenius-Schur trichotomy asks for.
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.Trichotomy
public import TauCeti.RepresentationTheory.InvariantForm.SumOfConjugates
public import TauCeti.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.RealForm

/-!
# The Frobenius-Schur indicator of a representation realizable over the reals

This file proves the direction of the Frobenius-Schur orthogonality criterion that goes from a real
form to the indicator: **an irreducible representation with a real form is orthogonal**,
`ν₂(ρ) = 1`.  The real-form vocabulary itself -- `Representation.IsRealForm` and
`Representation.IsRealizableOverReal` -- is in `TauCeti.RepresentationTheory.RealForm` and needs
none of the Frobenius-Schur layer.

The route is the one the trichotomy already asks for, an invariant symmetric form.  A
representation of a finite group on a nontrivial finite-dimensional real space carries a nonzero
invariant symmetric form, obtained by summing the coordinate dot product of a basis over the
conjugates (`Representation.exists_isInvariantForm_isSymm_ne_zero`, in
`TauCeti.RepresentationTheory.InvariantForm.SumOfConjugates`); both hypotheses are free here,
because irreducibility over a finite group makes `V` nontrivial and finite-dimensional and the
real form passes each of them to `W`.  A real form then transports the form to a nonzero
invariant symmetric form on `V`
(`Representation.IsRealForm.exists_isInvariantForm_isSymm_ne_zero`), and
`TauCeti.Representation.frobeniusSchurIndicator_eq_one_of_isSymm` reads off the indicator.
Finiteness of `G` is used twice over: the indicator itself and the trichotomy consumed here are
stated for a finite group, and the summing step needs it again to build the invariant form.  The
real-form vocabulary is the part that needs none of it.

The **converse** -- that an irreducible representation with `ν₂(ρ) = 1` is realizable over `ℝ` --
is not proved here.  It is a strictly stronger statement than the existence of an invariant
symmetric form supplied by
`TauCeti.Representation.frobeniusSchurIndicator_eq_one_iff`: passing from the form to a real
structure needs an invariant Hermitian inner product as well, and the antilinear involution built
from the two of them, whose fixed points are the real form.  That construction is separate work.

## Main results

* `Representation.IsRealForm.frobeniusSchurIndicator_eq_one` and
  `Representation.frobeniusSchurIndicator_eq_one_of_isRealizableOverReal`: **an
  irreducible representation realizable over `ℝ` has Frobenius-Schur indicator `1`.**

## References

This is the "realizable" direction of the milestone `frobeniusSchurIndicatorRep_eq_one_realizable`
pinned in the `Suggested.lean` accompanying Layer 7 of
`TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md`.

* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2.
* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 4.
-/

public section

open Module (finrank)

open TauCeti

namespace Representation

open TauCeti.Representation

section Orthogonal

variable {G : Type*} [Group G] [Fintype G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {W : Type*} [AddCommGroup W] [Module ℝ W]
variable {ρ : Representation ℂ G V} {σ : Representation ℝ G W}

/-- **An irreducible representation with a real form is orthogonal.**  Summing the dot product of a
basis over the conjugates produces a nonzero invariant symmetric form on the real side, and
transporting it along the real form makes the complex representation carry one too, which is
exactly the orthogonal case of the Frobenius-Schur trichotomy.

No finiteness is assumed of the real form: irreducibility over a finite group already makes `V`
finite-dimensional (`Representation.IsIrreducible.finiteDimensional`), which `W` inherits
(`Representation.IsRealForm.finiteDimensional_iff`), and a real form has the same dimension as the
representation it is a form of (`Representation.IsRealForm.finrank_eq`), so `W` is nontrivial
too. -/
theorem IsRealForm.frobeniusSchurIndicator_eq_one [ρ.IsIrreducible] (h : IsRealForm ρ σ) :
    frobeniusSchurIndicator ρ = 1 := by
  have : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional ‹ρ.IsIrreducible›
  have : Nontrivial V := IsIrreducible.nontrivial ‹ρ.IsIrreducible›
  have : FiniteDimensional ℝ W := h.finiteDimensional_iff.mpr inferInstance
  have hrank : finrank ℝ W = finrank ℂ V := h.finrank_eq
  have : Nontrivial W :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (hrank ▸ Module.finrank_pos)
  obtain ⟨B, hB, hsymm, hB0⟩ := σ.exists_isInvariantForm_isSymm_ne_zero
  obtain ⟨C, hC, hCsymm, hC0⟩ := h.exists_isInvariantForm_isSymm_ne_zero hB hsymm hB0
  exact frobeniusSchurIndicator_eq_one_of_isSymm ρ hC hC0 hCsymm

/-- **An irreducible representation realizable over `ℝ` has Frobenius-Schur indicator `1`.**  This
is the "realizable" half of the orthogonality criterion; the converse, that indicator `1` produces
a real form, is not proved here. -/
theorem frobeniusSchurIndicator_eq_one_of_isRealizableOverReal [ρ.IsIrreducible]
    (h : IsRealizableOverReal ρ) : frobeniusSchurIndicator ρ = 1 := by
  obtain ⟨σ, hσ⟩ := isRealizableOverReal_iff.mp h
  exact hσ.frobeniusSchurIndicator_eq_one

end Orthogonal

end Representation
