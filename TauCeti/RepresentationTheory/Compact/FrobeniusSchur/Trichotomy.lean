/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.FrobeniusSchur.InvariantTensors
public import TauCeti.RepresentationTheory.Continuous.Square.Invariants
-- the fundamental theorem of algebra, for the `IsAlgClosed ℂ` instance that
-- `ContRepresentation.finrank_invariants_squares_le_one` needs; used in proofs only
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The Frobenius-Schur reality trichotomy for compact groups

For an irreducible unitary representation `π` of a compact group on a finite-dimensional complex
inner product space, the Frobenius-Schur indicator takes only the three values

`ν₂(π) = 1`, `ν₂(π) = 0`, `ν₂(π) = -1`,

and which value occurs is read off the invariants of the symmetric and of the exterior square. This
is the compact-group form of the finite-group
`TauCeti.Representation.frobeniusSchurIndicator_eq_one_or_eq_zero_or_eq_neg_one`.

Everything analytic is already done.
`ContRepresentation.frobeniusSchurIndicator_eq_sub_finrank_invariants`, in
`TauCeti/RepresentationTheory/Compact/FrobeniusSchur/InvariantTensors.lean`, integrates the
character identity and reads the indicator as the signed count of invariant tensors,

`ν₂(π) = dim (Sym²V)ᴳ - dim (Λ²V)ᴳ`.

What remained was the bound on the two counts, and that is pure linear algebra plus Schur's lemma:
`ContRepresentation.finrank_invariants_squares_le_one`, in
`TauCeti/RepresentationTheory/Continuous/Square/Invariants.lean`, says the two dimensions add up to
at most `1`, because the invariants of the tensor square of an irreducible are at most a line and
the two squares meet in `0`. A difference of two non-negative integers whose sum is at most `1` is
`1`, `0` or `-1`, and each value is pinned by which of the two squares carries the invariant.

The trichotomy is stated here for the indicator and the two invariant counts only. The classical
reading of the three values as the **real**, **complex** and **quaternionic** types is *not*
established here: it is the refinement of the trichotomy into the invariant-form dictionary -- that
`ν₂ = 1` is the existence of a nonzero invariant *symmetric* bilinear form and `ν₂ = -1` that of an
invariant *alternating* one, together with the structure-map reformulation over `ℝ` -- which needs
the identification of the invariants of the two squares with invariant forms, a separate step for
compact groups. The finite-group version of that dictionary is
`TauCeti/RepresentationTheory/CharacterTable/FrobeniusSchur/Trichotomy.lean`.

## Main statements

* `ContRepresentation.frobeniusSchurIndicator_trichotomy`: **the indicator of an irreducible
  unitary representation of a compact group is `1`, `0` or `-1`.**
* `ContRepresentation.frobeniusSchurIndicator_eq_one_iff_finrank_invariants_symmetricSquare`,
  `ContRepresentation.frobeniusSchurIndicator_eq_neg_one_iff_finrank_invariants_exteriorSquare`
  and `ContRepresentation.frobeniusSchurIndicator_eq_zero_iff_finrank_invariants_squares`: which
  of the three values occurs, read off the invariants of the two squares.

## References

This discharges the `frobeniusSchurIndicator_trichotomy` target of Layer 6b of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
the step that its
[`Suggested.lean`](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/Suggested.lean)
pins on top of the indicator. The mathematical development follows Daniel Bump, *Lie Groups*,
second edition, Chapter 2, and T. Bröcker and T. tom Dieck, *Representations of Compact Lie
Groups*, Springer GTM 98 (1985), Chapter II.
-/

public section

open Module TauCeti TauCeti.ContRepresentation

namespace ContRepresentation

section CompactGroup

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

variable (π : ContRepresentation ℂ G V) (hπ : Continuous π)

include hπ

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] hπ in
/-- The two invariant counts of an irreducible unitary representation are `(1, 0)`, `(0, 0)` or
`(0, 1)`: they are non-negative and add up to at most `1`. This is the arithmetic behind every
statement below. -/
private theorem finrank_invariants_squares_cases (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    (finrank ℂ (symmetricSquare π).invariants = 1 ∧ finrank ℂ (exteriorSquare π).invariants = 0) ∨
      (finrank ℂ (symmetricSquare π).invariants = 0 ∧
        finrank ℂ (exteriorSquare π).invariants = 0) ∨
      (finrank ℂ (symmetricSquare π).invariants = 0 ∧
        finrank ℂ (exteriorSquare π).invariants = 1) := by
  have hle := finrank_invariants_squares_le_one hunitary hirr
  omega

/-- **The Frobenius-Schur reality trichotomy for compact groups.** The indicator of an irreducible
unitary representation of a compact group on a finite-dimensional complex inner product space is
`1`, `0` or `-1`.

The indicator is the difference `dim (Sym²V)ᴳ - dim (Λ²V)ᴳ`
(`ContRepresentation.frobeniusSchurIndicator_eq_sub_finrank_invariants`) and those two dimensions
add up to at most `1` (`ContRepresentation.finrank_invariants_squares_le_one`), so the difference
is one of the three values. -/
theorem frobeniusSchurIndicator_trichotomy (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    frobeniusSchurIndicator π hπ = 1 ∨ frobeniusSchurIndicator π hπ = 0 ∨
      frobeniusSchurIndicator π hπ = -1 := by
  rw [frobeniusSchurIndicator_eq_sub_finrank_invariants π hπ]
  rcases finrank_invariants_squares_cases π hunitary hirr with
    ⟨hs, ha⟩ | ⟨hs, ha⟩ | ⟨hs, ha⟩ <;> rw [hs, ha] <;> norm_num

/-- **The indicator is `1` exactly when the symmetric square carries a line of invariants.** -/
theorem frobeniusSchurIndicator_eq_one_iff_finrank_invariants_symmetricSquare
    (hunitary : IsUnitary π) (hirr : Representation.IsIrreducible π.toRepresentation) :
    frobeniusSchurIndicator π hπ = 1 ↔ finrank ℂ (symmetricSquare π).invariants = 1 := by
  rw [frobeniusSchurIndicator_eq_sub_finrank_invariants π hπ]
  rcases finrank_invariants_squares_cases π hunitary hirr with
    ⟨hs, ha⟩ | ⟨hs, ha⟩ | ⟨hs, ha⟩ <;> rw [hs, ha] <;> norm_num

/-- **The indicator is `-1` exactly when the exterior square carries a line of invariants.** -/
theorem frobeniusSchurIndicator_eq_neg_one_iff_finrank_invariants_exteriorSquare
    (hunitary : IsUnitary π) (hirr : Representation.IsIrreducible π.toRepresentation) :
    frobeniusSchurIndicator π hπ = -1 ↔ finrank ℂ (exteriorSquare π).invariants = 1 := by
  rw [frobeniusSchurIndicator_eq_sub_finrank_invariants π hπ]
  rcases finrank_invariants_squares_cases π hunitary hirr with
    ⟨hs, ha⟩ | ⟨hs, ha⟩ | ⟨hs, ha⟩ <;> rw [hs, ha] <;> norm_num

/-- **The indicator is `0` exactly when neither square carries an invariant tensor.** -/
theorem frobeniusSchurIndicator_eq_zero_iff_finrank_invariants_squares (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    frobeniusSchurIndicator π hπ = 0 ↔
      finrank ℂ (symmetricSquare π).invariants = 0 ∧
        finrank ℂ (exteriorSquare π).invariants = 0 := by
  rw [frobeniusSchurIndicator_eq_sub_finrank_invariants π hπ]
  rcases finrank_invariants_squares_cases π hunitary hirr with
    ⟨hs, ha⟩ | ⟨hs, ha⟩ | ⟨hs, ha⟩ <;> rw [hs, ha] <;> norm_num

end CompactGroup

end ContRepresentation
