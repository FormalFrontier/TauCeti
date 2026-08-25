/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.FrobeniusSchur.Trichotomy
public import TauCeti.RepresentationTheory.Continuous.Square.BilinearForm
-- the fundamental theorem of algebra, for the `IsAlgClosed ℂ` instance that the invariant-form
-- dichotomy needs; used in proofs only
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The Frobenius-Schur trichotomy of a compact group, read off invariant forms

`ContRepresentation.frobeniusSchurIndicator_trichotomy` says that the indicator of an irreducible
unitary representation of a compact group is `1`, `0` or `-1`, and pins which value occurs by the
invariants of the symmetric and of the exterior square. This file replaces those two invariant
counts by invariant **bilinear forms**:

`ν₂(π) = 1` iff `π` carries a nondegenerate invariant **symmetric** bilinear form,
`ν₂(π) = -1` iff it carries a nondegenerate invariant **alternating** one,
`ν₂(π) = 0` iff it carries no nonzero invariant bilinear form at all.

That is as far as this file goes: the classical reading of the three values as the real, complex
and quaternionic types — that `π` is the complexification of a real representation, that it is not
isomorphic to its conjugate, that it carries a quaternionic structure — is a further step, not
proved here, since none of the statements below mentions a structure map or a real or quaternionic
form.

The bridge is the inner-product dictionary of
`TauCeti/RepresentationTheory/Continuous/Square/BilinearForm.lean`: a tensor `t` of `V ⊗[ℂ] V`
becomes the form `⟪t, v ⊗ₜ w⟫`, and that construction carries the symmetric tensors to the
symmetric forms, the antisymmetric tensors to the alternating forms, and — because the
representation is unitary — the invariant tensors to the invariant forms. So the two eigenspaces of
the flip that the trichotomy counts *are* the invariant symmetric and the invariant alternating
forms, and each of the three cases can be stated without mentioning the tensor square.

Two facts about an irreducible representation supply the rest, and both are consumed from
`TauCeti/RepresentationTheory/InvariantForm.lean`: a nonzero invariant form on an irreducible
representation is automatically nondegenerate
(`TauCeti.Representation.IsInvariantForm.nondegenerate`), which is why the statements below ask for
nondegeneracy rather than for nonvanishing; and over an algebraically closed field away from
characteristic two it carries a nonzero invariant symmetric form, a nonzero invariant alternating
one, or no nonzero invariant form at all
(`TauCeti.Representation.exists_isSymm_or_exists_isAlt_or_invariantForms_eq_bot`), which is what
makes the vanishing case `ν₂ = 0` say that there is no invariant form at all.

This is the compact-group mirror of the finite-group
`TauCeti.Representation.frobeniusSchurIndicator_eq_one_iff` and its companions in
`TauCeti/RepresentationTheory/CharacterTable/FrobeniusSchur/Trichotomy.lean`, and the statements are
deliberately given the same shape: invariance is the named predicate
`TauCeti.Representation.IsInvariantForm`, which unfolds to `B (π g v) (π g w) = B v w`, and the
`B ≠ 0` clause is left out because nondegeneracy already implies it
(`TauCeti.Representation.IsInvariantForm.nondegenerate_iff_ne_zero`).

## Main statements

* `ContRepresentation.frobeniusSchurIndicator_eq_one_iff`: **the indicator is `1` exactly when the
  representation carries a nondegenerate invariant symmetric form.**
* `ContRepresentation.frobeniusSchurIndicator_eq_neg_one_iff`: **the indicator is `-1` exactly when
  it carries a nondegenerate invariant alternating form.**
* `ContRepresentation.frobeniusSchurIndicator_eq_zero_iff`: **the indicator is `0` exactly when it
  carries no nonzero invariant bilinear form.**

## Implementation notes

The first two theorems are one argument read twice, so both go through the private
`ContRepresentation.finrank_eq_one_iff_exists_nondegenerate`: a count of invariants that is at most
`1` is `1` exactly when a nonzero invariant form of the relevant kind exists, and on an irreducible
representation "nonzero" and "nondegenerate" agree. The third then needs no count of its own: the
trichotomy leaves only the values `1` and `-1` to exclude, and those are exactly what the first two
theorems name.

## References

This discharges the `frobeniusSchurIndicator_eq_one_iff` and
`frobeniusSchurIndicator_eq_neg_one_iff` targets of Layer 6b of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
the invariant-form dictionary its
[`Suggested.lean`](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/Suggested.lean)
pins on top of the trichotomy. The mathematical development follows Daniel Bump, *Lie Groups*,
second edition, Chapter 2, and T. Bröcker and T. tom Dieck, *Representations of Compact Lie
Groups*, Springer GTM 98 (1985), Chapter II.
-/

public section

open LinearMap (BilinForm)

open Module TauCeti TauCeti.ContRepresentation

namespace ContRepresentation

section CompactGroup

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

variable (π : ContRepresentation ℂ G V)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] [FiniteDimensional ℂ V] in
/-- A count of invariants that is at most `1` is `1` exactly when there is a nonzero invariant form
of the kind the count records; on an irreducible representation such a form is the same thing as a
nondegenerate one. This is the shape both the symmetric and the alternating case take. -/
private theorem finrank_eq_one_iff_exists_nondegenerate {M : Type*} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] {S : Submodule ℂ M} {P : BilinForm ℂ V → Prop}
    (hirr : Representation.IsIrreducible π.toRepresentation) (hle : finrank ℂ S ≤ 1)
    (hiff : (∃ B : BilinForm ℂ V, Representation.IsInvariantForm π.toRepresentation B ∧ P B ∧
        B ≠ 0) ↔ S ≠ ⊥) :
    finrank ℂ S = 1 ↔ ∃ B : BilinForm ℂ V,
      Representation.IsInvariantForm π.toRepresentation B ∧ P B ∧ B.Nondegenerate := by
  constructor
  · intro h
    have hne : S ≠ ⊥ := fun hbot => by
      rw [hbot, finrank_bot] at h
      exact one_ne_zero h.symm
    obtain ⟨B, hB, hPB, hB0⟩ := hiff.mpr hne
    exact ⟨B, hB, hPB, hB.nondegenerate hB0⟩
  · rintro ⟨B, hB, hPB, hnd⟩
    have hne : S ≠ ⊥ := hiff.mp ⟨B, hB, hPB, hB.nondegenerate_iff_ne_zero.mp hnd⟩
    have h1 := Submodule.one_le_finrank_iff.mpr hne
    omega

variable (hπ : Continuous π)

include hπ

/-- **The indicator is `1` exactly when there is an invariant symmetric form**: an irreducible
unitary representation of a compact group has Frobenius-Schur indicator `1` exactly when it carries
a nondegenerate invariant symmetric bilinear form. -/
theorem frobeniusSchurIndicator_eq_one_iff (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    frobeniusSchurIndicator π hπ = 1 ↔
      ∃ B : BilinForm ℂ V, Representation.IsInvariantForm π.toRepresentation B ∧
        B.IsSymm ∧ B.Nondegenerate := by
  rw [frobeniusSchurIndicator_eq_one_iff_finrank_invariants_symmetricSquare π hπ hunitary hirr]
  exact finrank_eq_one_iff_exists_nondegenerate π hirr
    ((Nat.le_add_right _ _).trans (finrank_invariants_squares_le_one hunitary hirr))
    (exists_isInvariantForm_isSymm_ne_zero_iff π hunitary)

/-- **The indicator is `-1` exactly when there is an invariant alternating form**: an irreducible
unitary representation of a compact group has Frobenius-Schur indicator `-1` exactly when it
carries a nondegenerate invariant alternating bilinear form. -/
theorem frobeniusSchurIndicator_eq_neg_one_iff (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    frobeniusSchurIndicator π hπ = -1 ↔
      ∃ B : BilinForm ℂ V, Representation.IsInvariantForm π.toRepresentation B ∧
        B.IsAlt ∧ B.Nondegenerate := by
  rw [frobeniusSchurIndicator_eq_neg_one_iff_finrank_invariants_exteriorSquare π hπ hunitary hirr]
  exact finrank_eq_one_iff_exists_nondegenerate π hirr
    ((Nat.le_add_left _ _).trans (finrank_invariants_squares_le_one hunitary hirr))
    (exists_isInvariantForm_isAlt_ne_zero_iff π hunitary)

/-- **The indicator is `0` exactly when there is no invariant form**: an irreducible unitary
representation of a compact group has Frobenius-Schur indicator `0` exactly when it carries no
nonzero invariant bilinear form at all.

Over `ℂ` an irreducible representation carries a nonzero invariant symmetric form, a nonzero
invariant alternating one, or no nonzero invariant form at all
(`TauCeti.Representation.exists_isSymm_or_exists_isAlt_or_invariantForms_eq_bot`), so the two
preceding theorems account for every invariant form, and the trichotomy leaves nothing else for the
indicator to be. -/
theorem frobeniusSchurIndicator_eq_zero_iff (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    frobeniusSchurIndicator π hπ = 0 ↔
      Representation.invariantForms π.toRepresentation = ⊥ := by
  constructor
  · intro h0
    rcases Representation.exists_isSymm_or_exists_isAlt_or_invariantForms_eq_bot
      π.toRepresentation (by norm_num) with
      ⟨B, hB, hB0, hsymm⟩ | ⟨B, hB, hB0, halt⟩ | hbot
    · have h1 := (frobeniusSchurIndicator_eq_one_iff π hπ hunitary hirr).mpr
        ⟨B, hB, hsymm, hB.nondegenerate hB0⟩
      rw [h0] at h1
      norm_num at h1
    · have h1 := (frobeniusSchurIndicator_eq_neg_one_iff π hπ hunitary hirr).mpr
        ⟨B, hB, halt, hB.nondegenerate hB0⟩
      rw [h0] at h1
      norm_num at h1
    · exact hbot
  · intro hbot
    -- No invariant form is nondegenerate, so neither `1` nor `-1` is left by the trichotomy.
    have hnone : ∀ B : BilinForm ℂ V, Representation.IsInvariantForm π.toRepresentation B →
        B.Nondegenerate → False := fun B hB hnd =>
      hB.nondegenerate_iff_ne_zero.mp hnd
        (Submodule.mem_bot ℂ |>.mp (hbot ▸ Representation.mem_invariantForms.mpr hB))
    rcases frobeniusSchurIndicator_trichotomy π hπ hunitary hirr with h | h | h
    · obtain ⟨B, hB, -, hnd⟩ := (frobeniusSchurIndicator_eq_one_iff π hπ hunitary hirr).mp h
      exact (hnone B hB hnd).elim
    · exact h
    · obtain ⟨B, hB, -, hnd⟩ := (frobeniusSchurIndicator_eq_neg_one_iff π hπ hunitary hirr).mp h
      exact (hnone B hB hnd).elim

end CompactGroup

end ContRepresentation
