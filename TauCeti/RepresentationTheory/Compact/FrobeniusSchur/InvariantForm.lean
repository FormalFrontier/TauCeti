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
counts by the classical reading of the three values as the **orthogonal**, **complex** and
**symplectic** (quaternionic) types:

`ν₂(π) = 1` iff `π` carries a nondegenerate invariant **symmetric** bilinear form,
`ν₂(π) = -1` iff it carries a nondegenerate invariant **alternating** one,
`ν₂(π) = 0` iff it carries no nonzero invariant bilinear form at all.

The bridge is the inner-product dictionary of
`TauCeti/RepresentationTheory/Continuous/Square/BilinearForm.lean`: a tensor `t` of `V ⊗[ℂ] V`
becomes the form `⟪t, v ⊗ₜ w⟫`, and that identification carries the symmetric tensors to the
symmetric forms, the antisymmetric tensors to the alternating forms, and — because the
representation is unitary — the invariant tensors to the invariant forms. So the two eigenspaces of
the flip that the trichotomy counts *are* the invariant symmetric and the invariant alternating
forms, and each of the three cases can be stated without mentioning the tensor square.

Two facts about an irreducible representation supply the rest, and both are consumed from
`TauCeti/RepresentationTheory/InvariantForm.lean`: a nonzero invariant form on an irreducible
representation is automatically nondegenerate
(`TauCeti.Representation.IsInvariantForm.nondegenerate`), which is why the statements below ask for
nondegeneracy rather than for nonvanishing; and over an algebraically closed field away from
characteristic two a nonzero invariant form is symmetric or alternating
(`TauCeti.Representation.IsInvariantForm.isSymm_or_isAlt`), which is what makes the vanishing case
`ν₂ = 0` say that there is no invariant form at all.

This is the compact-group mirror of the finite-group
`TauCeti.Representation.frobeniusSchurIndicator_eq_one_iff` and its companions in
`TauCeti/RepresentationTheory/CharacterTable/FrobeniusSchur/Trichotomy.lean`, and the statements are
deliberately given the same shape: invariance is the named predicate
`TauCeti.Representation.IsInvariantForm`, which unfolds to `B (π g v) (π g w) = B v w`, and the
`B ≠ 0` clause is left out because nondegeneracy already implies it
(`TauCeti.Representation.IsInvariantForm.nondegenerate_iff_ne_zero`).

## Main statements

* `ContRepresentation.frobeniusSchurIndicator_eq_one_iff`: **the indicator is `1` exactly in the
  orthogonal case**, that is, exactly when the representation carries a nondegenerate invariant
  symmetric form.
* `ContRepresentation.frobeniusSchurIndicator_eq_neg_one_iff`: **the indicator is `-1` exactly in
  the symplectic case**, that is, exactly when the representation carries a nondegenerate invariant
  alternating form.
* `ContRepresentation.frobeniusSchurIndicator_eq_zero_iff`: **the indicator is `0` exactly in the
  complex case**, that is, exactly when the representation carries no nonzero invariant bilinear
  form.

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

variable (π : ContRepresentation ℂ G V) (hπ : Continuous π)

include hπ

/-- **The indicator is `1` exactly in the orthogonal case**: an irreducible unitary representation
of a compact group has Frobenius-Schur indicator `1` exactly when it carries a nondegenerate
invariant symmetric bilinear form. -/
theorem frobeniusSchurIndicator_eq_one_iff (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    frobeniusSchurIndicator π hπ = 1 ↔
      ∃ B : BilinForm ℂ V, Representation.IsInvariantForm π.toRepresentation B ∧
        B.IsSymm ∧ B.Nondegenerate := by
  have hirr' : Representation.IsIrreducible π.toRepresentation := hirr
  rw [frobeniusSchurIndicator_eq_one_iff_finrank_invariants_symmetricSquare π hπ hunitary hirr]
  constructor
  · intro h
    have hne : (symmetricSquare π).invariants ≠ ⊥ := fun hbot => by
      rw [hbot, finrank_bot] at h
      exact one_ne_zero h.symm
    obtain ⟨B, hB, hB0, hsymm⟩ :=
      (exists_ne_zero_isSymm_isInvariantForm_iff π hunitary).mpr hne
    exact ⟨B, hB, hsymm, hB.nondegenerate hB0⟩
  · rintro ⟨B, hB, hsymm, hnd⟩
    have hne : (symmetricSquare π).invariants ≠ ⊥ :=
      (exists_ne_zero_isSymm_isInvariantForm_iff π hunitary).mp
        ⟨B, hB, hB.nondegenerate_iff_ne_zero.mp hnd, hsymm⟩
    have hle := finrank_invariants_squares_le_one hunitary hirr
    have h1 := Submodule.one_le_finrank_iff.mpr hne
    omega

/-- **The indicator is `-1` exactly in the symplectic case**: an irreducible unitary representation
of a compact group has Frobenius-Schur indicator `-1` exactly when it carries a nondegenerate
invariant alternating bilinear form. -/
theorem frobeniusSchurIndicator_eq_neg_one_iff (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    frobeniusSchurIndicator π hπ = -1 ↔
      ∃ B : BilinForm ℂ V, Representation.IsInvariantForm π.toRepresentation B ∧
        B.IsAlt ∧ B.Nondegenerate := by
  have hirr' : Representation.IsIrreducible π.toRepresentation := hirr
  rw [frobeniusSchurIndicator_eq_neg_one_iff_finrank_invariants_exteriorSquare π hπ hunitary hirr]
  constructor
  · intro h
    have hne : (exteriorSquare π).invariants ≠ ⊥ := fun hbot => by
      rw [hbot, finrank_bot] at h
      exact one_ne_zero h.symm
    obtain ⟨B, hB, hB0, halt⟩ :=
      (exists_ne_zero_isAlt_isInvariantForm_iff π hunitary).mpr hne
    exact ⟨B, hB, halt, hB.nondegenerate hB0⟩
  · rintro ⟨B, hB, halt, hnd⟩
    have hne : (exteriorSquare π).invariants ≠ ⊥ :=
      (exists_ne_zero_isAlt_isInvariantForm_iff π hunitary).mp
        ⟨B, hB, hB.nondegenerate_iff_ne_zero.mp hnd, halt⟩
    have hle := finrank_invariants_squares_le_one hunitary hirr
    have h1 := Submodule.one_le_finrank_iff.mpr hne
    omega

/-- **The indicator is `0` exactly in the complex case**: an irreducible unitary representation of a
compact group has Frobenius-Schur indicator `0` exactly when it carries no nonzero invariant
bilinear form at all.

Over `ℂ` a nonzero invariant form on an irreducible representation is symmetric or alternating
(`TauCeti.Representation.IsInvariantForm.isSymm_or_isAlt`), so the two preceding theorems account
for every invariant form. -/
theorem frobeniusSchurIndicator_eq_zero_iff (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    frobeniusSchurIndicator π hπ = 0 ↔
      Representation.invariantForms π.toRepresentation = ⊥ := by
  have hirr' : Representation.IsIrreducible π.toRepresentation := hirr
  rw [frobeniusSchurIndicator_eq_zero_iff_finrank_invariants_squares π hπ hunitary hirr]
  constructor
  · rintro ⟨hs, ha⟩
    refine le_antisymm (fun B hB => ?_) bot_le
    by_contra hB0
    rw [Submodule.mem_bot] at hB0
    have hBinv : Representation.IsInvariantForm π.toRepresentation B :=
      Representation.mem_invariantForms.mp hB
    rcases hBinv.isSymm_or_isAlt (by norm_num) hB0 with hsymm | halt
    · have hne := (exists_ne_zero_isSymm_isInvariantForm_iff π hunitary).mp ⟨B, hBinv, hB0, hsymm⟩
      have h1 := Submodule.one_le_finrank_iff.mpr hne
      omega
    · have hne := (exists_ne_zero_isAlt_isInvariantForm_iff π hunitary).mp ⟨B, hBinv, hB0, halt⟩
      have h1 := Submodule.one_le_finrank_iff.mpr hne
      omega
  · intro hbot
    have hsym : (symmetricSquare π).invariants = ⊥ := by
      by_contra hne
      obtain ⟨B, hB, hB0, -⟩ := (exists_ne_zero_isSymm_isInvariantForm_iff π hunitary).mpr hne
      exact hB0 (Submodule.mem_bot ℂ |>.mp (hbot ▸ Representation.mem_invariantForms.mpr hB))
    have halt : (exteriorSquare π).invariants = ⊥ := by
      by_contra hne
      obtain ⟨B, hB, hB0, -⟩ := (exists_ne_zero_isAlt_isInvariantForm_iff π hunitary).mpr hne
      exact hB0 (Submodule.mem_bot ℂ |>.mp (hbot ▸ Representation.mem_invariantForms.mpr hB))
    rw [hsym, halt, finrank_bot, finrank_bot]
    exact ⟨rfl, rfl⟩

end CompactGroup

end ContRepresentation
