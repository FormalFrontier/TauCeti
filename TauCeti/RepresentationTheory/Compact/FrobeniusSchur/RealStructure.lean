/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.FrobeniusSchur.InvariantForm
public import TauCeti.RepresentationTheory.InvariantForm.RealStructure

/-!
# Frobenius-Schur indicator `1` is a real structure, for a compact group

`TauCeti/RepresentationTheory/Compact/FrobeniusSchur/InvariantForm.lean` reads the three values of
the Frobenius-Schur indicator of an irreducible unitary representation of a compact group off
invariant bilinear forms, and stops there: an invariant *symmetric* form is strictly weaker than a
real form, and none of its statements mentions a structure map.  This file supplies the missing
step, in the operational shape the reality applications ask for:

`ν₂(π) = 1` iff `π` carries a **structure map** -- a conjugate-linear involution `K` of `V`
commuting with the action, `TauCeti.Representation.IsRealStructure` -- equivalently iff `π` is
**realizable over `ℝ`**, that is, is the complexification of a real representation.

Nothing new has to be integrated over the group.  The unitarity hypothesis the whole
Frobenius-Schur layer already carries *is* a positive definite invariant Hermitian form, namely the
inner product of `V` itself, and against a fixed such form a real structure and a nondegenerate
invariant symmetric form are interchangeable data
(`Representation.exists_isRealStructure_iff`, in
`TauCeti/RepresentationTheory/InvariantForm/RealStructure.lean`).  So the compact-group criterion is
the finite-group one of
`TauCeti/RepresentationTheory/CharacterTable/FrobeniusSchur/Realizability.lean` with the summed
invariant Hermitian form replaced by the inner product a unitary representation comes with; the
Haar integral enters only through the invariant-form criterion this file rewrites.

## Main statements

* `ContRepresentation.frobeniusSchurIndicator_eq_one_iff_exists_isRealStructure`: **the indicator
  is `1` exactly when the representation carries a real structure.**
* `ContRepresentation.frobeniusSchurIndicator_eq_one_iff_isRealizableOverReal`: **the indicator is
  `1` exactly when the representation is realizable over `ℝ`.**

## Implementation notes

The roadmap phrases the criterion with an unbundled structure map, a conjugate-linear
`J : V →ₗ⋆[ℂ] V` with `J (J v) = v` commuting with the action.  That is exactly
`TauCeti.Representation.IsRealStructure`, which
`TauCeti/RepresentationTheory/RealForm.lean` already defines and equips with the passage to a real
form, so the statements below are given in terms of the named predicate rather than its unfolding.

## References

This discharges the `frobeniusSchurIndicator_eq_one_iff_exists_structureMap` target of Layer 6b of
the [compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
whose invariant-form companions are proved in
`TauCeti/RepresentationTheory/Compact/FrobeniusSchur/InvariantForm.lean`.

* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter II, §6.
* Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open scoped ComplexOrder InnerProductSpace

open TauCeti TauCeti.ContRepresentation

namespace ContRepresentation

/-! ### The inner product as an invariant Hermitian form -/

section Inner

variable {G V : Type*} [Monoid G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **The inner product of a unitary representation is invariant.**  This is the whole of the
Hermitian input the real-structure construction needs; unitarity supplies it with no averaging. -/
private theorem isInvariantSesqForm_innerₛₗ {π : ContRepresentation ℂ G V} (hπ : IsUnitary π) :
    Representation.IsInvariantSesqForm π.toRepresentation (innerₛₗ ℂ (E := V)) :=
  Representation.isInvariantSesqForm_iff.mpr fun g x y => hπ.inner_map_map g x y

/-- The inner product is Hermitian. -/
private theorem isSymm_innerₛₗ : (innerₛₗ ℂ (E := V)).IsSymm where
  eq x y := by simpa only [innerₛₗ_apply_apply] using inner_conj_symm (𝕜 := ℂ) y x

/-- The inner product is nonnegative on the diagonal, in the complex order. -/
private theorem isNonneg_innerₛₗ : (innerₛₗ ℂ (E := V)).IsNonneg where
  nonneg x := by
    have h : ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [innerₛₗ_apply_apply, h]
    exact Complex.zero_le_real.mpr (sq_nonneg _)

/-- The inner product is definite off the origin. -/
private theorem innerₛₗ_apply_self_ne_zero {x : V} (hx : x ≠ 0) : innerₛₗ ℂ x x ≠ 0 := by
  simpa only [innerₛₗ_apply_apply] using inner_self_ne_zero.mpr hx

end Inner

/-! ### The criterion -/

section CompactGroup

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

variable (π : ContRepresentation ℂ G V) (hπ : Continuous π)

include hπ

/-- **The indicator is `1` exactly when there is a real structure**: an irreducible unitary
representation of a compact group has Frobenius-Schur indicator `1` exactly when it carries a
conjugate-linear involution of `V` commuting with the action.

The invariant-form criterion supplies a nondegenerate invariant symmetric form, and the inner
product of the unitary representation supplies the positive definite invariant Hermitian form that
turns one datum into the other. -/
theorem frobeniusSchurIndicator_eq_one_iff_exists_isRealStructure (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    frobeniusSchurIndicator π hπ = 1 ↔
      ∃ K : V →ₛₗ[starRingEnd ℂ] V, Representation.IsRealStructure π.toRepresentation K := by
  have := hirr
  rw [frobeniusSchurIndicator_eq_one_iff π hπ hunitary hirr]
  exact (Representation.exists_isRealStructure_iff (isInvariantSesqForm_innerₛₗ hunitary)
    isSymm_innerₛₗ isNonneg_innerₛₗ fun _ hx => innerₛₗ_apply_self_ne_zero hx).symm

/-- **The indicator is `1` exactly when the representation is realizable over `ℝ`**: the
Frobenius-Schur criterion for a compact group in its realizability form, the compact mirror of
`TauCeti.Representation.frobeniusSchurIndicator_eq_one_iff_isRealizableOverReal` for a finite
group.  The real form is the fixed space of the structure map. -/
theorem frobeniusSchurIndicator_eq_one_iff_isRealizableOverReal (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    frobeniusSchurIndicator π hπ = 1 ↔
      Representation.IsRealizableOverReal π.toRepresentation := by
  rw [frobeniusSchurIndicator_eq_one_iff_exists_isRealStructure π hπ hunitary hirr,
    Representation.isRealizableOverReal_iff_exists_isRealStructure]

end CompactGroup

end ContRepresentation
