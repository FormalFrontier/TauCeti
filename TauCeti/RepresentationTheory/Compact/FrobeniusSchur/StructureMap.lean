/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.FrobeniusSchur.InvariantForm
public import TauCeti.RepresentationTheory.InvariantForm.StructureMap

/-!
# The Frobenius-Schur indicator as a structure map, for a compact group

`TauCeti/RepresentationTheory/Compact/FrobeniusSchur/InvariantForm.lean` reads the three values of
the Frobenius-Schur indicator of an irreducible unitary representation of a compact group off
invariant bilinear forms, and stops there: an invariant *symmetric* form is strictly weaker than a
real form, an invariant *alternating* one than a quaternionic structure, and none of its statements
mentions a structure map.  This file supplies the missing step, in the operational shape the
reality applications ask for:

`ν₂(π) = 1` iff `π` carries a **real structure** -- a conjugate-linear involution `K` of `V`
commuting with the action, `Representation.IsRealStructure` -- equivalently iff `π` is
**realizable over `ℝ`**, that is, is the complexification of a real representation; and
`ν₂(π) = -1` iff `π` carries a **quaternionic structure**, a conjugate-linear `J` with
`J (J v) = -v` commuting with the action,
`Representation.IsQuaternionicStructure`.

Nothing new has to be integrated over the group.  The unitarity hypothesis the whole
Frobenius-Schur layer already carries *is* a positive definite invariant Hermitian form, namely the
inner product of `V` itself, and against a fixed such form a structure map exists exactly when a
nondegenerate invariant bilinear form of the matching kind does
(`Representation.exists_isRealStructure_iff` and
`Representation.exists_isQuaternionicStructure_iff`, in
`TauCeti/RepresentationTheory/InvariantForm/StructureMap.lean`).  So the compact-group criterion is
the finite-group one of
`TauCeti/RepresentationTheory/CharacterTable/FrobeniusSchur/Realizability.lean` with the summed
invariant Hermitian form replaced by the inner product a unitary representation comes with; the
Haar integral enters only through the invariant-form criteria this file rewrites.

## Main statements

* `ContRepresentation.frobeniusSchurIndicator_eq_one_iff_exists_structureMap`: **the indicator
  is `1` exactly when the representation carries a conjugate-linear involution commuting with the
  action**, that is, a real structure.
* `ContRepresentation.frobeniusSchurIndicator_eq_one_iff_isRealizableOverReal`: **the indicator is
  `1` exactly when the representation is realizable over `ℝ`.**
* `ContRepresentation.frobeniusSchurIndicator_eq_neg_one_iff_exists_isQuaternionicStructure`: **the
  indicator is `-1` exactly when the representation carries a quaternionic structure.**

## Implementation notes

A structure map is an unbundled conjugate-linear `J : V →ₗ⋆[ℂ] V` with `J (J v) = v`, respectively
`J (J v) = -v`, commuting with the action.  The `1` criterion spells those two conditions out, the
shape in which the reality applications consume it; the `-1` one names them, as
`Representation.IsQuaternionicStructure` of
`TauCeti/RepresentationTheory/QuaternionicStructure.lean`.  The two readings are interchangeable:
the conditions are exactly the fields of that predicate, and of
`Representation.IsRealStructure` -- which `TauCeti/RepresentationTheory/RealForm.lean` defines and
equips with the passage to a real form -- so a witness of either statement is a witness of the
other by `⟨_, _⟩`.

## References

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

/-- **The indicator is `1` exactly when there is a structure map**: an irreducible unitary
representation of a compact group has Frobenius-Schur indicator `1` exactly when it carries a
conjugate-linear `K` of `V` with `K (K v) = v` commuting with the action.

The two conditions are spelled out rather than named because they are the two fields of
`Representation.IsRealStructure`, so `⟨_, _⟩` passes between this statement and that predicate.

The invariant-form criterion supplies a nondegenerate invariant symmetric form, and the inner
product of the unitary representation supplies the positive definite invariant Hermitian form
against which the existence of one is equivalent to the existence of the other. -/
theorem frobeniusSchurIndicator_eq_one_iff_exists_structureMap (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    frobeniusSchurIndicator π hπ = 1 ↔
      ∃ K : V →ₛₗ[starRingEnd ℂ] V, (∀ v : V, K (K v) = v) ∧
        ∀ (g : G) (v : V), K (π g v) = π g (K v) := by
  have := hirr
  rw [frobeniusSchurIndicator_eq_one_iff π hπ hunitary hirr]
  refine ((Representation.exists_isRealStructure_iff (isInvariantSesqForm_innerₛₗ hunitary)
    isSymm_innerₛₗ isNonneg_innerₛₗ fun _ hx => innerₛₗ_apply_self_ne_zero hx).symm).trans ?_
  exact exists_congr fun _ => ⟨fun h => ⟨h.involutive, h.isIntertwining⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **The indicator is `1` exactly when the representation is realizable over `ℝ`**: the
Frobenius-Schur criterion for a compact group in its realizability form, the compact mirror of
`Representation.frobeniusSchurIndicator_eq_one_iff_isRealizableOverReal` for a finite group.  The
real form is the fixed space of the structure map. -/
theorem frobeniusSchurIndicator_eq_one_iff_isRealizableOverReal (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    frobeniusSchurIndicator π hπ = 1 ↔
      Representation.IsRealizableOverReal π.toRepresentation := by
  rw [frobeniusSchurIndicator_eq_one_iff_exists_structureMap π hπ hunitary hirr,
    Representation.isRealizableOverReal_iff_exists_isRealStructure]
  exact exists_congr fun _ => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.involutive, h.isIntertwining⟩⟩

/-- **The indicator is `-1` exactly when there is a quaternionic structure**: an irreducible
unitary representation of a compact group has Frobenius-Schur indicator `-1` exactly when it
carries a conjugate-linear `J` with `J (J v) = -v` commuting with the action.

The invariant-form criterion supplies a nondegenerate invariant alternating form, and the inner
product of the unitary representation supplies the positive definite invariant Hermitian form
against which the existence of one is equivalent to the existence of the other.  A quaternionic
structure is the standard quaternionic
realizability datum -- `J` together with the complex scalars makes `V` a module over the
quaternions -- but, unlike the real case, it supports no realizability-over-`ℝ` reading: it has no
nonzero fixed vector, so it cuts out no real form, and this file draws no such conclusion. -/
theorem frobeniusSchurIndicator_eq_neg_one_iff_exists_isQuaternionicStructure
    (hunitary : IsUnitary π) (hirr : Representation.IsIrreducible π.toRepresentation) :
    frobeniusSchurIndicator π hπ = -1 ↔
      ∃ J : V →ₛₗ[starRingEnd ℂ] V,
        Representation.IsQuaternionicStructure π.toRepresentation J := by
  have := hirr
  rw [frobeniusSchurIndicator_eq_neg_one_iff π hπ hunitary hirr]
  exact (Representation.exists_isQuaternionicStructure_iff (isInvariantSesqForm_innerₛₗ hunitary)
    isSymm_innerₛₗ isNonneg_innerₛₗ fun _ hx => innerₛₗ_apply_self_ne_zero hx).symm

end CompactGroup

end ContRepresentation
