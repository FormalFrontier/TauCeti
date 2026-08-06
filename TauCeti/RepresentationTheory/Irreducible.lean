/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.Subrepresentation
public import Mathlib.RingTheory.SimpleModule.Rank

/-!
# Criteria for irreducibility

This file collects three ways of recognising an irreducible representation from outside, without
inspecting its subrepresentations one by one, and the finite-dimensional existence statement that
makes the second of them usable.

A representation on a one-dimensional vector space is irreducible, whatever the group and however
it acts: a subrepresentation is in particular a subspace, and a line has only the two trivial
subspaces.  Nontriviality, the other half of irreducibility, is the same dimension count.  This is
how the smallest representations of a group are recognised as irreducible without knowing anything
about the group -- the trivial representation, a character, a sign.

The second criterion turns a lattice-theoretic statement about a fixed ambient representation into
a statement about a subrepresentation on its own: a subrepresentation that is an **atom** of the
lattice of subrepresentations carries an irreducible representation.  Irreducibility of a
subrepresentation `σ` of `ρ` is a statement about the subrepresentations of `σ.toRepresentation`,
one level down from `ρ`, whereas minimality is a statement inside the lattice attached to `ρ`; the
translation between them is the correspondence sending a subrepresentation of `σ.toRepresentation`
to its image in `ρ` under the inclusion of `σ.toSubmodule`.  In practice the atom form is the one
that gets proved -- one exhibits an invariant subspace of the ambient representation and shows it
has no proper nonzero invariant subspace -- and the irreducibility form is the one that gets used.

At the other extreme, a representation whose algebra map exhausts `End k V` is irreducible, because
a vector space is a simple module over its own endomorphism ring, so a nonzero vector can be carried
to any other.  This is the criterion a matrix block of a semisimple group algebra is recognised as
irreducible by.

## Main results

* `TauCeti.Representation.isIrreducible_of_finrank_eq_one`: a line is irreducible.
* `TauCeti.Representation.isIrreducible_toRepresentation_of_isAtom`: an atom of the lattice of
  subrepresentations carries an irreducible representation.
* `TauCeti.Representation.isIrreducible_of_asAlgebraHom_surjective`: a representation whose
  algebra map exhausts the endomorphisms is irreducible.
* `TauCeti.Representation.exists_isAtom_le`: in finite dimensions every nonzero subrepresentation
  contains an atom, so the atom criterion always has something to apply to.
* `TauCeti.Representation.exists_isIrreducible_subrepresentation`: consequently every nonzero
  finite-dimensional representation contains an irreducible subrepresentation.

## References

* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 4, "the named small irreducibles".
-/

public section

namespace TauCeti

namespace Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- A representation on a one-dimensional vector space is irreducible. -/
theorem isIrreducible_of_finrank_eq_one (ρ : Representation k G V)
    (h : Module.finrank k V = 1) : ρ.IsIrreducible := by
  have hsimple : IsSimpleModule k V := isSimpleModule_iff_finrank_eq_one.mpr h
  have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := fun hc =>
    bot_ne_top (α := Submodule k V) (by
      rw [← Subrepresentation.toSubmodule_bot (ρ := ρ), ← Subrepresentation.toSubmodule_top
        (ρ := ρ), hc])
  have : Nontrivial (Subrepresentation ρ) := ⟨⊥, ⊤, hne⟩
  refine ⟨fun σ => (eq_bot_or_eq_top σ.toSubmodule).imp (fun hσ => ?_) fun hσ => ?_⟩
  · exact Subrepresentation.toSubmodule_injective (hσ.trans Subrepresentation.toSubmodule_bot.symm)
  · exact Subrepresentation.toSubmodule_injective (hσ.trans Subrepresentation.toSubmodule_top.symm)

/-- The trivial representation of a monoid on the base field is irreducible, being a line. -/
instance isIrreducible_trivial_self : (_root_.Representation.trivial k G k).IsIrreducible :=
  isIrreducible_of_finrank_eq_one _ (Module.finrank_self k)

/-- A subrepresentation that is an **atom** of the lattice of subrepresentations -- nonzero, with
no subrepresentation strictly between it and zero -- carries an irreducible representation.  The
translation is the correspondence between the subrepresentations of `σ.toRepresentation` and the
subrepresentations of `ρ` contained in `σ`, given by pushing forward along the inclusion. -/
theorem isIrreducible_toRepresentation_of_isAtom {ρ : Representation k G V}
    {σ : Subrepresentation ρ} (h : IsAtom σ) : σ.toRepresentation.IsIrreducible := by
  have hσ : σ.toSubmodule ≠ ⊥ := fun hc =>
    h.1 (Subrepresentation.toSubmodule_injective (hc.trans Subrepresentation.toSubmodule_bot.symm))
  have : Nontrivial σ.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hσ
  have hne : (⊥ : Subrepresentation σ.toRepresentation) ≠ ⊤ := fun hc =>
    bot_ne_top (α := Submodule k σ.toSubmodule) (by
      rw [← Subrepresentation.toSubmodule_bot (ρ := σ.toRepresentation),
        ← Subrepresentation.toSubmodule_top (ρ := σ.toRepresentation), hc])
  have : Nontrivial (Subrepresentation σ.toRepresentation) := ⟨⊥, ⊤, hne⟩
  refine ⟨fun τ => ?_⟩
  -- push `τ` forward to a subrepresentation of `ρ` contained in `σ`
  let τ' : Subrepresentation ρ :=
    { toSubmodule := τ.toSubmodule.map σ.toSubmodule.subtype
      apply_mem_toSubmodule := by
        rintro g _ ⟨w, hw, rfl⟩
        exact ⟨σ.toRepresentation g w, τ.apply_mem_toSubmodule g hw, rfl⟩ }
  have hmap : τ'.toSubmodule = τ.toSubmodule.map σ.toSubmodule.subtype := rfl
  have hle : τ' ≤ σ := Submodule.map_subtype_le _ _
  rcases eq_or_ne τ' ⊥ with hτ | hτ
  · refine Or.inl (Subrepresentation.toSubmodule_injective ?_)
    have : τ.toSubmodule.map σ.toSubmodule.subtype =
        (⊥ : Submodule k σ.toSubmodule).map σ.toSubmodule.subtype := by
      rw [Submodule.map_bot]
      exact hmap.symm.trans (congrArg Subrepresentation.toSubmodule hτ)
    exact (Submodule.map_injective_of_injective σ.toSubmodule.subtype_injective this).trans
      Subrepresentation.toSubmodule_bot.symm
  · refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
    have heq : τ' = σ := by
      by_contra hne'
      exact hτ (h.2 _ (lt_of_le_of_ne hle hne'))
    have : τ.toSubmodule.map σ.toSubmodule.subtype =
        (⊤ : Submodule k σ.toSubmodule).map σ.toSubmodule.subtype := by
      rw [Submodule.map_subtype_top]
      exact hmap.symm.trans (congrArg Subrepresentation.toSubmodule heq)
    exact (Submodule.map_injective_of_injective σ.toSubmodule.subtype_injective this).trans
      Subrepresentation.toSubmodule_top.symm

/-- **A representation whose algebra map exhausts the endomorphisms is irreducible.** Every nonzero
vector then generates, because a vector space is a simple module over its endomorphism ring. -/
theorem isIrreducible_of_asAlgebraHom_surjective [Nontrivial V] (ρ : Representation k G V)
    (h : Function.Surjective ρ.asAlgebraHom) : ρ.IsIrreducible := by
  rw [_root_.Representation.irreducible_iff_isSimpleModule_asModule,
    isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨ρ.asModuleEquiv.toEquiv.nontrivial, fun x hx y => ?_⟩
  obtain ⟨T, hT⟩ := IsSimpleModule.toSpanSingleton_surjective (Module.End k V)
    (m := ρ.asModuleEquiv x) (by simpa using hx) (ρ.asModuleEquiv y)
  rw [LinearMap.toSpanSingleton_apply, Module.End.smul_def] at hT
  obtain ⟨r, rfl⟩ := h T
  refine ⟨r, ρ.asModuleEquiv.injective ?_⟩
  rw [LinearMap.toSpanSingleton_apply, _root_.Representation.asModuleEquiv_map_smul, hT]

/-! ### Atoms exist in finite dimensions -/

/-- The engine behind `TauCeti.Representation.exists_isAtom_le`: descend from a nonzero
subrepresentation to a smaller nonzero one until the descent stops, which it must, because the
subspace carried by a subrepresentation drops dimension at every step. -/
private theorem exists_isAtom_le_aux [FiniteDimensional k V] {ρ : Representation k G V} :
    ∀ n : ℕ, ∀ σ : Subrepresentation ρ, Module.finrank k σ.toSubmodule ≤ n → σ ≠ ⊥ →
      ∃ τ : Subrepresentation ρ, τ ≤ σ ∧ IsAtom τ := by
  intro n
  induction n with
  | zero =>
    intro σ hle hne
    exact absurd (Subrepresentation.toSubmodule_injective
      ((Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hle)).trans
        Subrepresentation.toSubmodule_bot.symm)) hne
  | succ n ih =>
    intro σ hle hne
    by_cases hatom : IsAtom σ
    · exact ⟨σ, le_rfl, hatom⟩
    · obtain ⟨υ, hυσ, hυ⟩ : ∃ υ : Subrepresentation ρ, υ < σ ∧ υ ≠ ⊥ := by
        by_contra hcon
        push Not at hcon
        exact hatom ⟨hne, fun υ hυ => hcon υ hυ⟩
      have hlt : Module.finrank k υ.toSubmodule < Module.finrank k σ.toSubmodule :=
        Submodule.finrank_lt_finrank_of_lt (Subrepresentation.toSubmodule_lt_toSubmodule.mpr hυσ)
      obtain ⟨τ, hτυ, hτ⟩ := ih υ (by omega) hυ
      exact ⟨τ, hτυ.trans hυσ.le, hτ⟩

/-- **Atoms exist.** In a finite-dimensional representation every nonzero subrepresentation
contains an atom of the lattice of subrepresentations.

Finite-dimensionality is what makes the descent to a minimal nonzero subrepresentation terminate;
it is a hypothesis on the ambient representation, not on the acting monoid, which stays arbitrary.
Combined with `TauCeti.Representation.isIrreducible_toRepresentation_of_isAtom` it exhibits an
irreducible subrepresentation inside any nonzero one. -/
theorem exists_isAtom_le [FiniteDimensional k V] {ρ : Representation k G V}
    {σ : Subrepresentation ρ} (hσ : σ ≠ ⊥) : ∃ τ : Subrepresentation ρ, τ ≤ σ ∧ IsAtom τ :=
  exists_isAtom_le_aux (Module.finrank k σ.toSubmodule) σ le_rfl hσ

/-- **Every nonzero finite-dimensional representation contains an irreducible subrepresentation.**
Finite-dimensionality alone suffices; no semisimplicity is assumed.  This produces a single
irreducible subrepresentation, not a decomposition: a representation that is not semisimple need
not be the sum of its irreducible subrepresentations. -/
theorem exists_isIrreducible_subrepresentation [FiniteDimensional k V] [Nontrivial V]
    (ρ : Representation k G V) :
    ∃ σ : Subrepresentation ρ, σ ≠ ⊥ ∧ σ.toRepresentation.IsIrreducible := by
  have htop : (⊤ : Subrepresentation ρ) ≠ ⊥ := fun hc =>
    top_ne_bot (α := Submodule k V) (by
      rw [← Subrepresentation.toSubmodule_top (ρ := ρ), ← Subrepresentation.toSubmodule_bot
        (ρ := ρ), hc])
  obtain ⟨σ, -, hσ⟩ := exists_isAtom_le htop
  exact ⟨σ, hσ.1, isIrreducible_toRepresentation_of_isAtom hσ⟩

end Representation

end TauCeti
