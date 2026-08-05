/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.SimpleModule.Rank

/-!
# Criteria for irreducibility

This file collects three ways of recognising an irreducible representation from outside, without
inspecting its subrepresentations one by one.

A representation on a one-dimensional vector space is irreducible, whatever the group and however
it acts: a subrepresentation is in particular a subspace, and a line has only the two trivial
subspaces.  Nontriviality, the other half of irreducibility, is the same dimension count.  This is
how the smallest representations of a group are recognised as irreducible without knowing anything
about the group -- the trivial representation, a character, a sign -- and it is the criterion the
one-row and one-column Specht modules are proved irreducible by.

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
  -- the two extreme subrepresentations carry the two extreme subspaces
  have hbot : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl
  have htop : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl
  have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := fun hc =>
    bot_ne_top (α := Submodule k V) (by rw [← hbot, ← htop, hc])
  have : Nontrivial (Subrepresentation ρ) := ⟨⊥, ⊤, hne⟩
  refine ⟨fun σ => (eq_bot_or_eq_top σ.toSubmodule).imp (fun hσ => ?_) fun hσ => ?_⟩
  · exact Subrepresentation.toSubmodule_injective (hσ.trans hbot.symm)
  · exact Subrepresentation.toSubmodule_injective (hσ.trans htop.symm)

/-- The trivial representation of a monoid on the base field is irreducible, being a line. -/
instance isIrreducible_trivial_self : (_root_.Representation.trivial k G k).IsIrreducible :=
  isIrreducible_of_finrank_eq_one _ (Module.finrank_self k)

/-- A subrepresentation that is an **atom** of the lattice of subrepresentations -- nonzero, with
no subrepresentation strictly between it and zero -- carries an irreducible representation.  The
translation is the correspondence between the subrepresentations of `σ.toRepresentation` and the
subrepresentations of `ρ` contained in `σ`, given by pushing forward along the inclusion. -/
theorem isIrreducible_toRepresentation_of_isAtom {ρ : Representation k G V}
    {σ : Subrepresentation ρ} (h : IsAtom σ) : σ.toRepresentation.IsIrreducible := by
  have hbot : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl
  have hσ : σ.toSubmodule ≠ ⊥ := fun hc =>
    h.1 (Subrepresentation.toSubmodule_injective (hc.trans hbot.symm))
  have : Nontrivial σ.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hσ
  -- the two extreme subrepresentations of `σ.toRepresentation` carry the two extreme subspaces
  have hbot' : (⊥ : Subrepresentation σ.toRepresentation).toSubmodule = ⊥ := rfl
  have htop' : (⊤ : Subrepresentation σ.toRepresentation).toSubmodule = ⊤ := rfl
  have hne : (⊥ : Subrepresentation σ.toRepresentation) ≠ ⊤ := fun hc =>
    bot_ne_top (α := Submodule k σ.toSubmodule) (by rw [← hbot', ← htop', hc])
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
      hbot'.symm
  · refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
    have heq : τ' = σ := by
      by_contra hne'
      exact hτ (h.2 _ (lt_of_le_of_ne hle hne'))
    have : τ.toSubmodule.map σ.toSubmodule.subtype =
        (⊤ : Submodule k σ.toSubmodule).map σ.toSubmodule.subtype := by
      rw [Submodule.map_subtype_top]
      exact hmap.symm.trans (congrArg Subrepresentation.toSubmodule heq)
    exact (Submodule.map_injective_of_injective σ.toSubmodule.subtype_injective this).trans
      htop'.symm

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

end Representation

end TauCeti
