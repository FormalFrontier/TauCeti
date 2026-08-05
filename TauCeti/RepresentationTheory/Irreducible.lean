/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.SimpleModule.Rank

/-!
# Criteria for irreducibility

Two criteria recognise a representation as irreducible from outside, without inspecting its
subrepresentations one by one.

A representation on a one-dimensional vector space is irreducible, whatever the group and however
it acts: a subrepresentation is in particular a subspace, and a line has only the two trivial
subspaces.  Nontriviality, the other half of irreducibility, is the same dimension count.

This is how the smallest representations of a group are recognised as irreducible without knowing
anything about the group -- the trivial representation, a character, a sign -- and it is the
criterion the one-row and one-column Specht modules are proved irreducible by.

At the other extreme, a representation whose algebra map exhausts `End k V` is irreducible, because
a vector space is a simple module over its own endomorphism ring, so a nonzero vector can be carried
to any other.  This is the criterion a matrix block of a semisimple group algebra is recognised as
irreducible by.

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
