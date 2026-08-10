/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.SimpleModule.Isotypic
public import TauCeti.RepresentationTheory.Induction.Clifford.Basic

/-!
# The constituents of a restriction to a normal subgroup form one orbit

Let `N` be a normal subgroup of `G` and let `ρ` be an irreducible representation of `G` on `V`.
Restricting `ρ` to `N` breaks it into irreducible constituents
(`TauCeti.Representation.isSemisimpleRepresentation_comp_subtype`), and this file identifies which
constituents occur: **they are the translates of any one of them**, up to isomorphism of
`N`-representations.  Equivalently, `G` permutes the isotypic components of the restriction
transitively.

The argument is short because the two halves it needs are already in place.  The translates
`TauCeti.Representation.conjSubrep ρ g σ` of a minimal `N`-stable subspace `σ` are again minimal
(`TauCeti.Representation.isAtom_conjSubrep_iff`) and they span
(`TauCeti.Representation.iSup_conjSubrep_eq_top`); and a simple submodule of a sum of simple
submodules is isomorphic to one of the summands (Mathlib's `Submodule.linearEquiv_of_le_sSup`).
The only work is to move the spanning statement from the lattice of `k`-subspaces, where it is
proved, to the lattice of `k[N]`-submodules of the restriction viewed as a `k[N]`-module, where the
isotypic machinery lives; that is `TauCeti.Representation.iSup_asSubmodule_conjSubrep_eq_top`, and
the transport is the order isomorphism
`Subrepresentation.subrepresentationSubmoduleOrderIso`.

No finiteness and no invertibility of `Nat.card N` is used: irreducibility of the ambient
representation replaces Maschke's theorem throughout, exactly as in
`TauCeti/RepresentationTheory/Induction/Clifford/Basic.lean`.  Finite-dimensionality of `V` is
needed only to know that a minimal `N`-stable subspace exists at all, and enters only in
`TauCeti.Representation.exists_isAtom_forall_nonempty_linearEquiv_conjSubrep`, the packaged form of
the theorem.

## Main statements

* `TauCeti.Representation.iSup_asSubmodule_conjSubrep_eq_top`: the translates of a nonzero
  `N`-subrepresentation of an irreducible representation span, as `k[N]`-submodules.
* `TauCeti.Representation.exists_nonempty_linearEquiv_conjSubrep`: **Clifford's theorem, single
  orbit form.** Any two minimal `N`-stable subspaces of an irreducible representation are
  translates of one another, up to isomorphism of `N`-representations.
* `TauCeti.Representation.exists_isAtom_forall_nonempty_linearEquiv_conjSubrep`: the same statement
  packaged for a finite-dimensional irreducible representation, where the minimal subspace to
  translate is produced rather than assumed.
* `TauCeti.Representation.isotypicComponents_eq_range`: the isotypic components of the restriction
  are exactly the components of the translates, so `G` acts transitively on them; with
  `TauCeti.Representation.finite_isotypicComponents` there are finitely many of them when `G` is
  finite.
* `TauCeti.Representation.isIsotypicOfType_asSubmodule_iff`: the restriction is isotypic exactly
  when every translate of one constituent is isomorphic to it — the case in which the inertia group
  of the constituent is all of `G`.

## Implementation notes

An `N`-constituent is presented as an atom of the lattice of `N`-subrepresentations, as in
`Basic.lean`, and "isomorphic as representations of `N`" is spelled as a `k[N]`-linear equivalence
of the associated submodules of `Representation.asModule (ρ.comp N.subtype)`.  That is what the
isotypic API of `Mathlib/RingTheory/SimpleModule/Isotypic.lean` speaks, and it is the same relation
as an isomorphism of the subrepresentations, transported along
`Subrepresentation.subrepresentationSubmoduleOrderIso`.  Reading the translate through
`TauCeti.Representation.conjSubrepEquiv` turns each statement below into the classical one about
the conjugate representation `{}^g V`.

## References

This file proves the **single-orbit** half of the **Clifford's theorem** milestone of Layer 5 of
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`: "its irreducible
`N`-constituents form a single `G`-orbit".  The rest of that milestone -- that the constituents
occur with a common multiplicity `e`, and the resulting decomposition
`Res_N W ≅ e · ⨁ᵢ {}^{gᵢ} V` indexed by a transversal of the inertia group -- needs the
multiplicity API the roadmap lists as the layer's prerequisite and is not proved here.

The mathematics is the classical argument of C. W. Curtis and I. Reiner, *Representation Theory of
Finite Groups and Associative Algebras*, §49.
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

namespace Representation

section Orbit

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : Representation k G V)

/-- **The translates of a nonzero `N`-subrepresentation of an irreducible representation span, as
`k[N]`-submodules.**  This is `TauCeti.Representation.iSup_conjSubrep_eq_top` read in the lattice of
`k[N]`-submodules of `Representation.asModule (ρ.comp N.subtype)` instead of the lattice of
`k`-subspaces of `V`; the two lattices are exchanged by
`Subrepresentation.subrepresentationSubmoduleOrderIso`. -/
theorem iSup_asSubmodule_conjSubrep_eq_top [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : σ ≠ ⊥) :
    ⨆ g : G, (conjSubrep ρ g σ).asSubmodule = ⊤ := by
  -- pull the supremum back to a subrepresentation, where the spanning statement lives
  set T : Subrepresentation (ρ.comp N.subtype) :=
    Subrepresentation.subrepresentationSubmoduleOrderIso.symm
      (⨆ g : G, (conjSubrep ρ g σ).asSubmodule) with hT
  have hTeq : T.asSubmodule = ⨆ g : G, (conjSubrep ρ g σ).asSubmodule := by
    rw [hT, ← Subrepresentation.subrepresentationSubmoduleOrderIso_apply,
      OrderIso.apply_symm_apply]
  have hle : ∀ g : G, conjSubrep ρ g σ ≤ T := fun g => by
    rw [← Subrepresentation.subrepresentationSubmoduleOrderIso.le_iff_le,
      Subrepresentation.subrepresentationSubmoduleOrderIso_apply,
      Subrepresentation.subrepresentationSubmoduleOrderIso_apply, hTeq]
    exact le_iSup (fun g : G => (conjSubrep ρ g σ).asSubmodule) g
  have htop : T = ⊤ := by
    refine Subrepresentation.toSubmodule_injective (le_antisymm le_top ?_)
    rw [Subrepresentation.toSubmodule_top, ← iSup_conjSubrep_eq_top ρ hσ]
    exact iSup_le fun g => hle g
  rw [← hTeq, htop, ← Subrepresentation.subrepresentationSubmoduleOrderIso_apply,
    OrderIso.map_top]

omit [N.Normal] in
/-- A minimal `N`-stable subspace is a simple `k[N]`-submodule of the restriction.  This is the
dictionary between the two ways of saying "irreducible constituent" used below. -/
theorem isSimpleModule_asSubmodule_of_isAtom {σ : Subrepresentation (ρ.comp N.subtype)}
    (hσ : IsAtom σ) : IsSimpleModule k[N] σ.asSubmodule :=
  isSimpleModule_iff_isAtom.mpr
    ((Subrepresentation.subrepresentationSubmoduleOrderIso.isAtom_iff σ).mpr hσ)

/-- **Every irreducible `N`-constituent is a translate of any fixed one.**  If `σ` is a minimal
`N`-stable subspace of an irreducible representation `ρ` and `T` is any simple `k[N]`-submodule of
the restriction, then `T` is isomorphic, as a representation of `N`, to the translate
`conjSubrep ρ g σ` for some `g : G`.

The translates of `σ` are simple and span, so `T` sits inside a sum of simple modules and is
therefore isomorphic to one of them. -/
theorem exists_nonempty_linearEquiv_asSubmodule_conjSubrep [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ)
    (T : Submodule k[N] (_root_.Representation.asModule (ρ.comp N.subtype)))
    [IsSimpleModule k[N] T] :
    ∃ g : G, Nonempty (T ≃ₗ[k[N]] (conjSubrep ρ g σ).asSubmodule) := by
  have hsimple : ∀ m : (Set.range fun g : G => (conjSubrep ρ g σ).asSubmodule),
      IsSimpleModule k[N] m := by
    rintro ⟨_, g, rfl⟩
    exact isSimpleModule_asSubmodule_of_isAtom ρ (isAtom_conjSubrep_iff.mpr hσ)
  have hsSup : sSup (Set.range fun g : G => (conjSubrep ρ g σ).asSubmodule) = ⊤ := by
    rw [sSup_range]
    exact iSup_asSubmodule_conjSubrep_eq_top ρ hσ.1
  obtain ⟨_, ⟨g, rfl⟩, he⟩ :=
    Submodule.linearEquiv_of_le_sSup T _ (simple := hsimple) (le_top.trans hsSup.ge)
  exact ⟨g, he⟩

/-- **Clifford's theorem, single-orbit form.**  Any two minimal `N`-stable subspaces of an
irreducible representation are translates of one another, up to isomorphism of representations of
`N`: the irreducible constituents of the restriction to `N` form a single `G`-orbit. -/
theorem exists_nonempty_linearEquiv_conjSubrep [ρ.IsIrreducible]
    {σ τ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) (hτ : IsAtom τ) :
    ∃ g : G, Nonempty (τ.asSubmodule ≃ₗ[k[N]] (conjSubrep ρ g σ).asSubmodule) :=
  have := isSimpleModule_asSubmodule_of_isAtom ρ hτ
  exists_nonempty_linearEquiv_asSubmodule_conjSubrep ρ hσ τ.asSubmodule

/-- **Clifford's theorem, single-orbit form, packaged.**  The restriction to `N` of a
finite-dimensional irreducible representation has a minimal `N`-stable subspace, and every minimal
`N`-stable subspace is a translate of it up to isomorphism of representations of `N`. -/
theorem exists_isAtom_forall_nonempty_linearEquiv_conjSubrep [ρ.IsIrreducible]
    [FiniteDimensional k V] :
    ∃ σ : Subrepresentation (ρ.comp N.subtype), IsAtom σ ∧
      ∀ τ : Subrepresentation (ρ.comp N.subtype), IsAtom τ →
        ∃ g : G, Nonempty (τ.asSubmodule ≃ₗ[k[N]] (conjSubrep ρ g σ).asSubmodule) := by
  obtain ⟨σ, hσ⟩ := exists_isAtom_comp_subtype (N := N) ρ
  exact ⟨σ, hσ, fun _ hτ => exists_nonempty_linearEquiv_conjSubrep ρ hσ hτ⟩

/-- **`G` permutes the isotypic components of the restriction transitively.**  The isotypic
components of the restriction to `N` of an irreducible representation are exactly the components of
the translates of one minimal `N`-stable subspace. -/
theorem isotypicComponents_eq_range [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) :
    isotypicComponents k[N] (_root_.Representation.asModule (ρ.comp N.subtype))
      = Set.range fun g : G =>
          isotypicComponent k[N] (_root_.Representation.asModule (ρ.comp N.subtype))
            (conjSubrep ρ g σ).asSubmodule := by
  ext c
  constructor
  · rintro ⟨S, _, rfl⟩
    obtain ⟨g, ⟨e⟩⟩ := exists_nonempty_linearEquiv_asSubmodule_conjSubrep ρ hσ S
    exact ⟨g, e.isotypicComponent_eq.symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨_, isSimpleModule_asSubmodule_of_isAtom ρ (isAtom_conjSubrep_iff.mpr hσ), rfl⟩

/-- **A restriction along a normal subgroup of a finite group has finitely many isotypic
components.**  There is one component for each translate, so at most one for each element of `G`. -/
theorem finite_isotypicComponents [ρ.IsIrreducible] [Finite G]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) :
    (isotypicComponents k[N] (_root_.Representation.asModule (ρ.comp N.subtype))).Finite := by
  rw [isotypicComponents_eq_range ρ hσ]
  exact Set.finite_range _

/-- **The restriction is isotypic exactly when one constituent is fixed by all of `G`.**  The
right-hand side says that the inertia group of `σ` is all of `G`; Clifford's theorem then leaves the
restriction with a single isomorphism class of constituents. -/
theorem isIsotypicOfType_asSubmodule_iff [ρ.IsIrreducible]
    {σ : Subrepresentation (ρ.comp N.subtype)} (hσ : IsAtom σ) :
    IsIsotypicOfType k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) σ.asSubmodule ↔
      ∀ g : G, Nonempty ((conjSubrep ρ g σ).asSubmodule ≃ₗ[k[N]] σ.asSubmodule) := by
  constructor
  · intro h g
    have := isSimpleModule_asSubmodule_of_isAtom (σ := conjSubrep ρ g σ) ρ
      (isAtom_conjSubrep_iff.mpr hσ)
    exact h _
  · intro h m _
    obtain ⟨g, ⟨e⟩⟩ := exists_nonempty_linearEquiv_asSubmodule_conjSubrep ρ hσ m
    exact ⟨e.trans (h g).some⟩

end Orbit

end Representation

end TauCeti
