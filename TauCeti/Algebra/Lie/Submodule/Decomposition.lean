/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
-- Non-public: `TauCeti.isIrreducible_iff_isAtom` appears only inside the proof.
import TauCeti.Algebra.Lie.Submodule.Atom

public section

/-!
# Complements make a finite-dimensional Lie module a direct sum of irreducibles

Complete reducibility is usually proved in its *complement* form: every Lie submodule of a
finite-dimensional module has a complement. This file turns that form into the *decomposition*
form: the module is the internal direct sum of finitely many irreducible Lie submodules.

The passage is lattice-theoretic and runs entirely in `LieSubmodule K L M`, which Mathlib already
knows to be a complete, modular, compactly generated lattice, well-founded for `>` once `M` is
Noetherian. Complements make it a `ComplementedLattice`, hence atomistic
(`isAtomistic_of_complementedLattice`), hence the supremum of an independent set of atoms
(`exists_sSupIndep_of_sSup_atoms_eq_top`), which well-foundedness makes finite
(`WellFoundedGT.finite_of_sSupIndep`). `TauCeti.isIrreducible_iff_isAtom` reads the atoms as the
irreducible submodules, and `LieSubmodule.iSupIndep_toSubmodule` transports the independence to the
underlying submodules, where `DirectSum.IsInternal` lives.

The decomposition is indexed by `Fin k` rather than by the set of atoms: a `Fin k` index carries
`DecidableEq`, which `DirectSum.IsInternal` needs, and it is what a dimension count sums over.

## Main results

* `TauCeti.exists_isInternal_isIrreducible`: **complete reducibility as a decomposition.** A
  finite-dimensional Lie module whose submodule lattice is complemented is the internal direct sum
  of finitely many irreducible Lie submodules.

## Roadmap

This is the shared tail of the two complete-reducibility theorems of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`: the `sl₂` case of Layer 0
(`TauCeti/Algebra/Lie/Sl2/Decomposition.lean`) and Weyl's theorem of Layer 5
(`TauCeti/Algebra/Lie/HighestWeight/CompleteReducibility.lean`), both of which ask for the module
to be exhibited as a direct sum of irreducibles.
-/

namespace TauCeti

open LieModule Module

variable (K : Type*) [Field K] (L : Type*) [LieRing L]
variable (M : Type*) [AddCommGroup M] [Module K M] [LieRingModule L M]

/-- **Complete reducibility as a decomposition.** A finite-dimensional Lie module whose lattice of
Lie submodules is complemented is the internal direct sum of a finite family of irreducible Lie
submodules. -/
theorem exists_isInternal_isIrreducible [FiniteDimensional K M]
    [ComplementedLattice (LieSubmodule K L M)] :
    ∃ (k : ℕ) (N : Fin k → LieSubmodule K L M),
      DirectSum.IsInternal (fun i ↦ (N i).toSubmodule) ∧
        ∀ i, LieModule.IsIrreducible K L (N i) := by
  obtain ⟨S, hindep, hSsup, hSatom⟩ :=
    exists_sSupIndep_of_sSup_atoms_eq_top (α := LieSubmodule K L M) sSup_atoms_eq_top
  have : Fintype S := (WellFoundedGT.finite_of_sSupIndep hindep).fintype
  refine ⟨Fintype.card S, fun i ↦ ((Fintype.equivFin S).symm i : LieSubmodule K L M), ?_,
    fun i ↦ (isIrreducible_iff_isAtom _).2 (hSatom ((Fintype.equivFin S).symm i).2)⟩
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rw [LieSubmodule.iSupIndep_toSubmodule]
    exact ((sSupIndep_iff S).1 hindep).comp (Fintype.equivFin S).symm.injective
  · rw [LieSubmodule.iSup_toSubmodule_eq_top, (Fintype.equivFin S).symm.iSup_comp
      (g := fun x : S ↦ (x : LieSubmodule K L M)), ← sSup_eq_iSup']
    exact hSsup

end TauCeti
