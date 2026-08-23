/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Semisimple.Basic

/-!
# Irreducible Lie submodules are the atoms of the submodule lattice

`LieModule.IsIrreducible R L N` is a statement about the lattice `LieSubmodule R L N` of the Lie
submodules of `N` itself, whereas `IsAtom N` is a statement about the position of `N` in the
lattice `LieSubmodule R L M` of the Lie submodules of the ambient module. This file proves that the
two agree, so that a lattice-theoretic decomposition into atoms may be read as a decomposition into
irreducibles. It also records that every nonzero vector of an irreducible module generates the whole
module as a Lie submodule.

Both directions move along the inclusion `N.incl : N →ₗ⁅R,L⁆ M`, whose `map` and `comap` connect
the two lattices: `LieSubmodule.map_incl_lt_iff_lt_top` says that a proper Lie submodule of `N`
maps to a Lie submodule strictly below `N`, while `LieSubmodule.comap_incl_eq_top` and
`LieSubmodule.comap_incl_eq_bot` read the two extremes of a comap back in the ambient module.

## Main results

* `TauCeti.isIrreducible_iff_isAtom`: a Lie submodule is irreducible as a Lie module exactly when
  it is an atom of the lattice of Lie submodules of the ambient module.
* `TauCeti.lieSpan_singleton_eq_top_of_ne_zero`: every nonzero vector of an irreducible Lie module
  generates the whole module.

## References

This supports Layer 0 of `TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, where
`TauCeti/Algebra/Lie/Sl2/Decomposition.lean` decomposes a finite-dimensional `sl₂`-module into
irreducibles by decomposing its lattice of Lie submodules into atoms.
-/

public section

namespace TauCeti

variable {R L M : Type*} [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]

/-- **Every nonzero vector generates an irreducible Lie module.** If `M` is irreducible and
`m : M` is nonzero, then the Lie submodule spanned by `m` is all of `M`. -/
theorem lieSpan_singleton_eq_top_of_ne_zero [LieModule.IsIrreducible R L M]
    {m : M} (hm : m ≠ 0) : LieSubmodule.lieSpan R L {m} = ⊤ := by
  have : Nontrivial (LieSubmodule.lieSpan R L ({m} : Set M)) :=
    (LieSubmodule.nontrivial_iff_ne_bot R L M).mpr fun hbot ↦
      hm ((LieSubmodule.lieSpan_eq_bot_iff R L M).mp hbot m (Set.mem_singleton m))
  exact LieSubmodule.eq_top_of_isIrreducible R L M _

/-- **The irreducible Lie submodules are the atoms.** A Lie submodule `N` of `M` is irreducible as
a Lie module exactly when it is an atom of `LieSubmodule R L M`, that is, when `N ≠ ⊥` and the only
Lie submodule of `M` strictly below `N` is `⊥`. -/
theorem isIrreducible_iff_isAtom (N : LieSubmodule R L M) :
    LieModule.IsIrreducible R L N ↔ IsAtom N := by
  constructor
  · intro hirr
    have hne : Nontrivial N := LieModule.nontrivial_of_isIrreducible R L N
    refine ⟨(LieSubmodule.nontrivial_iff_ne_bot R L M).1 hne, fun W hW ↦ ?_⟩
    have hcomap : W.comap N.incl ≠ ⊤ := fun hcon ↦
      absurd (le_antisymm hW.le (LieSubmodule.comap_incl_eq_top.1 hcon)) hW.ne
    have hbot := (IsSimpleOrder.eq_bot_or_eq_top (W.comap N.incl)).resolve_right hcomap
    rwa [LieSubmodule.comap_incl_eq_bot, inf_eq_right.2 hW.le] at hbot
  · intro hatom
    have : Nontrivial N := (LieSubmodule.nontrivial_iff_ne_bot R L M).2 hatom.1
    refine LieModule.IsIrreducible.mk fun W hW ↦ ?_
    by_contra hne
    have hbot : W.map N.incl = ⊥ :=
      hatom.2 _ (LieSubmodule.map_incl_lt_iff_lt_top.2 (lt_top_iff_ne_top.2 hne))
    refine hW ((LieSubmodule.eq_bot_iff W).2 fun z hz ↦ ?_)
    have hmem : (z : M) ∈ W.map N.incl := ⟨z, hz, rfl⟩
    rw [hbot] at hmem
    exact Subtype.ext (by simpa using hmem)

end TauCeti
