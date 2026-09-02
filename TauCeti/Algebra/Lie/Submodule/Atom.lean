/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Quotient
public import Mathlib.Algebra.Lie.Semisimple.Basic

/-!
# Irreducible Lie submodules are the atoms of the submodule lattice

`LieModule.IsIrreducible R L N` is a statement about the lattice `LieSubmodule R L N` of the Lie
submodules of `N` itself, whereas `IsAtom N` is a statement about the position of `N` in the
lattice `LieSubmodule R L M` of the Lie submodules of the ambient module. This file proves that the
two agree, so that a lattice-theoretic decomposition into atoms may be read as a decomposition into
irreducibles. It also records that every nonzero vector of an irreducible module generates the whole
module as a Lie submodule, and, dually, that the quotient by a Lie submodule is irreducible exactly
when that submodule is a coatom.

Both directions move along the inclusion `N.incl : N →ₗ⁅R,L⁆ M`, whose `map` and `comap` connect
the two lattices: `LieSubmodule.map_incl_lt_iff_lt_top` says that a proper Lie submodule of `N`
maps to a Lie submodule strictly below `N`, while `LieSubmodule.comap_incl_eq_top` and
`LieSubmodule.comap_incl_eq_bot` read the two extremes of a comap back in the ambient module. The
coatom statement runs the same way along the projection `LieSubmodule.Quotient.mk' N` instead.

## Main results

* `TauCeti.isIrreducible_iff_isAtom`: a Lie submodule is irreducible as a Lie module exactly when
  it is an atom of the lattice of Lie submodules of the ambient module.
* `TauCeti.lieSpan_singleton_eq_top_of_ne_zero`: every nonzero vector of an irreducible Lie module
  generates the whole module.
* `TauCeti.lieSpan_singleton_eq_top_of_lieSpan_eq`: the generator of a cyclic Lie submodule
  generates that submodule, read as a Lie module in its own right.
* `TauCeti.eq_top_of_mem_of_lieSpan_singleton_eq_top`: a Lie submodule containing a generator of
  the ambient module is the whole module.
* `TauCeti.isIrreducible_quotient_iff_isCoatom`: the quotient of a Lie module by a Lie submodule is
  irreducible exactly when that submodule is a coatom of the lattice of Lie submodules.

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

/-- **The generator of a cyclic Lie submodule generates it.** If a Lie submodule `N` of `M` is
spanned by a single vector `m`, then that vector, read inside `N`, spans the whole of `N`.
Otherwise the Lie submodule of `N` it spans would map to a Lie submodule strictly below `N`
(`LieSubmodule.map_incl_lt_iff_lt_top`), which nonetheless still contains `m`. -/
theorem lieSpan_singleton_eq_top_of_lieSpan_eq {N : LieSubmodule R L M} {m : M}
    (h : LieSubmodule.lieSpan R L {m} = N) :
    LieSubmodule.lieSpan R L {(⟨m, h ▸ LieSubmodule.subset_lieSpan rfl⟩ : N)} = ⊤ := by
  have hm : m ∈ N := h ▸ LieSubmodule.subset_lieSpan rfl
  by_contra hne
  have hlt : (LieSubmodule.lieSpan R L {(⟨m, hm⟩ : N)}).map N.incl < N :=
    LieSubmodule.map_incl_lt_iff_lt_top.mpr (lt_top_iff_ne_top.mpr hne)
  have hle : LieSubmodule.lieSpan R L {m} ≤ (LieSubmodule.lieSpan R L {(⟨m, hm⟩ : N)}).map N.incl :=
    LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr
      ⟨⟨m, hm⟩, LieSubmodule.subset_lieSpan rfl, rfl⟩)
  rw [h] at hle
  exact absurd (hlt.trans_le hle) (lt_irrefl _)

/-- **A Lie submodule containing a generator of the ambient module is the whole module.** -/
theorem eq_top_of_mem_of_lieSpan_singleton_eq_top {N : LieSubmodule R L M} {m : M}
    (hm : m ∈ N) (hgen : LieSubmodule.lieSpan R L {m} = ⊤) : N = ⊤ := by
  apply top_unique
  rw [← hgen]
  exact LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr hm)

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

variable [LieAlgebra R L] [LieModule R L M]

/-- **The quotient by a Lie submodule is irreducible exactly when that submodule is a coatom.**
A Lie submodule of `M ⧸ N` pulls back along the projection to a Lie submodule of `M` containing
`N`, which a coatom `N` forces to be either `N` itself, when the submodule is `⊥`, or all of `M`,
when it is `⊤`. Conversely, a Lie submodule strictly above `N` has a nonzero, hence full, image in
an irreducible `M ⧸ N`, and it contains `N`, so it is everything.

This is the Lie analogue of `isSimpleModule_iff_isCoatom`, which does not apply: the Lie submodules
of `M ⧸ N` are not the submodules of `M ⧸ N`. -/
theorem isIrreducible_quotient_iff_isCoatom {N : LieSubmodule R L M} :
    LieModule.IsIrreducible R L (M ⧸ N) ↔ IsCoatom N := by
  constructor
  · intro hirr
    have : Nontrivial (M ⧸ N) := LieModule.nontrivial_of_isIrreducible R L _
    obtain ⟨q, hq⟩ := exists_ne (0 : M ⧸ N)
    obtain ⟨x, rfl⟩ := LieSubmodule.Quotient.surjective_mk' N q
    rw [Ne, LieSubmodule.Quotient.mk_eq_zero] at hq
    refine ⟨fun htop ↦ hq (htop ▸ LieSubmodule.mem_top x), fun P hP ↦ ?_⟩
    obtain ⟨y, hyP, hyN⟩ := SetLike.exists_of_lt hP
    have hmap : P.map (LieSubmodule.Quotient.mk' N) = ⊤ := by
      refine (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left fun hbot ↦ hyN ?_
      have hmem : LieSubmodule.Quotient.mk' N y ∈ P.map (LieSubmodule.Quotient.mk' N) :=
        ⟨y, hyP, rfl⟩
      rw [hbot] at hmem
      exact (LieSubmodule.Quotient.mk_eq_zero _).mp (by simpa using hmem)
    refine eq_top_iff.mpr fun z _ ↦ ?_
    obtain ⟨w, hwP, hw⟩ : LieSubmodule.Quotient.mk' N z ∈ P.map (LieSubmodule.Quotient.mk' N) :=
      hmap ▸ LieSubmodule.mem_top _
    have hsub : z - w ∈ N :=
      (LieSubmodule.Quotient.mk_eq_zero _).mp (by rw [map_sub, sub_eq_zero]; exact hw.symm)
    simpa using add_mem (hP.le hsub) hwP
  · intro hN
    obtain ⟨m, hm⟩ : ∃ m : M, m ∉ N := by
      by_contra hcon
      push Not at hcon
      exact hN.1 (eq_top_iff.mpr fun x _ ↦ hcon x)
    have : Nontrivial (M ⧸ N) :=
      ⟨LieSubmodule.Quotient.mk' N m, 0, by rwa [Ne, LieSubmodule.Quotient.mk_eq_zero]⟩
    refine LieModule.IsIrreducible.mk fun P hP ↦ ?_
    have hle : N ≤ P.comap (LieSubmodule.Quotient.mk' N) := fun x hx ↦
      LieSubmodule.mem_comap.mpr (by
        rw [(LieSubmodule.Quotient.mk_eq_zero _).mpr hx]; exact P.zero_mem)
    rcases hle.lt_or_eq with hlt | heq
    · have htop := hN.2 _ hlt
      refine eq_top_iff.mpr fun q _ ↦ ?_
      obtain ⟨x, rfl⟩ := LieSubmodule.Quotient.surjective_mk' N q
      have hx : x ∈ P.comap (LieSubmodule.Quotient.mk' N) := by
        rw [htop]; exact LieSubmodule.mem_top x
      exact LieSubmodule.mem_comap.mp hx
    · refine absurd ((LieSubmodule.eq_bot_iff P).mpr fun q hq ↦ ?_) hP
      obtain ⟨x, rfl⟩ := LieSubmodule.Quotient.surjective_mk' N q
      have hx : x ∈ P.comap (LieSubmodule.Quotient.mk' N) := LieSubmodule.mem_comap.mpr hq
      rw [← heq] at hx
      exact (LieSubmodule.Quotient.mk_eq_zero _).mpr hx

end TauCeti
