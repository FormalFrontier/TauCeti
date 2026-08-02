/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Artinian.Module
public import TauCeti.RingTheory.KrullSchmidt.Indecomposable

/-!
# Existence of a decomposition into indecomposable submodules

The Krull-Schmidt theorem has two halves: every module of finite length is a finite internal direct
sum of indecomposable submodules, and that decomposition is unique up to a matching of the summands.
This file proves the first half. Uniqueness, whose proof is the exchange argument on the local
endomorphism rings supplied by `TauCeti.isLocalRing_end_of_isIndecomposable`, is not proved here.

Existence needs strictly less than finite length: the descending chain condition alone suffices. A
nonzero submodule that is not indecomposable splits as `N ⊕ Q` with both summands nonzero, hence
both *strictly smaller*, and the recursion terminates because an Artinian module has no infinite
strictly decreasing chain of submodules. The proof below is exactly that recursion, run by
well-founded induction on the submodule lattice, so the results are stated for `[IsArtinian A M]`
and the finite-length form is a corollary.

Running the induction over the submodules of a *fixed* `M` — rather than over modules — is what
keeps the argument short: the recursive calls land on submodules of `M` again, so the finite sets
of summands produced by the two halves live in one type and are combined by `Finset.union`, with no
transport along `Submodule.map` anywhere in the induction. The price is one translation lemma,
`TauCeti.isIndecomposableModule_coe_iff`, which reads indecomposability of `↥P` off the interval
below `P` in the ambient lattice; it is proved once, at the start.

## Main results

* `TauCeti.isIndecomposableModule_coe_iff`: a submodule `P` is indecomposable exactly when it is
  nonzero and admits no splitting `P = N ⊕ Q` into two nonzero submodules of the ambient module.
* `TauCeti.IsIndecomposableModule.ne_bot`: an indecomposable submodule is nonzero, so the summands
  produced below are all nonzero.
* `TauCeti.exists_finset_isIndecomposableModule_supIndep_sup_eq`: every submodule of an Artinian
  module is the internal direct sum of a finite set of indecomposable submodules. This is the
  induction, and the statement the recursion is strong enough to carry.
* `TauCeti.exists_isInternal_isIndecomposableModule`: **existence of an indecomposable
  decomposition** for an Artinian module, packaged as `DirectSum.IsInternal`.
* `TauCeti.exists_isInternal_isIndecomposableModule_of_isFiniteLength`: the same for a module of
  finite length, the form the Krull-Schmidt statement uses, and
  `TauCeti.exists_isInternal_isIndecomposableModule_of_finiteDimensional` for a module that is
  finite-dimensional over a field acting through a scalar tower.
* `TauCeti.exists_isCompl_isIndecomposableModule`: a nonzero Artinian module has an indecomposable
  direct summand.

## References

This implements the "existence of a decomposition" bullet of Layer 2 ("the Krull-Schmidt theorem")
of `TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, pinned as
`exists_indecomposable_decomposition` in its `Suggested.lean`.

See I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
Algebras, Vol. 1*, Section I.4.
-/

public section

namespace TauCeti

universe u v

variable {A : Type u} {M : Type v} [Ring A] [AddCommGroup M] [Module A M]

/-! ### Reading a submodule's decompositions in the ambient lattice -/

section Lattice

variable {P N Q : Submodule A M}

/-- A splitting `P = N ⊕ Q` by submodules of the ambient module `M` pulls back to a splitting of
the module `↥P`. -/
theorem isCompl_comap_subtype (hN : N ≤ P) (hQ : Q ≤ P) (hd : Disjoint N Q) (hs : N ⊔ Q = P) :
    IsCompl (N.comap P.subtype) (Q.comap P.subtype) := by
  constructor
  · rw [disjoint_iff, ← Submodule.comap_inf, disjoint_iff.mp hd, Submodule.comap_bot,
      Submodule.ker_subtype]
  · rw [codisjoint_iff]
    have h := Submodule.submoduleOf_sup_of_le hN hQ
    rw [hs, Submodule.submoduleOf_self] at h
    exact h.symm

/-- A codisjoint pair of submodules of `↥P` spans `P` once pushed forward into the ambient module.
Together with `Submodule.disjoint_map` this is the converse of `TauCeti.isCompl_comap_subtype`. -/
theorem sup_map_subtype_eq_of_codisjoint {N' Q' : Submodule A P} (h : Codisjoint N' Q') :
    N'.map P.subtype ⊔ Q'.map P.subtype = P := by
  rw [← Submodule.map_sup, codisjoint_iff.mp h, Submodule.map_subtype_top]

/-- An indecomposable submodule is nonzero. -/
theorem IsIndecomposableModule.ne_bot (h : IsIndecomposableModule A P) : P ≠ ⊥ :=
  Submodule.nontrivial_iff_ne_bot.mp h.nontrivial

/-- **Indecomposability of a submodule, read in the ambient lattice.** The module `↥P` is
indecomposable exactly when `P` is nonzero and every splitting of `P` as an internal direct sum of
two submodules of `M` has a zero summand.

This is the form the decomposition induction consumes: it never has to leave the lattice
`Submodule A M`. -/
theorem isIndecomposableModule_coe_iff (P : Submodule A M) :
    IsIndecomposableModule A P ↔
      P ≠ ⊥ ∧ ∀ N Q : Submodule A M, N ≤ P → Q ≤ P → Disjoint N Q → N ⊔ Q = P →
        N = ⊥ ∨ Q = ⊥ := by
  rw [isIndecomposableModule_iff_nontrivial_and_forall_isCompl,
    Submodule.nontrivial_iff_ne_bot]
  refine and_congr_right fun _ ↦ ⟨fun h N Q hN hQ hd hs ↦ ?_, fun h N' Q' hNQ ↦ ?_⟩
  · have := h _ _ (isCompl_comap_subtype hN hQ hd hs)
    have hmap : ∀ {X : Submodule A M}, X ≤ P → X.comap P.subtype = ⊥ → X = ⊥ := by
      intro X hX hbot
      rw [← Submodule.map_subtype_range_inclusion hX, Submodule.range_inclusion, hbot,
        Submodule.map_bot]
    exact this.imp (hmap hN) (hmap hQ)
  · have hmap : ∀ {X : Submodule A P}, X.map P.subtype = ⊥ → X = ⊥ := fun {X} hX ↦
      Submodule.map_injective_of_injective P.subtype_injective
        (hX.trans (Submodule.map_bot _).symm)
    exact (h _ _ (Submodule.map_subtype_le _ _) (Submodule.map_subtype_le _ _)
      (Submodule.disjoint_map P.subtype_injective hNQ.disjoint)
      (sup_map_subtype_eq_of_codisjoint hNQ.codisjoint)).imp hmap hmap

/-- A nonzero submodule that is not indecomposable splits into two nonzero submodules of the
ambient module, each of them strictly smaller. This is the step of the decomposition induction. -/
theorem exists_lt_lt_of_not_isIndecomposableModule (hP : P ≠ ⊥)
    (h : ¬IsIndecomposableModule A P) :
    ∃ N Q : Submodule A M, N < P ∧ Q < P ∧ Disjoint N Q ∧ N ⊔ Q = P := by
  rw [isIndecomposableModule_coe_iff] at h
  push Not at h
  obtain ⟨N, Q, hN, hQ, hd, hs, hN0, hQ0⟩ := h hP
  refine ⟨N, Q, lt_of_le_of_ne hN fun hNP ↦ hQ0 ?_, lt_of_le_of_ne hQ fun hQP ↦ hN0 ?_, hd, hs⟩
  · exact hd.symm.eq_bot_of_le (hNP ▸ hQ)
  · exact hd.eq_bot_of_le (hQP ▸ hN)

end Lattice

/-! ### Existence of the decomposition -/

/-- Every submodule of an Artinian module is the internal direct sum of a finite set of
indecomposable submodules, recorded as a `Finset` of submodules that is `Finset.SupIndep` with
supremum the given submodule.

The proof is well-founded induction on the submodule lattice: the zero submodule takes the empty
set, an indecomposable one takes a singleton, and a decomposable one is split by
`TauCeti.exists_lt_lt_of_not_isIndecomposableModule` into two strictly smaller pieces whose sets of
summands are unioned. -/
theorem exists_finset_isIndecomposableModule_supIndep_sup_eq [IsArtinian A M]
    (P : Submodule A M) :
    ∃ s : Finset (Submodule A M), (∀ N ∈ s, IsIndecomposableModule A N) ∧
      s.SupIndep id ∧ s.sup id = P := by
  classical
  induction P using WellFoundedLT.induction with
  | ind P ih =>
  rcases eq_or_ne P ⊥ with rfl | hP
  · exact ⟨∅, by simp, Finset.supIndep_empty _, by simp⟩
  by_cases hind : IsIndecomposableModule A P
  · exact ⟨{P}, by simpa using hind, Finset.supIndep_singleton _ _, by simp⟩
  obtain ⟨N, Q, hNP, hQP, hd, hs⟩ := exists_lt_lt_of_not_isIndecomposableModule hP hind
  obtain ⟨sN, hsN, hsNi, hsNs⟩ := ih N hNP
  obtain ⟨sQ, hsQ, hsQi, hsQs⟩ := ih Q hQP
  refine ⟨sN ∪ sQ, fun X hX ↦ ?_, hsNi.union hsQi ?_, ?_⟩
  · rcases Finset.mem_union.mp hX with h | h
    exacts [hsN X h, hsQ X h]
  · rwa [hsNs, hsQs]
  · rw [Finset.sup_union, hsNs, hsQs, hs]

/-- **Existence of an indecomposable decomposition.** An Artinian module is the internal direct sum
of a finite set of indecomposable submodules. -/
theorem exists_isInternal_isIndecomposableModule [IsArtinian A M] :
    ∃ s : Finset (Submodule A M), (∀ N ∈ s, IsIndecomposableModule A N) ∧
      DirectSum.IsInternal fun N : s ↦ (N : Submodule A M) := by
  obtain ⟨s, hs, hsi, hss⟩ :=
    exists_finset_isIndecomposableModule_supIndep_sup_eq (⊤ : Submodule A M)
  refine ⟨s, hs, (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨hsi.independent, ?_⟩⟩
  rw [← hss, Finset.sup_eq_iSup, iSup_subtype]
  rfl

/-- **Existence of an indecomposable decomposition** for a module of finite length: it is the
internal direct sum of a finite set of indecomposable submodules.

This is the existence half of the Krull-Schmidt theorem, in the hypotheses that theorem is usually
stated with. It is a corollary of the Artinian statement
`TauCeti.exists_isInternal_isIndecomposableModule`, since a module of finite length is Artinian. -/
theorem exists_isInternal_isIndecomposableModule_of_isFiniteLength (hM : IsFiniteLength A M) :
    ∃ s : Finset (Submodule A M), (∀ N ∈ s, IsIndecomposableModule A N) ∧
      DirectSum.IsInternal fun N : s ↦ (N : Submodule A M) :=
  have : IsArtinian A M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).2
  exists_isInternal_isIndecomposableModule

/-- A module that is finite-dimensional over a field acting through a scalar tower — in particular
a finite-dimensional module over a finite-dimensional algebra — is the internal direct sum of a
finite set of indecomposable submodules. -/
theorem exists_isInternal_isIndecomposableModule_of_finiteDimensional (k : Type*) [Field k]
    [SMul k A] [Module k M] [IsScalarTower k A M] [FiniteDimensional k M] :
    ∃ s : Finset (Submodule A M), (∀ N ∈ s, IsIndecomposableModule A N) ∧
      DirectSum.IsInternal fun N : s ↦ (N : Submodule A M) :=
  have : IsArtinian A M := isArtinian_of_tower k inferInstance
  exists_isInternal_isIndecomposableModule

/-- A nonzero Artinian module has an indecomposable direct summand: some indecomposable submodule
`N` admits a complement.

This is the decomposition of `⊤` with one summand singled out; it is the shape in which an
induction over the summands of a module usually consumes the decomposition. -/
theorem exists_isCompl_isIndecomposableModule [IsArtinian A M] [Nontrivial M] :
    ∃ N Q : Submodule A M, IsCompl N Q ∧ IsIndecomposableModule A N := by
  classical
  obtain ⟨s, hs, hsi, hss⟩ :=
    exists_finset_isIndecomposableModule_supIndep_sup_eq (⊤ : Submodule A M)
  obtain ⟨N, hN⟩ : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact top_ne_bot (α := Submodule A M) (by simpa using hss.symm)
  refine ⟨N, (s.erase N).sup id, ⟨?_, ?_⟩, hs N hN⟩
  · simpa using Finset.supIndep_iff_disjoint_erase.mp hsi N hN
  · rw [codisjoint_iff, ← hss]
    conv_rhs => rw [← Finset.insert_erase hN, Finset.sup_insert]
    rfl

end TauCeti
