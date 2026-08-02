/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
below `P` in the ambient lattice; it is proved once, at the start, out of Mathlib's order
isomorphism `Submodule.mapIic`.

## Main results

* `TauCeti.isIndecomposableModule_coe_iff`: a submodule `P` is indecomposable exactly when it is
  nonzero and admits no splitting `P = N ⊕ Q` into two nonzero submodules of the ambient module.
* `TauCeti.exists_finset_isIndecomposableModule_supIndep_sup_eq`: every submodule of an Artinian
  module is the internal direct sum of a finite set of indecomposable submodules. This is the
  induction, and the statement the recursion is strong enough to carry.
* `TauCeti.exists_isInternal_isIndecomposableModule`: **existence of an indecomposable
  decomposition** for an Artinian module, packaged as `DirectSum.IsInternal`.
* `TauCeti.exists_indecomposable_decomposition`: the same for a module of finite length, the form
  the Krull-Schmidt statement uses, and
  `TauCeti.exists_isInternal_isIndecomposableModule_of_finiteDimensional` for a module that is
  finite-dimensional over a division ring acting through a scalar tower.
* `TauCeti.exists_isCompl_isIndecomposableModule`: a nonzero Artinian module has an indecomposable
  direct summand.

## Implementation notes

The two lattice lemmas read indecomposability off the submodule lattice and need no subtraction,
so they are stated for a semimodule over a semiring, matching the generality of
`IsIndecomposableModule` itself. The decomposition statements are over a ring: assembling the two
halves of the induction is `Finset.SupIndep.union`, which needs `IsModularLattice (Submodule A M)`,
and Mathlib establishes that instance only for `[Ring A] [AddCommGroup M]`, its proof going through
`Submodule.sup_inf_assoc_of_le_of_neg_le`.

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

section Semiring

variable {A : Type u} {M : Type v} [Semiring A] [AddCommMonoid M] [Module A M] {P : Submodule A M}

/-! ### Reading a submodule's decompositions in the ambient lattice -/

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
  · have h' := h (P.mapIic.symm ⟨N, hN⟩) (P.mapIic.symm ⟨Q, hQ⟩) (P.mapIic.isCompl_iff.mpr ?_)
    · simpa [P.mapIic.symm.injective.eq_iff' P.mapIic.symm.map_bot, Subtype.ext_iff] using h'
    · simpa only [OrderIso.apply_symm_apply, Set.Iic.isCompl_iff] using ⟨hd, hs⟩
  · have h' := Set.Iic.isCompl_iff.mp (P.mapIic.isCompl_iff.mp hNQ)
    simp only [Submodule.coe_mapIic_apply] at h'
    refine (h _ _ (Submodule.map_subtype_le _ _) (Submodule.map_subtype_le _ _) h'.1 h'.2).imp
      (fun hX ↦ ?_) (fun hX ↦ ?_) <;>
      exact P.mapIic.injective (Subtype.ext (by simpa using hX))

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

end Semiring

/-! ### Existence of the decomposition -/

section Ring

variable {A : Type u} {M : Type v} [Ring A] [AddCommGroup M] [Module A M]

/-- Every submodule of an Artinian module is the internal direct sum of a finite set of
indecomposable submodules, recorded as a `Finset` of submodules that is `Finset.SupIndep` with
supremum the given submodule.

This is the statement the decomposition induction carries; the decomposition of the module itself
is `TauCeti.exists_isInternal_isIndecomposableModule`. -/
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
  simpa only [Finset.sup_eq_iSup, iSup_subtype, id_eq] using hss

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
    rw [id_eq]

/-- **Existence of an indecomposable decomposition** for a module of finite length: it is the
internal direct sum of a finite set of indecomposable submodules.

This is the existence half of the Krull-Schmidt theorem, in the hypotheses that theorem is usually
stated with; `TauCeti.exists_isInternal_isIndecomposableModule` is the same statement under the
weaker Artinian hypothesis. -/
theorem exists_indecomposable_decomposition (hM : IsFiniteLength A M) :
    ∃ s : Finset (Submodule A M), (∀ N ∈ s, IsIndecomposableModule A N) ∧
      DirectSum.IsInternal fun N : s ↦ (N : Submodule A M) :=
  have : IsArtinian A M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).2
  exists_isInternal_isIndecomposableModule

/-- A module that is finite-dimensional over a division ring acting through a scalar tower — in
particular a finite-dimensional module over a finite-dimensional algebra — is the internal direct
sum of a finite set of indecomposable submodules. -/
theorem exists_isInternal_isIndecomposableModule_of_finiteDimensional (k : Type*) [DivisionRing k]
    [SMul k A] [Module k M] [IsScalarTower k A M] [FiniteDimensional k M] :
    ∃ s : Finset (Submodule A M), (∀ N ∈ s, IsIndecomposableModule A N) ∧
      DirectSum.IsInternal fun N : s ↦ (N : Submodule A M) :=
  have : IsArtinian A M := isArtinian_of_tower k inferInstance
  exists_isInternal_isIndecomposableModule

end Ring

end TauCeti
