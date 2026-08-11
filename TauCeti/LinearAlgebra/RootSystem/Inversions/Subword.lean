/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Inversions.Length

public section

/-!
# The deletion condition and the subword property

A word in the simple reflections whose length exceeds the number of inversions of the element it
spells is wasteful, and the strong exchange condition says exactly where the waste is: two of its
letters can be deleted without changing the element. Iterating the deletion until no waste is left
extracts from any word a *subword* of least length spelling the same element.

The deletion is located by walking along the word until the first prefix that is already wasteful.
The prefix one letter shorter is not wasteful, so the letter just read is an inversion of the
element that prefix spells, and the strong exchange condition deletes a letter from that prefix.
Deleting the letter just read as well leaves a word two letters shorter spelling the same element.

The subword form is what makes these statements usable downstream. The deleted positions are named,
so the same deletions can be replayed verbatim on the corresponding word over any other family of
generators indexed by `b.support`, in particular over the generators of the presented Coxeter
group. The bare existence of some shorter word inside the Weyl group names no word over those
generators to carry the assertion back through the presentation map; this is the form in which the
deletion condition enters the word property behind Tits' theorem.

## Main results

* `TauCeti.exists_wordProd_eraseIdx_eraseIdx_eq` is the deletion condition: a word longer than the
  inversion count of the element it spells has two letters that can be deleted.
* `TauCeti.exists_sublist_wordProd_eq_and_length_eq_ncard_inversions` is the subword property:
  every word contains a subword of least length spelling the same element.
* `TauCeti.ncard_inversions_wordProd_eq_length_iff` records that a word is of least length exactly
  when no two of its letters can be deleted.

## References

This file continues the "inversion sets and the exchange step" item of Layer 1 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md` towards the Coxeter presentation
`weylCoxeterSystem` of Layer 2, whose completeness half is proved through the exchange condition at
root level. The deletion condition and the subword property are the standard packaging of that
step; see J. E. Humphreys, *Reflection Groups and Coxeter Groups*, CUP (1990), §1.7 and §5.8, and
Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4--6, Ch. IV, §1.5.
-/

namespace TauCeti

open Set

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

/-- **The deletion condition.** If a word has more letters than the element it spells has
inversions, then two of its letters can be deleted without changing the element it spells. -/
theorem exists_wordProd_eraseIdx_eraseIdx_eq (l : List b.support)
    (h : (inversions P b (wordProd P b l)).ncard < l.length) :
    ∃ j k, j < k ∧ k < l.length ∧
      wordProd P b ((l.eraseIdx k).eraseIdx j) = wordProd P b l ∧
      ((l.eraseIdx k).eraseIdx j).length + 2 = l.length := by
  classical
  -- Some prefix is already too long for the element it spells; the whole word is one.
  have hex : ∃ k, k < l.length ∧
      (inversions P b (wordProd P b (l.take (k + 1)))).ncard < k + 1 := by
    refine ⟨l.length - 1, by omega, ?_⟩
    have hsub : l.length - 1 + 1 = l.length := by omega
    rw [hsub, List.take_length]
    exact h
  -- Take the shortest such prefix.
  obtain ⟨k, ⟨hklt, hkinv⟩, hkmin⟩ :
      ∃ k, (k < l.length ∧ (inversions P b (wordProd P b (l.take (k + 1)))).ncard < k + 1) ∧
        ∀ m < k, ¬(m < l.length ∧
          (inversions P b (wordProd P b (l.take (m + 1)))).ncard < m + 1) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun _ hm ↦ Nat.find_min hex hm⟩
  -- One letter earlier the prefix is of least length.
  have hprefix : (inversions P b (wordProd P b (l.take k))).ncard = k := by
    have hle := ncard_inversions_wordProd_le_length P b (l.take k)
    rw [List.length_take] at hle
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp [wordProd_nil]
    · have hnot := hkmin (k - 1) (by omega)
      push Not at hnot
      have hge := hnot (by omega)
      rw [Nat.sub_add_cancel hkpos] at hge
      omega
  -- The letter just read is an inversion of the element the shorter prefix spells.
  have hsucc : l.take (k + 1) = l.take k ++ [l[k]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hklt]
    rfl
  have hword : wordProd P b (l.take (k + 1)) =
      wordProd P b (l.take k) * RootPairing.weylGroup.ofIdx P (l[k] : ι) := by
    rw [hsucc, wordProd_append, wordProd_cons, wordProd_nil, mul_one]
  have hmem : (l[k] : ι) ∈ inversions P b (wordProd P b (l.take k)) := by
    rw [← ncard_inversions_mul_ofIdx_lt_iff P b _ (b.isPos_of_mem_support l[k].2), ← hword,
      hprefix]
    have hstep := ncard_inversions_mul_ofIdx P (wordProd P b (l.take k)) b l[k].2
    rw [← hword, hprefix] at hstep
    omega
  obtain ⟨hmempos, hmemneg⟩ := (mem_inversions P b _ _).mp hmem
  -- The strong exchange condition deletes a letter from the shorter prefix.
  obtain ⟨j, hj, hjeq⟩ :=
    exists_wordProd_eraseIdx_eq_mul_ofIdx P b hmempos (l.take k) hmemneg
  rw [List.length_take] at hj
  have hjk : j < k := by omega
  have hjlt : j < (l.take k).length := by rw [List.length_take]; omega
  have hinner : l.eraseIdx k = l.take k ++ l.drop (k + 1) := List.eraseIdx_eq_take_drop_succ ..
  have hlist : (l.eraseIdx k).eraseIdx j = (l.take k).eraseIdx j ++ l.drop (k + 1) := by
    rw [hinner, List.eraseIdx_append_of_lt_length hjlt]
  refine ⟨j, k, hjk, hklt, ?_, ?_⟩
  · rw [hlist, wordProd_append, hjeq, ← hword, ← wordProd_append, List.take_append_drop]
  · have h₁ := List.length_eraseIdx_add_one hklt
    have h₂ : j < (l.eraseIdx k).length := by omega
    have h₃ := List.length_eraseIdx_add_one h₂
    omega

/-- **The subword property.** Every word in the simple reflections has a sublist that spells the
same Weyl-group element and whose length is the inversion count of that element, hence is of least
length. -/
theorem exists_sublist_wordProd_eq_and_length_eq_ncard_inversions (l : List b.support) :
    ∃ l' : List b.support, l'.Sublist l ∧ wordProd P b l' = wordProd P b l ∧
      l'.length = (inversions P b (wordProd P b l)).ncard := by
  suffices H : ∀ n : ℕ, ∀ l : List b.support, l.length ≤ n →
      ∃ l' : List b.support, l'.Sublist l ∧ wordProd P b l' = wordProd P b l ∧
        l'.length = (inversions P b (wordProd P b l)).ncard from H l.length l le_rfl
  intro n
  induction n with
  | zero =>
    intro l hl
    exact ⟨l, List.Sublist.refl l, rfl, by
      have := ncard_inversions_wordProd_le_length P b l
      omega⟩
  | succ n ih =>
    intro l hl
    rcases eq_or_lt_of_le (ncard_inversions_wordProd_le_length P b l) with heq | hlt
    · exact ⟨l, List.Sublist.refl l, rfl, heq.symm⟩
    · obtain ⟨j, k, -, -, hword, hlen⟩ := exists_wordProd_eraseIdx_eraseIdx_eq P b l hlt
      obtain ⟨l', hsub, hl'word, hl'len⟩ := ih ((l.eraseIdx k).eraseIdx j) (by omega)
      exact ⟨l', hsub.trans ((List.eraseIdx_sublist (l.eraseIdx k) j).trans
        (List.eraseIdx_sublist l k)), hl'word.trans hword, by rw [hl'len, hword]⟩

/-- **A word is of least length exactly when no two of its letters can be deleted.** -/
theorem ncard_inversions_wordProd_eq_length_iff (l : List b.support) :
    (inversions P b (wordProd P b l)).ncard = l.length ↔
      ∀ j k, j < k → k < l.length →
        wordProd P b ((l.eraseIdx k).eraseIdx j) ≠ wordProd P b l := by
  refine ⟨fun heq j k hjk hk hword ↦ ?_, fun h ↦ ?_⟩
  · -- A deletion would spell the same element with two letters fewer than its inversion count.
    have h₁ := List.length_eraseIdx_add_one hk
    have h₂ : j < (l.eraseIdx k).length := by omega
    have h₃ := List.length_eraseIdx_add_one h₂
    have hle := ncard_inversions_wordProd_le_length P b ((l.eraseIdx k).eraseIdx j)
    rw [hword, heq] at hle
    omega
  · by_contra hne
    have hlt : (inversions P b (wordProd P b l)).ncard < l.length :=
      lt_of_le_of_ne (ncard_inversions_wordProd_le_length P b l) hne
    obtain ⟨j, k, hjk, hk, hword, -⟩ := exists_wordProd_eraseIdx_eraseIdx_eq P b l hlt
    exact h j k hjk hk hword

end TauCeti
