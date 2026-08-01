/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Inversions.Exchange
public import TauCeti.LinearAlgebra.RootSystem.SimpleReflections

public section

/-!
# The deletion condition and the identity criterion for inversion sets

If a word in the simple reflections spells a Weyl-group element sending a simple root to a negative
root, then appending that simple reflection to the word can be spelled by a word two letters
shorter. This is the deletion condition, and it is the missing half of the identification of the
inversion set as the obstruction to being the identity: an element with an empty inversion set is
spelled by the empty word, so it is the identity.

The proof of the deletion condition is an induction on the word. Peeling off the leading simple
reflection `sⱼ`, either the shorter word already sends the simple root to a negative root, and the
inductive hypothesis deletes a letter from it, or the shorter word sends it to a positive root that
`sⱼ` makes negative. In the second case that positive root must be the simple root `αⱼ` itself,
because a simple reflection permutes the remaining positive roots, and then conjugation identifies
`sⱼ` with the appended reflection, so both letters cancel.

## Main results

* `TauCeti.exists_wordProd_eq_mul_ofIdx_of_not_isPos` is the deletion condition.
* `TauCeti.eq_one_of_inversions_eq_empty` and `TauCeti.inversions_eq_empty_iff_eq_one` say that the
  inversion set of a Weyl-group element is empty exactly when the element is the identity.
* `TauCeti.eq_one_of_mapsTo_posRoots` restates this as: a Weyl-group element keeping every positive
  root positive is the identity.
* `TauCeti.inversions_nonempty_of_ne_one` and `TauCeti.ncard_inversions_pos_of_ne_one` are the
  contrapositive forms used to detect nontrivial Weyl-group elements.

## References

This file supplies the root-level exchange condition of Layer 1 in
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`, the step through which the Coxeter
presentation of Layer 2 proves that the braid relations are complete. The argument is the one in
J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. III, §10.3.
-/

namespace TauCeti

open Set

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

/-- **The deletion condition.** If the word `l` spells a Weyl-group element sending the simple root
`αₖ` to a negative root, then the word `l` with `sₖ` appended is spelled by a word one letter
shorter than `l`, hence two letters shorter than `l` with `sₖ` appended. -/
theorem exists_wordProd_eq_mul_ofIdx_of_not_isPos {k : ι} (hk : k ∈ b.support)
    (l : List b.support) (h : ¬ b.IsPos (P.weylGroupToPerm (wordProd P b l) k)) :
    ∃ l' : List b.support,
      wordProd P b l' = wordProd P b l * RootPairing.weylGroup.ofIdx P k ∧
        l'.length + 1 = l.length := by
  induction l with
  | nil =>
    exact absurd (by simpa using b.isPos_of_mem_support hk) h
  | cons j l ih =>
    rw [wordProd_cons, RootPairing.weylGroupToPerm_ofIdx_mul_apply] at h
    by_cases hpos : b.IsPos (P.weylGroupToPerm (wordProd P b l) k)
    · -- The shorter word keeps `αₖ` positive, so the image is the simple root `αⱼ` itself.
      refine ⟨l, ?_, by simp⟩
      have hkey : P.weylGroupToPerm (wordProd P b l) k = (j : ι) := by
        by_contra hne
        have hmem : P.weylGroupToPerm (wordProd P b l) k ∈ posRoots P b \ {(j : ι)} :=
          ⟨(mem_posRoots P b _).mpr hpos, by simpa using hne⟩
        exact h ((mem_posRoots P b _).mp
          ((reflectionPerm_mem_posRoots_diff_singleton_iff P b j.2 _).mpr hmem).1)
      rw [wordProd_cons, ← hkey, RootPairing.weylGroup.ofIdx_weylGroupToPerm_eq_conj,
        inv_mul_cancel_right, mul_assoc, RootPairing.weylGroup.ofIdx_mul_self, mul_one]
    · -- The shorter word already makes `αₖ` negative, so a letter is deleted from it.
      obtain ⟨l', hl', hlen⟩ := ih hpos
      refine ⟨j :: l', ?_, by simp only [List.length_cons]; omega⟩
      rw [wordProd_cons, hl', wordProd_cons, mul_assoc]

variable {P b}

/-- **A Weyl-group element with an empty inversion set is the identity.** A shortest word spelling
it must be empty: otherwise its final simple reflection is an inversion of the word it follows, and
the deletion condition produces a shorter word. -/
theorem eq_one_of_inversions_eq_empty {w : P.weylGroup} (h : inversions P b w = ∅) : w = 1 := by
  classical
  have hex : ∃ n : ℕ, ∃ l : List b.support, l.length = n ∧ wordProd P b l = w := by
    obtain ⟨l, hl⟩ := exists_wordProd_eq P b w
    exact ⟨l.length, l, rfl, hl⟩
  obtain ⟨l, hlen, hl⟩ := Nat.find_spec hex
  rcases List.eq_nil_or_concat l with rfl | ⟨l₁, k, rfl⟩
  · simpa using hl.symm
  · exfalso
    -- Split off the final letter: `w = v * sₖ`, where `v` is spelled by the word `l₁`.
    rw [List.concat_eq_append, wordProd_append, wordProd_cons, wordProd_nil, mul_one] at hl
    -- The final simple root is not an inversion of `w`, so it is an inversion of `v`.
    have hkw : k.1 ∉ inversions P b w := by simp [h]
    have hkv : k.1 ∈ inversions P b (wordProd P b l₁) := by
      by_contra hc
      exact hkw (hl ▸ (mem_inversions_mul_ofIdx_iff_not_mem P _ b k.2).mpr hc)
    obtain ⟨l', hl'w, hl'len⟩ :=
      exists_wordProd_eq_mul_ofIdx_of_not_isPos P b k.2 l₁
        ((mem_inversions P b _ _).mp hkv).2
    -- The resulting word spells `w` and is two letters shorter, contradicting minimality.
    refine Nat.find_min hex (m := l'.length) ?_ ⟨l', rfl, hl'w.trans hl⟩
    rw [← hlen, List.concat_eq_append, List.length_append]
    omega

/-- The inversion set of a Weyl-group element is empty exactly when the element is the identity. -/
@[simp]
theorem inversions_eq_empty_iff_eq_one {w : P.weylGroup} : inversions P b w = ∅ ↔ w = 1 :=
  ⟨eq_one_of_inversions_eq_empty, fun h ↦ by rw [h, inversions_one]⟩

/-- **A Weyl-group element keeping every positive root positive is the identity.** -/
theorem eq_one_of_mapsTo_posRoots {w : P.weylGroup}
    (h : MapsTo (P.weylGroupToPerm w) (posRoots P b) (posRoots P b)) : w = 1 :=
  eq_one_of_inversions_eq_empty ((inversions_eq_empty_iff P b w).mpr h)

/-- A Weyl-group element other than the identity sends some positive root to a negative root. -/
theorem inversions_nonempty_of_ne_one {w : P.weylGroup} (hw : w ≠ 1) :
    (inversions P b w).Nonempty :=
  Set.nonempty_iff_ne_empty.mpr fun h ↦ hw (eq_one_of_inversions_eq_empty h)

/-- A Weyl-group element other than the identity has at least one inversion. -/
theorem ncard_inversions_pos_of_ne_one {w : P.weylGroup} (hw : w ≠ 1) :
    0 < (inversions P b w).ncard :=
  (Set.ncard_pos (Set.toFinite _)).mpr (inversions_nonempty_of_ne_one hw)

end TauCeti
