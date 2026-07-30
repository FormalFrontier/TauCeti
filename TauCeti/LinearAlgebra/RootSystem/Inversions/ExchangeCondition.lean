/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Inversions.Exchange
public import TauCeti.LinearAlgebra.RootSystem.SimpleReflections

public section

/-!
# The exchange condition for words in the simple reflections

Fix a base `b` of a finite reduced crystallographic root system. Every Weyl-group element is a
product of simple reflections, so it is the value of a word in `b.support`. This file proves the
*exchange condition* for such words: if the product of a word sends the simple root `αⱼ` to a
negative root, then appending `sⱼ` to the word has the same effect as deleting one of its letters.

The proof is the classical one. Reading the word from the left, either the shorter word already
sends `αⱼ` to a negative root, in which case induction applies, or the leading simple reflection
`sᵢ` is responsible; since `sᵢ` permutes the positive roots other than `αᵢ`, the only root it can
turn negative is `αᵢ`, and then conjugation identifies `sᵢ` with a conjugate of `sⱼ`, which lets the
leading letter be cancelled.

The immediate payoff is that only the identity has an empty inversion set: reading a word for a
non-identity element from the right, either its last letter is already an inversion, or the exchange
condition shortens the word by two letters and the induction continues. Equivalently, the only
Weyl-group element permuting the positive roots among themselves is the identity.

## Main results

* `TauCeti.exists_wordProd_eraseIdx_eq` is the exchange condition.
* `TauCeti.exists_mem_support_not_isPos_of_ne_one` produces, for a non-identity element, a simple
  root sent to a negative root.
* `TauCeti.inversions_eq_empty_iff_eq_one` and `TauCeti.eq_one_iff_mapsTo_posRoots` say that the
  identity is the only element without inversions.

## References

This file supplies the exchange condition that Layer 2 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md` consumes, in the root-level form
described there. The argument follows Humphreys, *Introduction to Lie Algebras and Representation
Theory*, Lemma 10.3C, and Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4--6.
-/

namespace TauCeti

open Set

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)
  [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

/-- **The exchange condition.** If the product of the word `L` sends the simple root `αⱼ` to a
negative root, then appending `sⱼ` to `L` has the same effect as deleting one of the letters of
`L`. -/
theorem exists_wordProd_eraseIdx_eq (L : List b.support) {j : b.support}
    (hj : ¬ b.IsPos (P.weylGroupToPerm (wordProd P b L) (j : ι))) :
    ∃ m < L.length,
      wordProd P b L * RootPairing.weylGroup.ofIdx P (j : ι) = wordProd P b (L.eraseIdx m) := by
  induction L with
  | nil =>
    simp only [wordProd_nil, map_one, Equiv.Perm.coe_one, id_eq] at hj
    exact absurd (b.isPos_of_mem_support j.2) hj
  | cons i L ih =>
    have hsplit : P.weylGroupToPerm (wordProd P b (i :: L)) (j : ι) =
        P.reflectionPerm (i : ι) (P.weylGroupToPerm (wordProd P b L) (j : ι)) := by
      rw [wordProd_cons, map_mul, Equiv.Perm.mul_apply,
        RootPairing.weylGroupToPerm_ofIdx_apply]
    by_cases hpos : b.IsPos (P.weylGroupToPerm (wordProd P b L) (j : ι))
    · -- The leading reflection is the one turning `αⱼ` negative, so it is the reflection in the
      -- image of `αⱼ` and can be cancelled.
      have hki : P.weylGroupToPerm (wordProd P b L) (j : ι) = (i : ι) := by
        by_contra hne
        have hmem : P.reflectionPerm (i : ι) (P.weylGroupToPerm (wordProd P b L) (j : ι)) ∈
            posRoots P b \ {(i : ι)} :=
          (reflectionPerm_mem_posRoots_diff_singleton_iff P b i.2 _).mpr
            ⟨(mem_posRoots P b _).mpr hpos, hne⟩
        rw [hsplit] at hj
        exact hj ((mem_posRoots P b _).mp hmem.1)
      have hconj : RootPairing.weylGroup.ofIdx P (i : ι) =
          wordProd P b L * RootPairing.weylGroup.ofIdx P (j : ι) * (wordProd P b L)⁻¹ := by
        rw [← hki]
        exact RootPairing.ofIdx_weylGroupToPerm P (wordProd P b L) (j : ι)
      have hcomm : RootPairing.weylGroup.ofIdx P (i : ι) * wordProd P b L =
          wordProd P b L * RootPairing.weylGroup.ofIdx P (j : ι) := by
        rw [hconj]
        group
      have hsq : RootPairing.weylGroup.ofIdx P (i : ι) *
          RootPairing.weylGroup.ofIdx P (i : ι) = 1 :=
        mul_eq_one_iff_eq_inv.mpr (RootPairing.ofIdx_inv P (i : ι)).symm
      have hzero : (i :: L).eraseIdx 0 = L := rfl
      refine ⟨0, by simp, ?_⟩
      rw [hzero, wordProd_cons, mul_assoc, ← hcomm, ← mul_assoc, hsq, one_mul]
    · -- The shorter word already sends `αⱼ` to a negative root.
      obtain ⟨m, hm, hmeq⟩ := ih hpos
      refine ⟨m + 1, by simpa using hm, ?_⟩
      rw [wordProd_cons, mul_assoc, hmeq, List.eraseIdx_cons_succ, wordProd_cons]

/-- Auxiliary induction on the length of a word: a word whose product is not the identity has a
simple root sent to a negative root. -/
private theorem exists_mem_support_not_isPos_aux (n : ℕ) :
    ∀ L : List b.support, L.length ≤ n → wordProd P b L ≠ 1 →
      ∃ i ∈ b.support, ¬ b.IsPos (P.weylGroupToPerm (wordProd P b L) i) := by
  induction n with
  | zero =>
    intro L hL hne
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hL)] at hne
    exact absurd (wordProd_nil P b) hne
  | succ n ih =>
    intro L hL hne
    obtain rfl | ⟨L', j, rfl⟩ := List.eq_nil_or_concat L
    · exact absurd (wordProd_nil P b) hne
    simp only [List.concat_eq_append] at hL hne ⊢
    by_cases hpos : b.IsPos (P.weylGroupToPerm (wordProd P b (L' ++ [j])) (j : ι))
    · -- The last letter is not an inversion, so the exchange condition deletes two letters.
      have hshort : ¬ b.IsPos (P.weylGroupToPerm (wordProd P b L') (j : ι)) := by
        letI := P.indexNeg
        rwa [wordProd_concat, RootPairing.weylGroupToPerm_mul_ofIdx_apply,
          ← RootPairing.indexNeg_neg, RootPairing.weylGroupToPerm_neg,
          RootPairing.Base.IsPos.neg_iff_not] at hpos
      obtain ⟨m, hm, hmeq⟩ := exists_wordProd_eraseIdx_eq P b L' hshort
      have heq : wordProd P b (L'.eraseIdx m) = wordProd P b (L' ++ [j]) := by
        rw [wordProd_concat, ← hmeq]
      have hlen : (L'.eraseIdx m).length ≤ n := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hL
        rw [List.length_eraseIdx, if_pos hm]
        omega
      obtain ⟨i, hi, hni⟩ := ih (L'.eraseIdx m) hlen (by rwa [heq])
      exact ⟨i, hi, by rwa [heq] at hni⟩
    · exact ⟨(j : ι), j.2, hpos⟩

/-- Every Weyl-group element other than the identity sends some simple root to a negative root. -/
theorem exists_mem_support_not_isPos_of_ne_one {w : P.weylGroup} (hw : w ≠ 1) :
    ∃ i ∈ b.support, ¬ b.IsPos (P.weylGroupToPerm w i) := by
  obtain ⟨L, rfl⟩ := exists_wordProd_eq P b w
  exact exists_mem_support_not_isPos_aux P b L.length L le_rfl hw

/-- A non-identity Weyl-group element has a simple root among its inversions. -/
theorem exists_mem_support_mem_inversions {w : P.weylGroup} (hw : w ≠ 1) :
    ∃ i ∈ b.support, i ∈ inversions P b w := by
  obtain ⟨i, hi, hni⟩ := exists_mem_support_not_isPos_of_ne_one P b hw
  exact ⟨i, hi, (mem_inversions P b _ i).mpr ⟨b.isPos_of_mem_support hi, hni⟩⟩

/-- **The identity is the only Weyl-group element without inversions.** -/
theorem inversions_eq_empty_iff_eq_one (w : P.weylGroup) :
    inversions P b w = ∅ ↔ w = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ inversions_one P b⟩
  by_contra hw
  obtain ⟨i, -, hi⟩ := exists_mem_support_mem_inversions P b hw
  rw [h] at hi
  exact hi

/-- A non-identity Weyl-group element has a nonempty inversion set. -/
theorem inversions_nonempty_iff_ne_one (w : P.weylGroup) :
    (inversions P b w).Nonempty ↔ w ≠ 1 := by
  rw [Set.nonempty_iff_ne_empty, not_iff_not, inversions_eq_empty_iff_eq_one]

/-- **The identity is the only Weyl-group element permuting the positive roots among
themselves.** -/
theorem eq_one_iff_mapsTo_posRoots (w : P.weylGroup) :
    w = 1 ↔ MapsTo (P.weylGroupToPerm w) (posRoots P b) (posRoots P b) := by
  rw [← inversions_eq_empty_iff_eq_one P b w, inversions_eq_empty_iff]

/-- The inversion count vanishes exactly on the identity. -/
theorem ncard_inversions_eq_zero_iff (w : P.weylGroup) :
    (inversions P b w).ncard = 0 ↔ w = 1 := by
  rw [Set.ncard_eq_zero (Set.toFinite _), inversions_eq_empty_iff_eq_one]

/-- A non-identity Weyl-group element has at least one inversion. -/
theorem ncard_inversions_pos_iff_ne_one (w : P.weylGroup) :
    0 < (inversions P b w).ncard ↔ w ≠ 1 := by
  rw [Nat.pos_iff_ne_zero, ne_eq, ncard_inversions_eq_zero_iff]

/-- The number of inversions of the product of a word is at most the length of that word. -/
theorem ncard_inversions_wordProd_le (L : List b.support) :
    (inversions P b (wordProd P b L)).ncard ≤ L.length := by
  induction L using List.reverseRecOn with
  | nil => simp
  | append_singleton L i ih =>
    have hstep := ncard_inversions_mul_ofIdx P (wordProd P b L) b i.2
    rw [wordProd_concat]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

end TauCeti
