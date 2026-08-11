/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange

public section

/-!
# Length equals inversions

The number of positive roots that a Weyl-group element sends to negative roots is exactly the
number of letters in a shortest word in the simple reflections spelling that element. One
inequality is the exchange step: a letter changes the inversion count by exactly one, so a word of
`k` letters cannot spell an element with more than `k` inversions. The other is a descent
induction: an element other than the identity inverts some *simple* root, and removing that simple
reflection from the right lowers the inversion count by one, so a word of exactly as many letters
as there are inversions is built up one letter at a time.

The identification is packaged as an `IsLeast` statement, `TauCeti.isLeast_ncard_inversions`, so
that both halves are available at once. Everything here is stated and proved purely at the root
level, in terms of `TauCeti.inversions` and `TauCeti.wordProd`: no Coxeter presentation is
mentioned, assumed, or needed. Downstream it *is* the root-level form of the Coxeter length of a
Weyl group, because Mathlib defines `CoxeterSystem.length` to be exactly the least length of a
word in the simple reflections; so once the Coxeter presentation lands, the Coxeter-length
spelling of this theorem is a rewrite of it rather than a further theorem.

The subadditivity, inversion-invariance and descent consequences recorded here are the standard
length-function axioms in their inversion-count spelling.

## Main results

* `TauCeti.ncard_inversions_wordProd_le_length`: a word spells an element with at most as many
  inversions as the word has letters.
* `TauCeti.exists_wordProd_eq_and_length_eq_ncard_inversions`: some word spells the element with
  exactly as many letters as it has inversions.
* `TauCeti.isLeast_ncard_inversions`: the inversion count is the least length of a word spelling
  the element.
* `TauCeti.ncard_inversions_wordProd_modEq_length` and
  `TauCeti.length_modEq_length_of_wordProd_eq`: every word spelling a given element has the same
  length parity, namely that of the inversion count.
* `TauCeti.ncard_inversions_inv` and `TauCeti.ncard_inversions_mul_le`: the inversion count is
  invariant under inversion and subadditive.
* `TauCeti.ncard_inversions_mul_ofIdx_lt_of_mem`,
  `TauCeti.ncard_inversions_mul_ofIdx_lt_iff` and
  `TauCeti.lt_ncard_inversions_mul_ofIdx_iff`: right multiplication by the reflection in a
  positive root lowers the inversion count exactly when that root is an inversion. The reflecting
  root need not be simple, because the strong exchange condition does not require it to be.
* `TauCeti.ncard_inversions_ofIdx_mul_lt_iff` and
  `TauCeti.lt_ncard_inversions_ofIdx_mul_iff`: the same criteria for left multiplication, read off
  the inverse element.

## References

This file iterates over a whole word the root-level exchange step of "Inversion sets and the
exchange step" in Layer 1 of `TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`, the item
that asks for exactly that iteration: the step "iterated, is the exchange/deletion condition for
the geometric action and the combinatorial core that Layer 2's generation and presentation
consume". Nothing beyond that Layer 1 material is consumed, and all of it is on `main`
(`TauCeti/LinearAlgebra/RootSystem/Inversions/StrongExchange.lean` and its imports).

What Layer 2's presentation takes from the iteration is that a nonempty word of least length
spells an element other than the identity, equivalently that its inversion set is nonempty: that
is how the roadmap proves the lift from the presented group injective in Tits' theorem, "a
nonempty reduced word has a nonempty inversion set". This file therefore precedes
`weylCoxeterSystem` rather than waiting on it, and the Coxeter-length identity
`(weylCoxeterSystem b).length w = (inversions b w).ncard` is not proved here.

The argument is the one in J. E. Humphreys, *Introduction to Lie Algebras and Representation
Theory*, GTM 9, Ch. III, §10.3, and in Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4--6.
-/

namespace TauCeti

open Set

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

/-- **A word spells an element with at most as many inversions as the word has letters.** Each
letter changes the inversion count by exactly one, so the count cannot outrun the length. -/
theorem ncard_inversions_wordProd_le_length (l : List b.support) :
    (inversions P b (wordProd P b l)).ncard ≤ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l i ih =>
    have hstep := ncard_inversions_mul_ofIdx P (wordProd P b l) b i.2
    rw [wordProd_append, wordProd_cons, wordProd_nil, mul_one]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- **The inversion count of the element spelled by a word has the parity of the word length.**
Each letter changes the count by exactly one. -/
theorem ncard_inversions_wordProd_modEq_length (l : List b.support) :
    (inversions P b (wordProd P b l)).ncard ≡ l.length [MOD 2] := by
  induction l using List.reverseRecOn with
  | nil => simp [Nat.ModEq]
  | append_singleton l i ih =>
    have hstep := ncard_inversions_mul_ofIdx P (wordProd P b l) b i.2
    rw [wordProd_append, wordProd_cons, wordProd_nil, mul_one]
    simp only [Nat.ModEq, List.length_append, List.length_cons, List.length_nil] at ih ⊢
    omega

variable {P b} in
/-- **Two words spelling the same Weyl-group element have the same length parity.** This is the
well-definedness of the sign character of a Weyl group. -/
theorem length_modEq_length_of_wordProd_eq {l l' : List b.support}
    (h : wordProd P b l = wordProd P b l') : l.length ≡ l'.length [MOD 2] := by
  have hl := ncard_inversions_wordProd_modEq_length P b l
  rw [h] at hl
  exact hl.symm.trans (ncard_inversions_wordProd_modEq_length P b l')

/-- The descent induction behind `TauCeti.exists_wordProd_eq_and_length_eq_ncard_inversions`: an
element with `n` inversions is spelled by a word of `n` letters, built up by peeling off a simple
reflection whose simple root is an inversion. -/
private theorem exists_wordProd_eq_of_ncard_inversions_eq :
    ∀ (n : ℕ) (w : P.weylGroup), (inversions P b w).ncard = n →
      ∃ l : List b.support, wordProd P b l = w ∧ l.length = n := by
  intro n
  induction n with
  | zero =>
    intro w hw
    have hempty : inversions P b w = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).mp hw
    exact ⟨[], by rw [wordProd_nil, eq_one_of_inversions_eq_empty hempty], rfl⟩
  | succ n ih =>
    intro w hw
    have hne : w ≠ 1 := fun h ↦ by rw [h, ncard_inversions_one] at hw; omega
    obtain ⟨i, hi, hmem⟩ := exists_mem_support_mem_inversions_of_ne_one P b hne
    have hdrop := ncard_inversions_mul_ofIdx_of_mem P w b hi hmem
    obtain ⟨l, hl, hlen⟩ := ih (w * RootPairing.weylGroup.ofIdx P i) (by omega)
    refine ⟨l ++ [⟨i, hi⟩], ?_, by simp [hlen]⟩
    simp [hl, mul_assoc]

/-- **Some word spells a Weyl-group element with exactly as many letters as it has inversions.** -/
theorem exists_wordProd_eq_and_length_eq_ncard_inversions (w : P.weylGroup) :
    ∃ l : List b.support, wordProd P b l = w ∧ l.length = (inversions P b w).ncard :=
  exists_wordProd_eq_of_ncard_inversions_eq P b _ w rfl

/-- **Length equals inversions.** The number of inversions of a Weyl-group element is the least
number of simple reflections needed to spell it. -/
theorem isLeast_ncard_inversions (w : P.weylGroup) :
    IsLeast {n | ∃ l : List b.support, wordProd P b l = w ∧ l.length = n}
      ((inversions P b w).ncard) := by
  refine ⟨exists_wordProd_eq_and_length_eq_ncard_inversions P b w, ?_⟩
  rintro n ⟨l, rfl, rfl⟩
  exact ncard_inversions_wordProd_le_length P b l

/-- **The inversion count is invariant under inversion**: reversing a word spelling `w` spells
`w⁻¹`, since a simple reflection is its own inverse. -/
@[simp]
theorem ncard_inversions_inv (w : P.weylGroup) :
    (inversions P b w⁻¹).ncard = (inversions P b w).ncard := by
  have key : ∀ v : P.weylGroup, (inversions P b v⁻¹).ncard ≤ (inversions P b v).ncard := by
    intro v
    obtain ⟨l, hl, hlen⟩ := exists_wordProd_eq_and_length_eq_ncard_inversions P b v
    have hrev : wordProd P b l.reverse = v⁻¹ := by rw [wordProd_reverse, hl]
    calc
      (inversions P b v⁻¹).ncard ≤ l.reverse.length := by
        rw [← hrev]; exact ncard_inversions_wordProd_le_length P b l.reverse
      _ = (inversions P b v).ncard := by rw [List.length_reverse, hlen]
  exact le_antisymm (key w) (by simpa using key w⁻¹)

/-- **The inversion count is subadditive**: concatenating shortest words for `v` and `w` spells
`v * w`. -/
theorem ncard_inversions_mul_le (v w : P.weylGroup) :
    (inversions P b (v * w)).ncard ≤ (inversions P b v).ncard + (inversions P b w).ncard := by
  obtain ⟨l, hl, hlen⟩ := exists_wordProd_eq_and_length_eq_ncard_inversions P b v
  obtain ⟨l', hl', hlen'⟩ := exists_wordProd_eq_and_length_eq_ncard_inversions P b w
  have hcat : wordProd P b (l ++ l') = v * w := by rw [wordProd_append, hl, hl']
  calc
    (inversions P b (v * w)).ncard ≤ (l ++ l').length := by
      rw [← hcat]; exact ncard_inversions_wordProd_le_length P b (l ++ l')
    _ = (inversions P b v).ncard + (inversions P b w).ncard := by
      rw [List.length_append, hlen, hlen']

/-- **Right multiplication by the reflection in an inversion shortens.** The reflecting root is an
arbitrary inversion, not necessarily a simple root, so this is the length inequality for a general
reflection of the Weyl group. -/
theorem ncard_inversions_mul_ofIdx_lt_of_mem (w : P.weylGroup) {i : ι}
    (hi : i ∈ inversions P b w) :
    (inversions P b (w * RootPairing.weylGroup.ofIdx P i)).ncard < (inversions P b w).ncard := by
  obtain ⟨hipos, hineg⟩ := (mem_inversions P b w i).mp hi
  obtain ⟨l, hl, hlen⟩ := exists_wordProd_eq_and_length_eq_ncard_inversions P b w
  obtain ⟨j, hj, hj'⟩ :=
    exists_wordProd_eraseIdx_eq_mul_ofIdx P b hipos l (by rw [hl]; exact hineg)
  have hle := ncard_inversions_wordProd_le_length P b (l.eraseIdx j)
  rw [hj', hl] at hle
  have hlen' := List.length_eraseIdx_add_one hj
  omega

/-- **Descent criterion.** Right multiplication by the reflection in a positive root shortens an
element exactly when that root is already an inversion. -/
@[simp]
theorem ncard_inversions_mul_ofIdx_lt_iff (w : P.weylGroup) {i : ι} (hi : b.IsPos i) :
    (inversions P b (w * RootPairing.weylGroup.ofIdx P i)).ncard < (inversions P b w).ncard ↔
      i ∈ inversions P b w := by
  refine ⟨fun h ↦ by_contra fun hc ↦ ?_, ncard_inversions_mul_ofIdx_lt_of_mem P b w⟩
  have hback := ncard_inversions_mul_ofIdx_lt_of_mem P b (w * RootPairing.weylGroup.ofIdx P i)
    ((mem_inversions_mul_ofIdx_iff_not_mem P w b hi).mpr hc)
  rw [mul_assoc, RootPairing.weylGroup.ofIdx_mul_self, mul_one] at hback
  omega

/-- **Ascent criterion.** Right multiplication by the reflection in a positive root lengthens an
element exactly when that root is not yet an inversion. -/
@[simp]
theorem lt_ncard_inversions_mul_ofIdx_iff (w : P.weylGroup) {i : ι} (hi : b.IsPos i) :
    (inversions P b w).ncard < (inversions P b (w * RootPairing.weylGroup.ofIdx P i)).ncard ↔
      i ∉ inversions P b w := by
  refine ⟨fun h hc ↦ ?_, fun h ↦ ?_⟩
  · have hdrop := ncard_inversions_mul_ofIdx_lt_of_mem P b w hc
    omega
  · have hback := ncard_inversions_mul_ofIdx_lt_of_mem P b (w * RootPairing.weylGroup.ofIdx P i)
      ((mem_inversions_mul_ofIdx_iff_not_mem P w b hi).mpr h)
    rwa [mul_assoc, RootPairing.weylGroup.ofIdx_mul_self, mul_one] at hback

/-- Left multiplication by a reflection has the same inversion count as right multiplication by it
on the inverse element; this is what turns the left criteria into the right ones. -/
private theorem ncard_inversions_ofIdx_mul (w : P.weylGroup) (i : ι) :
    (inversions P b (RootPairing.weylGroup.ofIdx P i * w)).ncard =
      (inversions P b (w⁻¹ * RootPairing.weylGroup.ofIdx P i)).ncard := by
  rw [← ncard_inversions_inv P b (w⁻¹ * RootPairing.weylGroup.ofIdx P i), mul_inv_rev,
    RootPairing.weylGroup.ofIdx_inv_eq, inv_inv]

/-- **Left descent criterion.** Left multiplication by the reflection in a positive root shortens
an element exactly when that root is an inversion of the inverse element. -/
@[simp]
theorem ncard_inversions_ofIdx_mul_lt_iff (w : P.weylGroup) {i : ι} (hi : b.IsPos i) :
    (inversions P b (RootPairing.weylGroup.ofIdx P i * w)).ncard < (inversions P b w).ncard ↔
      i ∈ inversions P b w⁻¹ := by
  rw [ncard_inversions_ofIdx_mul, ← ncard_inversions_inv P b w,
    ncard_inversions_mul_ofIdx_lt_iff P b w⁻¹ hi]

/-- **Left ascent criterion.** Left multiplication by the reflection in a positive root lengthens
an element exactly when that root is not yet an inversion of the inverse element. -/
@[simp]
theorem lt_ncard_inversions_ofIdx_mul_iff (w : P.weylGroup) {i : ι} (hi : b.IsPos i) :
    (inversions P b w).ncard < (inversions P b (RootPairing.weylGroup.ofIdx P i * w)).ncard ↔
      i ∉ inversions P b w⁻¹ := by
  rw [ncard_inversions_ofIdx_mul, ← ncard_inversions_inv P b w,
    lt_ncard_inversions_mul_ofIdx_iff P b w⁻¹ hi]

end TauCeti
