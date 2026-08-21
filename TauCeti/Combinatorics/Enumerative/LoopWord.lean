/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Set.Function
public import TauCeti.Combinatorics.Enumerative.TransitionCount

/-!
# Loops at a base point and their excursions

A finite word that starts at a letter `a₀` and returns to it splits at its visits to `a₀` into
**excursions**: the (possibly empty) stretches of letters strictly between consecutive visits.
Conversely a list `bs : List (List α)` of excursions spells out a word

```text
a₀, bs[0], a₀, bs[1], a₀, …, bs[k-1], a₀
```

which this file calls `TauCeti.loopPath a₀ bs`.

The theorem of this file is that the transition counts of a loop are the sum of the transition
counts of its individual excursion loops (`TauCeti.transitionCount_loopPathAt`), so they do not
see the order in which the excursions are traversed
(`TauCeti.transitionCount_loopPathAt_eq_of_perm`). Together with the first-letter equality
`TauCeti.loopPathAt_zero` this is exactly the input of Diaconis and Freedman's Markov
exchangeability, where the first letter and the transition counts of a finite path are its
sufficient statistic: see `TauCeti/Probability/Exchangeability/Excursion.lean`.

The mechanism is a bookkeeping identity for the list `List.consecutivePairs l` of consecutive
pairs of a word. Concatenating two words at a shared letter `y` splits that list as the pairs of
the first word closed off with `y`, followed by the pairs of the second word
(`TauCeti.consecutivePairs_append_cons`); every excursion of a loop is closed off with `a₀`, so
iterating the split writes the pairs of `loopPath a₀ bs` as a `List.flatMap` over `bs`, which a
permutation of `bs` rearranges.

Words are lists here, while `TauCeti.transitionCount` counts transitions of a
`Fin (n + 1)`-indexed word; the bridge is `TauCeti.transitionCount_getD`, which reads a list of
length `n + 1` as such a word through `List.getD`. Both of those list lemmas live in
`TauCeti/Combinatorics/Enumerative/TransitionCount.lean`.

## Main definitions

* `TauCeti.loopPath`: the word spelled out by a base letter and a list of excursions.
* `TauCeti.loopSteps`: its number of transitions.
* `TauCeti.loopPathAt`: `loopPath` read as a function on `ℕ`, padded with the base letter.

## Main results

* `TauCeti.transitionCount_loopPathAt`: the transition counts of a loop are the sum of those of
  its excursion loops.
* `TauCeti.transitionCount_loopPathAt_eq_of_perm`: reordering the excursions leaves them unchanged.
* `TauCeti.exists_loopPath`: every word that starts and ends at `a₀` is a loop path, with
  excursions that avoid `a₀`.
* `TauCeti.loopPath_injOn`: those excursions are unique.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.
-/

public section

namespace TauCeti

variable {α : Type*}

/-! ## Loops and their excursions -/

/-- The word spelled out by a base letter `a₀` and a list of excursions: `a₀`, the first
excursion, `a₀` again, the second excursion, and so on, ending with a final `a₀`. -/
def loopPath (a₀ : α) : List (List α) → List α
  | [] => [a₀]
  | e :: bs => a₀ :: (e ++ loopPath a₀ bs)

@[simp]
theorem loopPath_nil (a₀ : α) : loopPath a₀ [] = [a₀] := by
  simp only [loopPath]

@[simp]
theorem loopPath_cons (a₀ : α) (e : List α) (bs : List (List α)) :
    loopPath a₀ (e :: bs) = a₀ :: (e ++ loopPath a₀ bs) := by
  simp only [loopPath]

/-- The number of transitions of a loop with the given excursions: each excursion contributes its
own length, plus the one step that returns to the base letter. -/
def loopSteps (bs : List (List α)) : ℕ :=
  (bs.map fun e => e.length + 1).sum

@[simp]
theorem loopSteps_nil : loopSteps ([] : List (List α)) = 0 := by
  simp [loopSteps]

@[simp]
theorem loopSteps_cons (e : List α) (bs : List (List α)) :
    loopSteps (e :: bs) = e.length + 1 + loopSteps bs := by
  simp [loopSteps]

@[simp]
theorem length_loopPath (a₀ : α) (bs : List (List α)) :
    (loopPath a₀ bs).length = loopSteps bs + 1 := by
  induction bs with
  | nil => simp
  | cons e bs ih =>
    simp only [loopPath_cons, loopSteps_cons, List.length_cons, List.length_append, ih]
    omega

/-- Reordering the excursions does not change the length of the loop. -/
theorem loopSteps_eq_of_perm {bs bs' : List (List α)} (h : bs.Perm bs') :
    loopSteps bs = loopSteps bs' :=
  (h.map _).sum_eq

/-- A loop, read as a function on `ℕ`: past its last letter it is padded with the base letter. -/
def loopPathAt (a₀ : α) (bs : List (List α)) (i : ℕ) : α :=
  (loopPath a₀ bs).getD i a₀

theorem loopPathAt_def (a₀ : α) (bs : List (List α)) (i : ℕ) :
    loopPathAt a₀ bs i = (loopPath a₀ bs).getD i a₀ := by
  simp only [loopPathAt]

@[simp]
theorem loopPathAt_zero (a₀ : α) (bs : List (List α)) : loopPathAt a₀ bs 0 = a₀ := by
  cases bs <;> simp [loopPathAt_def]

@[simp]
theorem loopPathAt_loopSteps (a₀ : α) (bs : List (List α)) :
    loopPathAt a₀ bs (loopSteps bs) = a₀ := by
  induction bs with
  | nil => simp
  | cons e bs ih =>
    have hstep : e.length + 1 + loopSteps bs = e.length + loopSteps bs + 1 := by omega
    rw [loopPathAt_def, loopPath_cons, loopSteps_cons, hstep, List.getD_cons_succ,
      List.getD_append_right _ _ _ _ (by omega)]
    simpa [loopPathAt_def] using ih

/-- A loop always starts at its base letter. -/
theorem loopPath_eq_cons_tail (a₀ : α) (bs : List (List α)) :
    loopPath a₀ bs = a₀ :: (loopPath a₀ bs).tail := by
  cases bs <;> simp

/-- Implementation helper for `TauCeti.loopPath_injOn`: in a word split at the base letter,
the first block cannot be shorter than a competing one that avoids the base letter, since the
letter after the shorter block is the base letter on one side and not on the other. -/
private theorem not_length_lt_of_loopPath_eq (a₀ : α) {e e' : List α} {bs bs' : List (List α)}
    (havoid' : a₀ ∉ e') (heq : e ++ loopPath a₀ bs = e' ++ loopPath a₀ bs') :
    ¬e.length < e'.length := by
  intro hlt
  have h1 : (e ++ loopPath a₀ bs).getD e.length a₀ = a₀ := by
    rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, loopPath_eq_cons_tail]
    simp
  rw [heq, List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt] at h1
  exact havoid' (h1 ▸ List.getElem_mem hlt)

/-- **The excursions of a loop are determined by the loop.** Two lists of excursions that avoid
the base letter and spell out the same word are equal, so together with
`TauCeti.exists_loopPath` this makes `TauCeti.loopPath` a bijection between such lists and the
words that start and end at the base letter. -/
theorem loopPath_injOn (a₀ : α) :
    Set.InjOn (loopPath a₀) {bs : List (List α) | ∀ e ∈ bs, a₀ ∉ e} := by
  intro bs
  induction bs with
  | nil =>
    intro _ bs' _ heq
    cases bs' with
    | nil => rfl
    | cons e' bs' =>
      have hlen := congrArg List.length heq
      rw [length_loopPath, length_loopPath, loopSteps_nil, loopSteps_cons] at hlen
      omega
  | cons e bs ih =>
    intro havoid bs' havoid' heq
    cases bs' with
    | nil =>
      have hlen := congrArg List.length heq
      rw [length_loopPath, length_loopPath, loopSteps_nil, loopSteps_cons] at hlen
      omega
    | cons e' bs' =>
      rw [loopPath_cons, loopPath_cons, List.cons.injEq] at heq
      obtain ⟨-, heq⟩ := heq
      have hlen : e.length = e'.length :=
        Nat.le_antisymm
          (Nat.not_lt.1 (not_length_lt_of_loopPath_eq a₀ (havoid e (by simp)) heq.symm))
          (Nat.not_lt.1 (not_length_lt_of_loopPath_eq a₀ (havoid' e' (by simp)) heq))
      obtain ⟨rfl, htail⟩ := List.append_inj heq hlen
      exact congrArg (e :: ·)
        (ih (fun f hf => havoid f (by simp [hf])) (fun f hf => havoid' f (by simp [hf])) htail)

/-- The consecutive pairs of a loop, gathered excursion by excursion. -/
theorem consecutivePairs_loopPath (a₀ : α) (bs : List (List α)) :
    (loopPath a₀ bs).consecutivePairs =
      bs.flatMap fun e => (loopPath a₀ [e]).consecutivePairs := by
  induction bs with
  | nil => simp
  | cons e bs ih =>
    have hcons := loopPath_eq_cons_tail a₀ bs
    rw [loopPath_cons, ← List.cons_append, hcons, consecutivePairs_append_cons, ← hcons, ih,
      List.flatMap_cons]
    congr 1

/-- **The transition counts of a loop are the sum of those of its excursions.** Each excursion is
counted as the loop it forms on its own, from the base letter back to it. -/
theorem transitionCount_loopPathAt (a₀ : α) (bs : List (List α)) {n : ℕ}
    (hn : loopSteps bs = n) (a b : α) :
    transitionCount (fun i : Fin (n + 1) => loopPathAt a₀ bs i.val) a b =
      (bs.map fun e =>
        transitionCount (fun i : Fin (e.length + 1 + 1) => loopPathAt a₀ [e] i.val) a b).sum := by
  classical
  subst hn
  simp only [loopPathAt_def]
  rw [transitionCount_getD a₀ a b _ (loopPath a₀ bs) (length_loopPath a₀ bs),
    consecutivePairs_loopPath, List.count_flatMap]
  refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
  rw [transitionCount_getD a₀ a b _ (loopPath a₀ [e]) (by simp)]
  rfl

/-- **Reordering the excursions of a loop leaves its transition counts unchanged.** -/
theorem transitionCount_loopPathAt_eq_of_perm (a₀ : α) {bs bs' : List (List α)} (h : bs.Perm bs')
    {n : ℕ} (hn : loopSteps bs = n) (a b : α) :
    transitionCount (fun i : Fin (n + 1) => loopPathAt a₀ bs i.val) a b =
      transitionCount (fun i : Fin (n + 1) => loopPathAt a₀ bs' i.val) a b := by
  rw [transitionCount_loopPathAt a₀ bs hn a b,
    transitionCount_loopPathAt a₀ bs' ((loopSteps_eq_of_perm h).symm.trans hn) a b]
  exact (h.map _).sum_eq

/-! ## Every loop decomposes into excursions -/

/-- **A word that starts and ends at `a₀` is the loop of its excursions.** The excursions are the
stretches strictly between consecutive visits to `a₀`, so none of them visits `a₀`. -/
theorem exists_loopPath (a₀ : α) :
    ∀ (n : ℕ) (x : ℕ → α), x 0 = a₀ → x n = a₀ →
      ∃ bs : List (List α), loopSteps bs = n ∧ (∀ e ∈ bs, a₀ ∉ e) ∧
        ∀ i ≤ n, loopPathAt a₀ bs i = x i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x h0 hn
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · refine ⟨[], loopSteps_nil, by simp, fun i hi => ?_⟩
      obtain rfl : i = 0 := Nat.le_zero.1 hi
      simp [h0]
    classical
    have hex : ∃ m, 0 < m ∧ m ≤ n ∧ x m = a₀ := ⟨n, hnpos, le_rfl, hn⟩
    set m := Nat.find hex with hm
    obtain ⟨hm0, hmn, hxm⟩ : 0 < m ∧ m ≤ n ∧ x m = a₀ := Nat.find_spec hex
    have hmin : ∀ j, 0 < j → j < m → x j ≠ a₀ := by
      intro j hj0 hjm hxj
      have hle : m ≤ j := Nat.find_le ⟨hj0, by omega, hxj⟩
      omega
    obtain ⟨bs, hlen, havoid, hval⟩ :=
      ih (n - m) (by omega) (fun j => x (m + j)) (by simpa using hxm)
        (by simpa [Nat.add_sub_cancel' hmn] using hn)
    refine ⟨(List.range (m - 1)).map (fun j => x (j + 1)) :: bs, ?_, ?_, ?_⟩
    · simp only [loopSteps_cons, List.length_map, List.length_range, hlen]
      omega
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · intro hmem
        obtain ⟨j, hjmem, hxj⟩ := List.mem_map.1 hmem
        have hj : j < m - 1 := List.mem_range.1 hjmem
        exact hmin (j + 1) (Nat.succ_pos j) (by omega) hxj
      · exact havoid e he
    · rintro (_ | j) hi
      · simpa using h0.symm
      · rw [loopPathAt_def, loopPath_cons, List.getD_cons_succ]
        by_cases hlt : j < m - 1
        · rw [List.getD_append _ _ _ _ (by simpa using hlt),
            List.getD_eq_getElem _ _ (by simpa using hlt)]
          simp
        · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
          have hb := hval (j + 1 - m) (by omega)
          rw [loopPathAt_def] at hb
          have hidx : j - (m - 1) = j + 1 - m := by omega
          have hshift : m + (j + 1 - m) = j + 1 := by omega
          simp only [List.length_map, List.length_range]
          rw [hidx, hb, hshift]

/-- **A word that ends where it starts is the loop of its excursions.** The `Fin`-indexed form of
`TauCeti.exists_loopPath`. -/
theorem exists_loopPathAt {n : ℕ} (w : Fin (n + 1) → α) (hw : w (Fin.last n) = w 0) :
    ∃ bs : List (List α), loopSteps bs = n ∧ (∀ e ∈ bs, w 0 ∉ e) ∧
      ∀ i : Fin (n + 1), loopPathAt (w 0) bs i.val = w i := by
  obtain ⟨bs, hlen, havoid, hval⟩ :=
    exists_loopPath (w 0) n (fun j => if h : j < n + 1 then w ⟨j, h⟩ else w 0) (by simp)
      (by simpa [Fin.last] using hw)
  refine ⟨bs, hlen, havoid, fun i => ?_⟩
  simpa [i.isLt] using hval i.val (by omega)

end TauCeti

end
