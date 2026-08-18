/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Logic.Equiv.Basic

/-!
# Occurrence and transition counts of a finite word

A word `w : Fin N → α` over an arbitrary alphabet `α` has two elementary statistics: the
**occurrence count** `occCount w a`, the number of positions carrying the letter `a`, and — for a
word of length `n + 1` — the **transition count** `transitionCount w a b`, the number of positions
at which the letter `a` is immediately followed by the letter `b`.

The main result is that a word of positive length is determined up to rearrangement by its first
letter together with its transition counts:

`exists_perm_comp_of_transitionCount_eq`.

The mechanism is a conservation law. Summing `transitionCount w a ·` recovers the number of
positions other than the last carrying `a`, and summing `transitionCount w · a` recovers the number
of positions other than the first carrying `a`; comparing the two expressions for `occCount w a`
pins the last letter once the first letter is known, and then pins every occurrence count. Equal
occurrence counts glue the fibrewise bijections into a permutation of the positions.

This is the combinatorial heart of Markov exchangeability (Diaconis–Freedman), where the
transition counts of a path are the sufficient statistic: see
`TauCeti/Probability/Exchangeability/MarkovExchangeable.lean`.

## Main definitions

* `TauCeti.occCount`: the number of positions of a word carrying a given letter.
* `TauCeti.transitionCount`: the number of positions of a word at which a given ordered pair of
  letters occurs consecutively.

## Main results

* `TauCeti.occCount_eq_of_transitionCount_eq`: equal first letters and equal transition counts
  force equal occurrence counts.
* `TauCeti.exists_perm_comp_of_transitionCount_eq`: two such words are rearrangements of each
  other.
* `TauCeti.prod_transitionCount`: a product of transition weights along a word depends on the word
  only through its transition counts.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.
-/

public section

noncomputable section

open Finset

namespace TauCeti

variable {α : Type*}

/-- The number of positions of the word `w` carrying the letter `a`. -/
def occCount {N : ℕ} (w : Fin N → α) (a : α) : ℕ :=
  Nat.card {i : Fin N // w i = a}

/-- The number of positions `i` of the word `w` at which the letter `a` is immediately followed by
the letter `b`. -/
def transitionCount {n : ℕ} (w : Fin (n + 1) → α) (a b : α) : ℕ :=
  Nat.card {i : Fin n // w i.castSucc = a ∧ w i.succ = b}

/-- The occurrence count as the cardinality of a `Finset` of positions. -/
theorem occCount_eq_card_filter [DecidableEq α] {N : ℕ} (w : Fin N → α) (a : α) :
    occCount w a = #{i : Fin N | w i = a} := by
  rw [occCount, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The transition count as the cardinality of a `Finset` of positions. -/
theorem transitionCount_eq_card_filter [DecidableEq α] {n : ℕ} (w : Fin (n + 1) → α) (a b : α) :
    transitionCount w a b = #{i : Fin n | w i.castSucc = a ∧ w i.succ = b} := by
  rw [transitionCount, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The occurrence count as a sum of indicators over the positions. -/
theorem occCount_eq_sum [DecidableEq α] {N : ℕ} (w : Fin N → α) (a : α) :
    occCount w a = ∑ i : Fin N, if w i = a then 1 else 0 := by
  rw [occCount_eq_card_filter, card_filter]

/-- Splitting off the last position: the occurrences of `a` in a word are those in its initial
segment together with a possible occurrence at the last position. -/
theorem occCount_comp_castSucc_add_last [DecidableEq α] {n : ℕ} (w : Fin (n + 1) → α) (a : α) :
    occCount (w ∘ Fin.castSucc) a + (if w (Fin.last n) = a then 1 else 0) = occCount w a := by
  rw [occCount_eq_sum, occCount_eq_sum, Fin.sum_univ_castSucc]
  rfl

/-- Splitting off the first position: the occurrences of `a` in a word are those in its final
segment together with a possible occurrence at the first position. -/
theorem occCount_comp_succ_add_zero [DecidableEq α] {n : ℕ} (w : Fin (n + 1) → α) (a : α) :
    occCount (w ∘ Fin.succ) a + (if w 0 = a then 1 else 0) = occCount w a := by
  rw [occCount_eq_sum, occCount_eq_sum, Fin.sum_univ_succ, Nat.add_comm]
  rfl

/-- Summing the transitions out of `a` counts the positions carrying `a` other than the last one.
The index set `S` only has to exhaust the letters actually used by `w`. -/
theorem sum_transitionCount_right {n : ℕ} (w : Fin (n + 1) → α) {S : Finset α}
    (hS : ∀ i, w i ∈ S) (a : α) :
    ∑ b ∈ S, transitionCount w a b = occCount (w ∘ Fin.castSucc) a := by
  classical
  rw [occCount_eq_card_filter,
    card_eq_sum_card_fiberwise (f := fun i : Fin n => w i.succ) (t := S)
      fun i _ => hS i.succ]
  refine sum_congr rfl fun b _ => ?_
  rw [transitionCount_eq_card_filter, filter_filter]
  rfl

/-- Summing the transitions into `a` counts the positions carrying `a` other than the first one.
The index set `S` only has to exhaust the letters actually used by `w`. -/
theorem sum_transitionCount_left {n : ℕ} (w : Fin (n + 1) → α) {S : Finset α}
    (hS : ∀ i, w i ∈ S) (b : α) :
    ∑ a ∈ S, transitionCount w a b = occCount (w ∘ Fin.succ) b := by
  classical
  rw [occCount_eq_card_filter,
    card_eq_sum_card_fiberwise (f := fun i : Fin n => w i.castSucc) (t := S)
      fun i _ => hS i.castSucc]
  refine sum_congr rfl fun a _ => ?_
  rw [transitionCount_eq_card_filter, filter_filter]
  exact congrArg _ (filter_congr fun i _ => by simp [and_comm])

/-- **The transition counts and the first letter determine the occurrence counts.** -/
theorem occCount_eq_of_transitionCount_eq {n : ℕ} {u v : Fin (n + 1) → α} (h0 : u 0 = v 0)
    (h : ∀ a b, transitionCount u a b = transitionCount v a b) (a : α) :
    occCount u a = occCount v a := by
  classical
  set S : Finset α := image u univ ∪ image v univ
  have hSu : ∀ i, u i ∈ S := fun i => mem_union_left _ (mem_image_of_mem u (mem_univ i))
  have hSv : ∀ i, v i ∈ S := fun i => mem_union_right _ (mem_image_of_mem v (mem_univ i))
  have hout : occCount (u ∘ Fin.castSucc) a = occCount (v ∘ Fin.castSucc) a := by
    rw [← sum_transitionCount_right u hSu a, ← sum_transitionCount_right v hSv a]
    exact sum_congr rfl fun b _ => h a b
  have hin : occCount (u ∘ Fin.succ) a = occCount (v ∘ Fin.succ) a := by
    rw [← sum_transitionCount_left u hSu a, ← sum_transitionCount_left v hSv a]
    exact sum_congr rfl fun c _ => h c a
  have hu_last := occCount_comp_castSucc_add_last u a
  have hu_zero := occCount_comp_succ_add_zero u a
  have hv_last := occCount_comp_castSucc_add_last v a
  have hv_zero := occCount_comp_succ_add_zero v a
  rw [h0] at hu_zero
  omega

/-- Two words with the same occurrence counts are rearrangements of each other. -/
theorem exists_perm_comp_of_occCount_eq {N : ℕ} {u v : Fin N → α}
    (h : ∀ a, occCount u a = occCount v a) :
    ∃ σ : Equiv.Perm (Fin N), v ∘ σ = u := by
  classical
  refine ⟨Equiv.ofFiberEquiv (f := u) (g := v) fun c =>
    Fintype.equivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact h c), ?_⟩
  funext i
  exact Equiv.ofFiberEquiv_map _ i

/-- **Words with the same first letter and the same transition counts are rearrangements of each
other.** This is the elementary fact underlying Markov exchangeability: the transition counts of a
path, together with its starting point, are a sufficient statistic finer than the occurrence
counts, so any symmetry expressed through them is implied by exchangeability. -/
theorem exists_perm_comp_of_transitionCount_eq {n : ℕ} {u v : Fin (n + 1) → α} (h0 : u 0 = v 0)
    (h : ∀ a b, transitionCount u a b = transitionCount v a b) :
    ∃ σ : Equiv.Perm (Fin (n + 1)), v ∘ σ = u :=
  exists_perm_comp_of_occCount_eq (occCount_eq_of_transitionCount_eq h0 h)

/-- **A product of transition weights along a word is a function of its transition counts.** The
index set `S` only has to exhaust the letters actually used by `w`. -/
theorem prod_transitionCount {M : Type*} [CommMonoid M] {n : ℕ} (w : Fin (n + 1) → α)
    {S : Finset α} (hS : ∀ i, w i ∈ S) (p : α → α → M) :
    ∏ i : Fin n, p (w i.castSucc) (w i.succ) =
      ∏ ab ∈ S ×ˢ S, p ab.1 ab.2 ^ transitionCount w ab.1 ab.2 := by
  classical
  rw [← prod_fiberwise_of_maps_to (s := (univ : Finset (Fin n))) (t := S ×ˢ S)
      (g := fun i : Fin n => (w i.castSucc, w i.succ))
      (fun i _ => mem_product.2 ⟨hS _, hS _⟩) fun i => p (w i.castSucc) (w i.succ)]
  refine prod_congr rfl fun ab _ => ?_
  have hval : ∀ i ∈ filter (fun i : Fin n => (w i.castSucc, w i.succ) = ab) univ,
      p (w i.castSucc) (w i.succ) = p ab.1 ab.2 := fun i hi => by
    rw [← (mem_filter.1 hi).2]
  have hset : filter (fun i : Fin n => (w i.castSucc, w i.succ) = ab) univ =
      filter (fun i : Fin n => w i.castSucc = ab.1 ∧ w i.succ = ab.2) univ :=
    filter_congr fun i _ => by simp [Prod.ext_iff]
  rw [prod_congr rfl hval, prod_const, transitionCount_eq_card_filter, hset]

end TauCeti

end

end
