/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.SuccessorArray

/-!
# Last-exit admissibility for finite path reconstruction

The successor-array proof of the Diaconis--Freedman theorem reconstructs a finite path after
permuting entries separately within each successor row. The finite reconstruction theorem needs
the chosen row permutations to preserve every part of a row used by the prefix and to fix its last
used entry. This file packages that classical *last-exit condition* and gives its deterministic
support criterion.

## Main definitions and results

* `TauCeti.LastExitAdmissible` packages the two hypotheses of finite last-exit reconstruction;
* `TauCeti.lastExitAdmissible_of_support_lt_visitCount` proves the support criterion.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115--130.
* S. Fortini, L. Ladelli, G. Petris, and E. Regazzini, "On mixtures of distributions of Markov
  chains", *Stochastic Processes and their Applications* 100 (2002), 147--165, Lemma 1(b).
-/

public section

noncomputable section

namespace TauCeti

variable {α : Type*}

/-- A family of successor-row permutations is **last-exit admissible** for the prefix of `x`
before time `m` when it preserves every used row prefix and fixes the final used position in each
nonempty row.

These are exactly the two hypotheses needed by finite last-exit reconstruction: the first keeps
every reindexed successor entry inside the finite prefix, and the second prevents reconstruction
from closing a proper subtrail before all prescribed entries have been consumed. -/
def LastExitAdmissible (π : α → Equiv.Perm ℕ) (x : ℕ → α) (m : ℕ) : Prop :=
  (∀ a k, k < visitCount x a m → π a k < visitCount x a m) ∧
    ∀ a, 0 < visitCount x a m →
      π a (visitCount x a m - 1) = visitCount x a m - 1

/-- The two conditions defining last-exit admissibility. -/
@[simp]
theorem lastExitAdmissible_iff {π : α → Equiv.Perm ℕ} {x : ℕ → α} {m : ℕ} :
    LastExitAdmissible π x m ↔
      (∀ a k, k < visitCount x a m → π a k < visitCount x a m) ∧
        ∀ a, 0 < visitCount x a m →
          π a (visitCount x a m - 1) = visitCount x a m - 1 :=
  Iff.rfl

/-- A last-exit-admissible permutation keeps every used row index inside the used prefix. -/
theorem LastExitAdmissible.maps_lt_visitCount
    {π : α → Equiv.Perm ℕ} {x : ℕ → α} {m : ℕ}
    (h : LastExitAdmissible π x m) {a : α} {k : ℕ} (hk : k < visitCount x a m) :
    π a k < visitCount x a m :=
  h.1 a k hk

/-- A last-exit-admissible permutation fixes the last used index of every nonempty row. -/
theorem LastExitAdmissible.apply_visitCount_sub_one {π : α → Equiv.Perm ℕ}
    {x : ℕ → α} {m : ℕ} (h : LastExitAdmissible π x m) {a : α}
    (ha : 0 < visitCount x a m) :
    π a (visitCount x a m - 1) = visitCount x a m - 1 :=
  h.2 a ha

/-- If every moved position lies strictly below the last used position of its row, then the row
permutations are last-exit admissible. -/
theorem lastExitAdmissible_of_support_lt_visitCount {π : α → Equiv.Perm ℕ}
    {x : ℕ → α} {m : ℕ}
    (h : ∀ a, 0 < visitCount x a m → ∀ k, π a k ≠ k → k + 1 < visitCount x a m) :
    LastExitAdmissible π x m := by
  rw [lastExitAdmissible_iff]
  constructor
  · intro a k hk
    by_cases hfix : π a k = k
    · simpa only [hfix] using hk
    · have himage : π a (π a k) ≠ π a k := by
        intro himage
        exact hfix ((π a).injective himage)
      have hlt := h a (Nat.zero_lt_of_lt hk) (π a k) himage
      omega
  · intro a ha
    by_contra hlast
    have hlt := h a ha (visitCount x a m - 1) hlast
    omega

end TauCeti

end

end
