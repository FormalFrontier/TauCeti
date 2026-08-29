/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: recurrence and visit counts occur in the main statements.
public import TauCeti.Probability.Exchangeability.Recurrence.SuccessorArray

/-!
# Recurrent prefixes adapted to finite successor reindexings

The successor-array proof of the Diaconis--Freedman theorem reconstructs a finite path after
permuting entries separately within each successor row.  The finite reconstruction theorem needs
the chosen row permutations to preserve every part of a row used by the prefix and to fix its last
used entry.  This is the classical *last-exit condition*.

This file supplies the recurrence step that produces that condition.  A family
`π : α → Equiv.Perm ℕ` of row permutations with finite total support moves entries in only
finitely many rows and only at finitely many positions.  Along a recurrent path, every such row is
either never visited or eventually has more visits than every moved position.  Consequently every
sufficiently long prefix is `LastExitAdmissible π x`: `π` permutes each used row prefix within
itself and fixes its last position.

This is the bridge between finite-support reduction for row exchangeability and finite last-exit
reconstruction in the Layer 8 Markov-exchangeability milestone of
`TauCetiRoadmap/Exchangeability/README.md`.  The remaining step after this bridge is probabilistic:
use Markov exchangeability to compare the reconstructed finite prefixes and then pass to the full
successor-array law.

## Main definitions and results

* `TauCeti.LastExitAdmissible` packages the two hypotheses of finite last-exit reconstruction;
* `TauCeti.eventually_lastExitAdmissible_of_recurrent` is the pointwise recurrence theorem;
* `TauCeti.Probability.Recurrent.ae_eventually_lastExitAdmissible` is its process-level form.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115--130.
* S. Fortini, L. Ladelli, G. Petris, and E. Regazzini, "On mixtures of distributions of Markov
  chains", *Stochastic Processes and their Applications* 100 (2002), 147--165, Lemma 1(b).

No material is adapted from `cameronfreer/exchangeability`, which treats exchangeable rather than
Markov-exchangeable sequences.
-/

public section

noncomputable section

open Filter MeasureTheory

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

/-- **Finite-support row reindexings are eventually last-exit admissible along a recurrent
path.** Here recurrence is stated pointwise: every state attained by `x` is attained infinitely
often.  A row occurring in the finite support is either unattained, in which case its visit count
is always zero, or its visit count eventually exceeds every supported position. -/
theorem eventually_lastExitAdmissible_of_recurrent {π : α → Equiv.Perm ℕ} {x : ℕ → α}
    (hrec : ∀ k : ℕ, {n | x n = x k}.Infinite)
    (hπ : {p : α × ℕ | π p.1 p.2 ≠ p.2}.Finite) :
    ∀ᶠ m in atTop, LastExitAdmissible π x m := by
  classical
  have hsupported : ∀ p ∈ {p : α × ℕ | π p.1 p.2 ≠ p.2},
      ∀ᶠ m in atTop,
        visitCount x p.1 m = 0 ∨ p.2 + 1 < visitCount x p.1 m := by
    intro p hp
    by_cases hvisited : ∃ t, x t = p.1
    · obtain ⟨t, ht⟩ := hvisited
      have hinfinite : {n | x n = p.1}.Infinite := by
        simpa only [ht] using hrec t
      have hcount : Tendsto (visitCount x p.1) atTop atTop := by
        refine tendsto_atTop_atTop.2 fun b => ?_
        obtain ⟨n, -, hn⟩ := exists_visitCount_of_infinite hinfinite b
        exact ⟨n, fun m hnm => hn ▸ visitCount_monotone x p.1 hnm⟩
      obtain ⟨N, hN⟩ := tendsto_atTop_atTop.1 hcount (p.2 + 2)
      exact eventually_atTop.2 ⟨N, fun m hm => Or.inr (by have := hN m hm; omega)⟩
    · exact Eventually.of_forall fun m => Or.inl <|
        visitCount_eq_zero_of_forall_ne fun i _ hi => hvisited ⟨i, hi⟩
  filter_upwards [hπ.eventually_all.2 hsupported] with m hm
  apply lastExitAdmissible_of_support_lt_visitCount
  intro a ha k hk
  have hmem : (a, k) ∈ {p : α × ℕ | π p.1 p.2 ≠ p.2} := hk
  rcases hm (a, k) hmem with hzero | hlt
  · exact (ha.ne' hzero).elim
  · exact hlt

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → α}

/-- **A finite-support family of successor-row permutations is almost surely eventually
last-exit admissible for a recurrent process.** This is the process-level recurrence bridge used
before finite last-exit reconstruction. -/
theorem Recurrent.ae_eventually_lastExitAdmissible (h : Recurrent μ X)
    (π : α → Equiv.Perm ℕ) (hπ : {p : α × ℕ | π p.1 p.2 ≠ p.2}.Finite) :
    ∀ᵐ ω ∂μ, ∀ᶠ m in atTop, LastExitAdmissible π (fun n => X n ω) m := by
  filter_upwards [h.ae_infinite_setOf_eq] with ω hω
  exact eventually_lastExitAdmissible_of_recurrent hω hπ

end Probability

end TauCeti

end

end
