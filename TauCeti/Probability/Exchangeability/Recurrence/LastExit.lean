/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.LastExit
public import TauCeti.Probability.Recurrent

/-!
# Recurrent prefixes adapted to finite successor reindexings

This file supplies the recurrence step that produces the last-exit condition. A family
`π : α → Equiv.Perm ℕ` of row permutations that moves only finitely many positions on rows attained
by a recurrent path eventually has every such position below the last visit to its row.
Consequently every sufficiently long prefix is `LastExitAdmissible π x`: `π` permutes each used
row prefix within itself and fixes its last position.

This is the bridge between finite-support reduction for row exchangeability and finite last-exit
reconstruction in the Layer 8 Markov-exchangeability milestone of
`TauCetiRoadmap/Exchangeability/README.md`.  The remaining step after this bridge is probabilistic:
use Markov exchangeability to compare the reconstructed finite prefixes and then pass to the full
successor-array law.

## Main results

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

/-- **Finitely many moved cells on attained rows are eventually last-exit admissible along a
recurrent path.** Here recurrence is needed only for attained rows on which `π` moves a cell.
Each such row's visit count eventually exceeds every moved position in the finite attained
support. -/
theorem eventually_lastExitAdmissible_of_recurrent {π : α → Equiv.Perm ℕ} {x : ℕ → α}
    (hrec : ∀ a, (∃ k, π a k ≠ k) → (∃ t, x t = a) → {n | x n = a}.Infinite)
    (hπ : {p : α × ℕ | π p.1 p.2 ≠ p.2 ∧ ∃ t, x t = p.1}.Finite) :
    ∀ᶠ m in atTop, LastExitAdmissible π x m := by
  classical
  have hsupported : ∀ p ∈ {p : α × ℕ | π p.1 p.2 ≠ p.2 ∧ ∃ t, x t = p.1},
      ∀ᶠ m in atTop, p.2 + 1 < visitCount x p.1 m := by
    intro p hp
    have hinfinite := hrec p.1 ⟨p.2, hp.1⟩ hp.2
    have hcount : Tendsto (visitCount x p.1) atTop atTop := by
      refine tendsto_atTop_atTop.2 fun b => ?_
      obtain ⟨n, -, hn⟩ := exists_visitCount_of_infinite hinfinite b
      exact ⟨n, fun m hnm => hn ▸ visitCount_monotone x p.1 hnm⟩
    obtain ⟨N, hN⟩ := tendsto_atTop_atTop.1 hcount (p.2 + 2)
    exact eventually_atTop.2 ⟨N, fun m hm => by have := hN m hm; omega⟩
  filter_upwards [hπ.eventually_all.2 hsupported] with m hm
  apply lastExitAdmissible_of_support_lt_visitCount
  intro a ha k hk
  have hvisited : ∃ t, x t = a := by
    by_contra hvisited
    push Not at hvisited
    have hzero := visitCount_eq_zero_of_forall_ne (n := m) fun i _ => hvisited i
    omega
  exact hm (a, k) ⟨hk, hvisited⟩

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → α}

/-- **A finite-support family of successor-row permutations is almost surely eventually
last-exit admissible for a recurrent process.** This is the process-level recurrence bridge used
before finite last-exit reconstruction. -/
theorem Recurrent.ae_eventually_lastExitAdmissible (h : Recurrent μ X)
    (π : α → Equiv.Perm ℕ) (hπ : {p : α × ℕ | π p.1 p.2 ≠ p.2}.Finite) :
    ∀ᵐ ω ∂μ, ∀ᶠ m in atTop, LastExitAdmissible π (fun n => X n ω) m := by
  filter_upwards [h.ae_infinite_setOf_eq] with ω hω
  exact eventually_lastExitAdmissible_of_recurrent
    (fun _ _ ⟨t, ht⟩ => by simpa only [ht] using hω t) <|
      hπ.subset fun _ hp => hp.1

end Probability

end TauCeti

end

end
